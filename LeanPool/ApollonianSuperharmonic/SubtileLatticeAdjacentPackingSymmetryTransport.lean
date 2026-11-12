/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.TileOdometerSlopeNonempty

public import LeanPool.ApollonianSuperharmonic.P5625T1CentroidSlopeDifferenceCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryScopedPhase
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileOdometerCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileAction

-- [TABLET NODE: SubtileLatticeAdjacentPackingSymmetryTransport]

/-!
# SubtileLatticeAdjacentPackingSymmetryTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SubtileTransportGeometry

private theorem rotation_transport :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (s : Fin 4), ∀ (negative : Bool), ∀ (x : GaussianInt ×
            GaussianInt),
        let I : GaussianInt := ⟨0, 1⟩
          let P := fun (k : Fin 4) (y : GaussianInt × GaussianInt) =>
            (I ^ k.val * (y.1 + I * y.1), (-I) ^ k.val * (y.2 + -I * y.2))
          let s' := if BandPackingSymmetryReversesOrientation g then
            -s - 1 + (if negative then (2 : Fin 4) else 0)
            else s + (if negative then (2 : Fin 4) else 0)
          BandPackingSymmetryAffineVectorAction g (P s x) =
            P s' (if negative then -BandPackingSymmetryAffineVectorAction g x
              else BandPackingSymmetryAffineVectorAction g x) ) := by
  classical
  intro g s negative x
  let I : GaussianInt := ⟨0, 1⟩
  let R := fun y : GaussianInt × GaussianInt => (I * y.1, -I * y.2)
  have Rneg (y : GaussianInt × GaussianInt) : R (-y) = -R y := by
    ext <;> simp [R]
  have facts : ∀ a : BandPackingSymmetry,
      (∀ y z, BandPackingSymmetryAffineVectorAction a (y + z) =
        BandPackingSymmetryAffineVectorAction a y + BandPackingSymmetryAffineVectorAction a z) ∧
      (∀ y, BandPackingSymmetryAffineVectorAction a (-y) =
        -BandPackingSymmetryAffineVectorAction a y) ∧
      (∀ y, BandPackingSymmetryAffineVectorAction a (R y) =
        if BandPackingSymmetryReversesOrientation a then
          -R (BandPackingSymmetryAffineVectorAction a y)
        else R (BandPackingSymmetryAffineVectorAction a y)) := by
    intro a
    induction a with
    | identity => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
    | shift w =>
        rcases w with ⟨wr, wi⟩
        refine ⟨?_, ?_, ?_⟩
        · rintro ⟨⟨vr, vi⟩, ⟨ar, ai⟩⟩ ⟨⟨ur, ui⟩, ⟨br, bi⟩⟩
          ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianReflection] <;> ring
        · rintro ⟨⟨vr, vi⟩, ⟨ar, ai⟩⟩
          ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianReflection] <;> ring
        · rintro ⟨⟨vr, vi⟩, ⟨ar, ai⟩⟩
          ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianReflection,
            BandPackingSymmetryReversesOrientation, R, I]; ring
    | negate =>
        refine ⟨?_, ?_, ?_⟩
        · intro y z
          ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianQuarterTurn] <;> ring
        · intro y
          ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianQuarterTurn]
        · intro y
          ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianQuarterTurn,
            BandPackingSymmetryReversesOrientation, R, I]
    | conjugate =>
        refine ⟨?_, ?_, ?_⟩
        · intro y z
          ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianReflection] <;> ring
        · intro y
          ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianReflection]
        · intro y
          ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianReflection,
            BandPackingSymmetryReversesOrientation, R, I]
    | comp a b iha ihb =>
        refine ⟨?_, ?_, ?_⟩
        · intro y z
          change BandPackingSymmetryAffineVectorAction a
            (BandPackingSymmetryAffineVectorAction b (y + z)) = _
          rw [ihb.1, iha.1]
          rfl
        · intro y
          change BandPackingSymmetryAffineVectorAction a
            (BandPackingSymmetryAffineVectorAction b (-y)) = _
          rw [ihb.2.1, iha.2.1]
          rfl
        · intro y
          change BandPackingSymmetryAffineVectorAction a
            (BandPackingSymmetryAffineVectorAction b (R y)) = _
          rw [ihb.2.2]
          cases ha : BandPackingSymmetryReversesOrientation a <;>
            cases hb : BandPackingSymmetryReversesOrientation b <;>
            simp [ha, hb, iha.2.1, iha.2.2,
              BandPackingSymmetryReversesOrientation, BandPackingSymmetryAffineVectorAction]
  let P := fun (k : Fin 4) (y : GaussianInt × GaussianInt) =>
    (I ^ k.val * (y.1 + I * y.1), (-I) ^ k.val * (y.2 + -I * y.2))
  let B := fun (k : Fin 4) (y : GaussianInt × GaussianInt) =>
    match k.val with
    | 0 => y + R y
    | 1 => R y + -y
    | 2 => -(y + R y)
    | _ => y + -(R y)
  have PB (k : Fin 4) (y : GaussianInt × GaussianInt) : P k y = B k y := by
    fin_cases k <;> ext <;> simp [P, B, R, I, pow_succ] <;> ring
  change BandPackingSymmetryAffineVectorAction g (P s x) = P _ _
  rw [PB, PB]
  fin_cases s <;> cases negative <;>
    cases he : BandPackingSymmetryReversesOrientation g
  all_goals norm_num [B, he, (facts g).1, (facts g).2.1, (facts g).2.2, Rneg,
    Fin.val_neg', Fin.sub_def, Fin.add_def]
  all_goals ext <;> simp [R, I] <;> ring

private theorem support_nonempty :
    (by
      classical
      exact
        ∀ (C : CircleCoordinates), ∀ (U : ProtoTile), ∀ (h : PartialOdometer), ∀ (p : ℝ × ℝ), 0 <
            C.1 → TileOdometer C U h → PartialOdometerSlope h = some p → U.cells.Nonempty ) := by
  intro C U k p _ hO hp
  exact TileOdometerSlopeNonempty.cells C U k p hO hp

private theorem hsr₀ :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (T₀ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (p₀ : ℝ ×
            ℝ), (PartialOdometerSlope h₀ = some p₀) → ((Finset.Nonempty T₀.cells) →
            ((Finset.Nonempty T₀.cells → PartialOdometerSlope
            (BandPackingSymmetryPartialOdometerAction g h₀) = Option.map
            (BandPackingSymmetrySlopeAction g T₀) (PartialOdometerSlope h₀)) →
            (PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g h₀) = some
            (BandPackingSymmetrySlopeAction g T₀ p₀)))) ) := by
  classical
  intro g T₀ h₀ p₀ hp₀ hT₀ne hST₀
  simpa [Option.map] using (hST₀ hT₀ne).trans
    (congrArg (Option.map (BandPackingSymmetrySlopeAction g T₀)) hp₀)

private theorem hsrᵢ :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (Tᵢ : ProtoTile), ∀ (hᵢ : PartialOdometer), ∀ (pᵢ : ℝ ×
            ℝ), (PartialOdometerSlope hᵢ = some pᵢ) → ((Finset.Nonempty Tᵢ.cells) →
            ((Finset.Nonempty Tᵢ.cells → PartialOdometerSlope
            (BandPackingSymmetryPartialOdometerAction g hᵢ) = Option.map
            (BandPackingSymmetrySlopeAction g Tᵢ) (PartialOdometerSlope hᵢ)) →
            (PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g hᵢ) = some
            (BandPackingSymmetrySlopeAction g Tᵢ pᵢ)))) ) := by
  classical
  intro g Tᵢ hᵢ pᵢ hpᵢ hTᵢne hSTᵢ
  simpa [Option.map] using (hSTᵢ hTᵢne).trans
    (congrArg (Option.map (BandPackingSymmetrySlopeAction g Tᵢ)) hpᵢ)

private theorem incoming :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀
            (negative : Bool), (BandPackingSymmetryScopedPhase g q negative) → ((∀ (i : Fin (3 :
            ℕ)),
        let e := if negative = true then (-1 : GaussianInt) else (1 : GaussianInt);
        let incoming := BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))));
        let cyclic := BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q (i + (2 : Fin (3
            : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ), BandVectors.2 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)); BandVectors.2
            (BandPackingSymmetryQuadrupleAction g q ((fun (i : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -i else i) i).succ)
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))) = e * incoming.2 ∧
            BandVectors.2 (BandPackingSymmetryQuadrupleAction g q ((fun (i : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -i else i) i + (2 : Fin (3 :
            ℕ))).succ) (BandPackingSymmetryQuadrupleAction g q ((fun (i : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -i else i) i + (1 : Fin (3 :
            ℕ))).succ) = e * if BandPackingSymmetryReversesOrientation g = true then
            -GaussianQuarterTurn cyclic.2 else cyclic.2) → ((∀ (g : BandPackingSymmetry), ∀ (z :
            GaussianInt × GaussianInt), (BandPackingSymmetryAffineVectorAction g z).1 =
            BandPackingSymmetryVectorAction g z.1) → (
        let q' := BandPackingSymmetryQuadrupleAction g q
        let j : Fin 3 := if BandPackingSymmetryReversesOrientation g then -i else i
        let V := BandVectors.1 (q i.succ) (q 0)
        let A := BandVectors.2 (q i.succ) (q 0)
        let V' := BandVectors.1 (q' j.succ) (q' 0)
        let A' := BandVectors.2 (q' j.succ) (q' 0)
        (V', A') = if negative then -BandPackingSymmetryAffineVectorAction g (V, A) else
            BandPackingSymmetryAffineVectorAction g (V, A)))) ) := by
  classical
  intro g q i negative hphase hvec affine_first q' j V A V' A'
  have hv := (hphase i).1
  have ha := (hvec i).1
  change V' = (if negative then (-1 : GaussianInt) else 1) *
    BandPackingSymmetryVectorAction g V at hv
  change A' = (if negative then (-1 : GaussianInt) else 1) *
    (BandPackingSymmetryAffineVectorAction g (V, A)).2 at ha
  apply Prod.ext
  · cases negative <;> simpa [affine_first] using hv
  · cases negative <;> simpa using ha

private theorem hrot :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin
            4),
        let P := fun (k : Fin 4) (z : GaussianInt × GaussianInt) =>
          ((⟨0, 1⟩ : GaussianInt) ^ k.val * (z.1 + (⟨0, 1⟩ : GaussianInt) * z.1),
            (-⟨0, 1⟩ : GaussianInt) ^ k.val * (z.2 + (-⟨0, 1⟩ : GaussianInt) * z.2))
        ∀ (negative : Bool),
        let s' : Fin 4 := if BandPackingSymmetryReversesOrientation g then
          -s - 1 + (if negative then (2 : Fin 4) else 0)
          else s + (if negative then (2 : Fin 4) else 0)
        (∀ (g : BandPackingSymmetry), ∀ (s : Fin 4), ∀ (negative : Bool), ∀ (x : GaussianInt ×
            GaussianInt),
        let I : GaussianInt := ⟨0, 1⟩
          let P := fun (k : Fin 4) (y : GaussianInt × GaussianInt) =>
            (I ^ k.val * (y.1 + I * y.1), (-I) ^ k.val * (y.2 + -I * y.2))
          let s' := if BandPackingSymmetryReversesOrientation g then
            -s - 1 + (if negative then (2 : Fin 4) else 0)
            else s + (if negative then (2 : Fin 4) else 0)
          BandPackingSymmetryAffineVectorAction g (P s x) =
            P s' (if negative then -BandPackingSymmetryAffineVectorAction g x
              else BandPackingSymmetryAffineVectorAction g x)) → (
        let q' := BandPackingSymmetryQuadrupleAction g q
        let j : Fin 3 := if BandPackingSymmetryReversesOrientation g then -i else i
        let V := BandVectors.1 (q i.succ) (q 0)
        let A := BandVectors.2 (q i.succ) (q 0)
        let V' := BandVectors.1 (q' j.succ) (q' 0)
        let A' := BandVectors.2 (q' j.succ) (q' 0)
        ((V', A') = if negative then -BandPackingSymmetryAffineVectorAction g (V, A) else
            BandPackingSymmetryAffineVectorAction g (V, A)) →
            (BandPackingSymmetryAffineVectorAction g (P s (V, A)) = P s' (V', A'))) ) := by
  classical
  intro g q i s P negative s' rotation_transport q' j V A V' A' incoming
  have hr := rotation_transport g s negative (V, A)
  change BandPackingSymmetryAffineVectorAction g (P s (V, A)) =
    P s' (if negative then -BandPackingSymmetryAffineVectorAction g (V, A)
      else BandPackingSymmetryAffineVectorAction g (V, A)) at hr
  rw [← incoming] at hr
  exact hr

private theorem hc :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (T₀ : ProtoTile), ∀
            (Tᵢ : ProtoTile), (TileCentroid Tᵢ - TileCentroid T₀ = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1 (q
            i.succ) (q (0 : Fin (4 : ℕ))) + BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ)))) → (
        let V := BandVectors.1 (q i.succ) (q 0)
        let A := BandVectors.2 (q i.succ) (q 0)
        (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (q (0 : Fin (4 : ℕ)))
            (q i.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (q i.succ) (q (0 :
            Fin (4 : ℕ)))) → (
        let P := fun (k : Fin 4) (z : GaussianInt × GaussianInt) =>
          ((⟨0, 1⟩ : GaussianInt) ^ k.val * (z.1 + (⟨0, 1⟩ : GaussianInt) * z.1),
            (-⟨0, 1⟩ : GaussianInt) ^ k.val * (z.2 + (-⟨0, 1⟩ : GaussianInt) * z.2))
        TileCentroid Tᵢ - TileCentroid T₀ = (1 / 2 : ℝ) • GaussianRealPoint (P s (V, A)).1)) ) := by
  classical
  intro q i s T₀ Tᵢ hcent V A hflip P
  simpa only [P, Prod.fst, V, hflip.1] using hcent

private theorem hp :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (p₀ : ℝ × ℝ), ∀ (pᵢ :
            ℝ × ℝ), (pᵢ.1 - p₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ^ (↑s : ℕ) * (BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))) +
            BandVectors.2 (q (0 : Fin (4 : ℕ))) (q i.succ)))).1) → ((pᵢ.2 - p₀.2 = ((1 / 2 : ℝ) •
            GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑s : ℕ) * (BandVectors.2
            (q i.succ) (q (0 : Fin (4 : ℕ))) + BandVectors.2 (q (0 : Fin (4 : ℕ))) (q
            i.succ)))).2) → (
        let V := BandVectors.1 (q i.succ) (q 0)
        let A := BandVectors.2 (q i.succ) (q 0)
        (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (q (0 : Fin (4 : ℕ)))
            (q i.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (q i.succ) (q (0 :
            Fin (4 : ℕ)))) → (
        let P := fun (k : Fin 4) (z : GaussianInt × GaussianInt) =>
          ((⟨0, 1⟩ : GaussianInt) ^ k.val * (z.1 + (⟨0, 1⟩ : GaussianInt) * z.1),
            (-⟨0, 1⟩ : GaussianInt) ^ k.val * (z.2 + (-⟨0, 1⟩ : GaussianInt) * z.2))
        pᵢ - p₀ = (1 / 2 : ℝ) • GaussianRealPoint (P s (V, A)).2))) ) := by
  classical
  intro q i s p₀ pᵢ hslopeRe hslopeIm V A hflip P
  apply Prod.ext
  · simpa [P, A, hflip.2] using hslopeRe
  · simpa [P, A, hflip.2] using hslopeIm

end SubtileTransportGeometry

theorem SubtileLatticeAdjacentPackingSymmetryTransport
    (g : BandPackingSymmetry) (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) (i : Fin 3) (s : Fin 4)
    (hparent : 0 < (q i.succ).1)
    (T₀ Tᵢ : ProtoTile) (h₀ hᵢ : PartialOdometer) (p₀ pᵢ : ℝ × ℝ)
    (hO₀ : TileOdometer (q 0) T₀ h₀)
    (hOᵢ : TileOdometer (q i.succ) Tᵢ hᵢ)
    (hp₀ : PartialOdometerSlope h₀ = some p₀)
    (hpᵢ : PartialOdometerSlope hᵢ = some pᵢ)
    (hcent : TileCentroid Tᵢ - TileCentroid T₀ =
      (1 / 2 : ℝ) • GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.1 (q i.succ) (q 0) +
           BandVectors.1 (q 0) (q i.succ))))
    (hslopeRe : pᵢ.1 - p₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint
      ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
        (BandVectors.2 (q i.succ) (q 0) +
         BandVectors.2 (q 0) (q i.succ)))).1)
    (hslopeIm : pᵢ.2 - p₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint
      ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
        (BandVectors.2 (q i.succ) (q 0) +
         BandVectors.2 (q 0) (q i.succ)))).2) :
    let q' := BandPackingSymmetryQuadrupleAction g q
    let sigma : Fin 3 → Fin 3 := fun j =>
      if BandPackingSymmetryReversesOrientation g then -j else j
    ∃ negative : Bool, ∃ r₀ rᵢ : ℝ × ℝ, ∃ s' : Fin 4,
      BandPackingSymmetryScopedPhase g q negative ∧
      s' = (if BandPackingSymmetryReversesOrientation g then
        -s - 1 + (if negative then (2 : Fin 4) else 0)
      else s + (if negative then (2 : Fin 4) else 0)) ∧
      TileOdometer (q' 0) (BandPackingSymmetryTileAction g T₀)
          (BandPackingSymmetryPartialOdometerAction g h₀) ∧
      TileOdometer (q' (sigma i).succ) (BandPackingSymmetryTileAction g Tᵢ)
          (BandPackingSymmetryPartialOdometerAction g hᵢ) ∧
      PartialOdometerSlope
          (BandPackingSymmetryPartialOdometerAction g h₀) = some r₀ ∧
      PartialOdometerSlope
          (BandPackingSymmetryPartialOdometerAction g hᵢ) = some rᵢ ∧
      TileCentroid (BandPackingSymmetryTileAction g Tᵢ) -
          TileCentroid (BandPackingSymmetryTileAction g T₀) =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s'.val *
            (BandVectors.1 (q' (sigma i).succ) (q' 0) +
             BandVectors.1 (q' 0) (q' (sigma i).succ))) ∧
      rᵢ.1 - r₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ s'.val *
          (BandVectors.2 (q' (sigma i).succ) (q' 0) +
           BandVectors.2 (q' 0) (q' (sigma i).succ)))).1 ∧
      rᵢ.2 - r₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ s'.val *
          (BandVectors.2 (q' (sigma i).succ) (q' 0) +
           BandVectors.2 (q' 0) (q' (sigma i).succ)))).2 ∧
      (OdometerCompatibility
          (BandPackingSymmetryPartialOdometerAction g h₀)
          (BandPackingSymmetryPartialOdometerAction g hᵢ) ↔
        OdometerCompatibility h₀ hᵢ) := by
-- BODY
  classical
  dsimp
  have difference_transport := P5625T1CentroidSlopeDifferenceCovariance.2
  -- The same phase changes the two rotated coordinates.
  have rotation_transport := SubtileTransportGeometry.rotation_transport
  obtain ⟨negative, hphase, hvec⟩ :=
    BandPackingSymmetryAffineVectorCovariance g q hq
  have support_nonempty := SubtileTransportGeometry.support_nonempty
  have hT₀ne := support_nonempty (q 0) T₀ h₀ p₀
    (ProperBandCurvatureStructure q hq).1 hO₀ hp₀
  have hTᵢne := support_nonempty (q i.succ) Tᵢ hᵢ pᵢ hparent hOᵢ hpᵢ
  obtain ⟨hOT₀, _, hST₀⟩ :=
    BandPackingSymmetryTileOdometerCovariance g (q 0) T₀ h₀ hO₀
  obtain ⟨hOTᵢ, _, hSTᵢ⟩ :=
    BandPackingSymmetryTileOdometerCovariance g (q i.succ) Tᵢ hᵢ hOᵢ
  have hsr₀ := SubtileTransportGeometry.hsr₀ g T₀ h₀ p₀ hp₀ hT₀ne hST₀
  have hsrᵢ := SubtileTransportGeometry.hsrᵢ g Tᵢ hᵢ pᵢ hpᵢ hTᵢne hSTᵢ
  have affine_first := P5625T1CentroidSlopeDifferenceCovariance.1
  let q' := BandPackingSymmetryQuadrupleAction g q
  let j : Fin 3 := if BandPackingSymmetryReversesOrientation g then -i else i
  let V := BandVectors.1 (q i.succ) (q 0)
  let A := BandVectors.2 (q i.succ) (q 0)
  let V' := BandVectors.1 (q' j.succ) (q' 0)
  let A' := BandVectors.2 (q' j.succ) (q' 0)
  have incoming := SubtileTransportGeometry.incoming g q i negative hphase hvec affine_first
  have hproper := BandPackingSymmetryProperCovariance g q hq
  have hflip := (VectorRecursionLaws q hq.1).2.2.2.2 hq i
  have hflip' := (VectorRecursionLaws q' hproper.1).2.2.2.2 hproper j
  let P := fun (k : Fin 4) (z : GaussianInt × GaussianInt) =>
    ((⟨0, 1⟩ : GaussianInt) ^ k.val * (z.1 + (⟨0, 1⟩ : GaussianInt) * z.1),
      (-⟨0, 1⟩ : GaussianInt) ^ k.val * (z.2 + (-⟨0, 1⟩ : GaussianInt) * z.2))
  let s' : Fin 4 := if BandPackingSymmetryReversesOrientation g then
    -s - 1 + (if negative then (2 : Fin 4) else 0)
    else s + (if negative then (2 : Fin 4) else 0)
  have hrot : BandPackingSymmetryAffineVectorAction g (P s (V, A)) =
      P s' (V', A') := SubtileTransportGeometry.hrot g q i s negative rotation_transport incoming
  have hc := SubtileTransportGeometry.hc q i s T₀ Tᵢ hcent hflip
  have hp := SubtileTransportGeometry.hp q i s p₀ pᵢ hslopeRe hslopeIm hflip
  have ht := difference_transport g T₀ Tᵢ pᵢ p₀
    (P s (V, A)).1 (P s (V, A)).2 (1 / 2 : ℝ) hc hp
  change TileCentroid (BandPackingSymmetryTileAction g Tᵢ) -
      TileCentroid (BandPackingSymmetryTileAction g T₀) =
      (1 / 2 : ℝ) • GaussianRealPoint
        (BandPackingSymmetryAffineVectorAction g (P s (V, A))).1 ∧
    BandPackingSymmetrySlopeAction g Tᵢ pᵢ -
      BandPackingSymmetrySlopeAction g T₀ p₀ =
      (1 / 2 : ℝ) • GaussianRealPoint
        (BandPackingSymmetryAffineVectorAction g (P s (V, A))).2 at ht
  rw [hrot] at ht
  have neg1 : -(1 : Fin 3) = 2 := rfl
  have neg2 : -(2 : Fin 3) = 1 := rfl
  refine ⟨negative, BandPackingSymmetrySlopeAction g T₀ p₀,
    BandPackingSymmetrySlopeAction g Tᵢ pᵢ, s', hphase, rfl,
    ?_, ?_, hsr₀, hsrᵢ, ?_, ?_, ?_, ?_⟩
  · simpa [BandPackingSymmetryQuadrupleAction] using hOT₀
  · cases he : BandPackingSymmetryReversesOrientation g <;> fin_cases i <;>
      simpa [BandPackingSymmetryQuadrupleAction, he, neg1, neg2] using hOTᵢ
  · simpa only [P, Prod.fst, V', q', j, hflip'.1] using ht.1
  · simpa [P, A', q', j, hflip'.2] using congrArg Prod.fst ht.2
  · simpa [P, A', q', j, hflip'.2] using congrArg Prod.snd ht.2
  · exact (BandPackingSymmetryPartialOdometerActionFormulas g h₀ hᵢ).2.2.2.2.2.2.1

end ApollonianSuperharmonic

end
