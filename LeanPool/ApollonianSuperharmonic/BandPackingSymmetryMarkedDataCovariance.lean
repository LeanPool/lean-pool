/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCurvature
public import LeanPool.ApollonianSuperharmonic.LatticeAdjacentPackingSymmetryFacts
public import LeanPool.ApollonianSuperharmonic.TileOdometerSlopeNonempty

public import LeanPool.ApollonianSuperharmonic.P5625T1CentroidSlopeDifferenceCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryInversePhaseCancellation
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileOdometerCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTilingTransport
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import LeanPool.ApollonianSuperharmonic.TileSubodometer

-- [TABLET NODE: BandPackingSymmetryMarkedDataCovariance]

/-!
# BandPackingSymmetryMarkedDataCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace MarkedCovarianceGeometry

private theorem negCellMap :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (j : Fin 4), LatticeVertexIncidentCell (GaussianQuarterTurn x) j =
            GaussianQuarterTurn (LatticeVertexIncidentCell x (j - 1)) - 1 ) := by
  classical
  intro x j
  fin_cases j <;> simp only [LatticeVertexIncidentCell, GaussianQuarterTurn, Int.reduceNeg,
      Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, sub_self,
      Fin.reduceFinMk, Matrix.cons_val, Fin.sub_def, Fin.coe_ofNat_eq_mod, Nat.one_mod,
      Nat.add_one_sub_one, Nat.mod_succ, Nat.reduceAdd, Nat.reduceMod, Zsqrtd.im_sub,
      Zsqrtd.im_one, sub_zero, neg_sub, Zsqrtd.re_sub, Zsqrtd.re_one, Fin.zero_eta, zero_sub] <;>
          ext <;> simp

private theorem negStar :
    (by
      classical
      exact
        (∀ (x : GaussianInt), ∀ (j : Fin 4), LatticeVertexIncidentCell (GaussianQuarterTurn x) j
            = GaussianQuarterTurn (LatticeVertexIncidentCell x (j - 1)) - 1) → (∀ (x :
            GaussianInt), ∀ (T : ProtoTile), ∀ (U : ProtoTile), (∀ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ T.cells ∨ LatticeVertexIncidentCell x j ∈ U.cells) ↔
            (∀ j : Fin 4, LatticeVertexIncidentCell (GaussianQuarterTurn x) j ∈ (TileQuarterTurn
            T).cells ∨ LatticeVertexIncidentCell (GaussianQuarterTurn x) j ∈ (TileQuarterTurn
            U).cells)) ) := by
  classical
  intro negCellMap x T U
  constructor
  · intro h j
    have hj := h (j - 1)
    rw [(TileQuarterTurnFormulas T).1, (TileQuarterTurnFormulas U).1]
    rw [negCellMap]
    simp only [Finset.mem_image]
    rcases hj with ht | hu
    · exact Or.inl ⟨LatticeVertexIncidentCell x (j - 1), ht, rfl⟩
    · exact Or.inr ⟨LatticeVertexIncidentCell x (j - 1), hu, rfl⟩
  · intro h j
    have hj := h (j + 1)
    rw [(TileQuarterTurnFormulas T).1, (TileQuarterTurnFormulas U).1] at hj
    rw [negCellMap] at hj
    simp only [Finset.mem_image] at hj
    have hidx : (j + 1 - 1 : Fin 4) = j := by fin_cases j <;> decide
    rw [hidx] at hj
    have hinj : Function.Injective GaussianQuarterTurn := by
      intro a b hab
      apply Zsqrtd.ext
      · simpa [GaussianQuarterTurn] using congrArg (fun z : GaussianInt => z.im) hab
      · simpa [GaussianQuarterTurn] using congrArg (fun z : GaussianInt => z.re) hab
    rcases hj with ht | hu
    · rcases ht with ⟨a, ha, he⟩
      left
      have he' : GaussianQuarterTurn a =
          GaussianQuarterTurn (LatticeVertexIncidentCell x j) := by
        have hc := congrArg (fun z : GaussianInt => z + 1) he
        simpa using hc
      have ae := hinj he'
      rw [← ae]
      exact ha
    · rcases hu with ⟨a, ha, he⟩
      right
      have he' : GaussianQuarterTurn a =
          GaussianQuarterTurn (LatticeVertexIncidentCell x j) := by
        have hc := congrArg (fun z : GaussianInt => z + 1) he
        simpa using hc
      have ae := hinj he'
      rw [← ae]
      exact ha

private theorem conjugateCellMap :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (j : Fin 4), LatticeVertexIncidentCell (-GaussianReflection x) j =
            -GaussianReflection (LatticeVertexIncidentCell x (1 - j)) - 1 ) := by
  classical
  intro x j
  fin_cases j <;> simp only [LatticeVertexIncidentCell, GaussianReflection, Int.reduceNeg,
      Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, sub_self,
      Fin.reduceFinMk, Matrix.cons_val, Fin.sub_def, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
      Nat.reduceSub, Nat.one_mod, Nat.reduceAdd, Nat.reduceMod, Zsqrtd.re_sub, Zsqrtd.re_one,
      sub_zero, Zsqrtd.im_sub, Zsqrtd.im_one, neg_sub, Fin.zero_eta] <;> ext <;> simp

private theorem conjugateCells :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (BandPackingSymmetryTileAction .conjugate T).cells = T.cells.image
            (fun x => -GaussianReflection x - 1) ) := by
  classical
  intro T
  change (TileQuarterTurn (TileQuarterTurn (TileReflection T))).cells = _
  rw [(TileQuarterTurnFormulas (TileQuarterTurn (TileReflection T))).1,
    (TileQuarterTurnFormulas (TileReflection T)).1,
    (TileReflectionFormulas T).1]
  simp only [Finset.image_image]
  congr 1
  funext x
  ext <;> simp [GaussianQuarterTurn, GaussianReflection]

private theorem conjugateStar :
    (by
      classical
      exact
        (∀ (x : GaussianInt), ∀ (j : Fin 4), LatticeVertexIncidentCell (-GaussianReflection x) j
            = -GaussianReflection (LatticeVertexIncidentCell x (1 - j)) - 1) → ((∀ (T :
            ProtoTile), (BandPackingSymmetryTileAction .conjugate T).cells = T.cells.image (fun x
            => -GaussianReflection x - 1)) → (∀ (x : GaussianInt), ∀ (T : ProtoTile), ∀ (U :
            ProtoTile), (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells ∨
            LatticeVertexIncidentCell x j ∈ U.cells) ↔ (∀ j : Fin 4, LatticeVertexIncidentCell
            (-GaussianReflection x) j ∈ (BandPackingSymmetryTileAction .conjugate T).cells ∨
            LatticeVertexIncidentCell (-GaussianReflection x) j ∈ (BandPackingSymmetryTileAction
            .conjugate U).cells))) ) := by
  classical
  intro conjugateCellMap conjugateCells x T U
  constructor
  · intro h j
    have hj := h (1 - j)
    rw [conjugateCells T, conjugateCells U, conjugateCellMap]
    simp only [Finset.mem_image]
    rcases hj with ht | hu
    · exact Or.inl ⟨LatticeVertexIncidentCell x (1 - j), ht, rfl⟩
    · exact Or.inr ⟨LatticeVertexIncidentCell x (1 - j), hu, rfl⟩
  · intro h j
    have hj := h (1 - j)
    rw [conjugateCells T, conjugateCells U] at hj
    rw [conjugateCellMap] at hj
    simp only [Finset.mem_image] at hj
    have hidx : (1 - (1 - j) : Fin 4) = j := by fin_cases j <;> decide
    rw [hidx] at hj
    have hinj : Function.Injective (fun z : GaussianInt => -GaussianReflection z) := by
      intro a b hab
      apply Zsqrtd.ext
      · simpa [GaussianReflection] using congrArg (fun z : GaussianInt => z.re) hab
      · simpa [GaussianReflection] using congrArg (fun z : GaussianInt => z.im) hab
    rcases hj with ht | hu
    · rcases ht with ⟨a, ha, he⟩
      left
      have he' : -GaussianReflection a =
          -GaussianReflection (LatticeVertexIncidentCell x j) := by
        have hc := congrArg (fun z : GaussianInt => z + 1) he
        simpa using hc
      have ae := hinj he'
      rw [← ae]
      exact ha
    · rcases hu with ⟨a, ha, he⟩
      right
      have he' : -GaussianReflection a =
          -GaussianReflection (LatticeVertexIncidentCell x j) := by
        have hc := congrArg (fun z : GaussianInt => z + 1) he
        simpa using hc
      have ae := hinj he'
      rw [← ae]
      exact ha

private theorem starCov :
    (by
      classical
      exact
        (∀ (x : GaussianInt), ∀ (T : ProtoTile), ∀ (U : ProtoTile), (∀ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ T.cells ∨ LatticeVertexIncidentCell x j ∈ U.cells) ↔
            (∀ j : Fin 4, LatticeVertexIncidentCell (GaussianQuarterTurn x) j ∈ (TileQuarterTurn
            T).cells ∨ LatticeVertexIncidentCell (GaussianQuarterTurn x) j ∈ (TileQuarterTurn
            U).cells)) → ((∀ (x : GaussianInt), ∀ (T : ProtoTile), ∀ (U : ProtoTile), (∀ j : Fin
            4, LatticeVertexIncidentCell x j ∈ T.cells ∨ LatticeVertexIncidentCell x j ∈ U.cells)
            ↔ (∀ j : Fin 4, LatticeVertexIncidentCell (-GaussianReflection x) j ∈
            (BandPackingSymmetryTileAction .conjugate T).cells ∨ LatticeVertexIncidentCell
            (-GaussianReflection x) j ∈ (BandPackingSymmetryTileAction .conjugate U).cells)) → (∀
            (g : BandPackingSymmetry), ∀ (x : GaussianInt), ∀ (T : ProtoTile), ∀ (U : ProtoTile),
            (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells ∨ LatticeVertexIncidentCell x j
            ∈ U.cells) ↔ (∀ j : Fin 4, LatticeVertexIncidentCell (BandPackingSymmetryVectorAction
            g x) j ∈ (BandPackingSymmetryTileAction g T).cells ∨ LatticeVertexIncidentCell
            (BandPackingSymmetryVectorAction g x) j ∈ (BandPackingSymmetryTileAction g
            U).cells))) ) := by
  classical
  intro negStar conjugateStar g
  induction g with
  | identity => intro x T U; simp [BandPackingSymmetryVectorAction,
      BandPackingSymmetryTileAction]
  | shift w => intro x T U; simp [BandPackingSymmetryVectorAction,
      BandPackingSymmetryTileAction]
  | negate => intro x T U; simpa [BandPackingSymmetryVectorAction,
      BandPackingSymmetryTileAction] using negStar x T U
  | conjugate => intro x T U; simpa [BandPackingSymmetryVectorAction,
      BandPackingSymmetryTileAction] using conjugateStar x T U
  | comp a b iha ihb =>
      intro x T U
      change (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells ∨
        LatticeVertexIncidentCell x j ∈ U.cells) ↔
        (∀ j : Fin 4, LatticeVertexIncidentCell
          (BandPackingSymmetryVectorAction a
            (BandPackingSymmetryVectorAction b x)) j ∈
              (BandPackingSymmetryTileAction a (BandPackingSymmetryTileAction b T)).cells ∨
          LatticeVertexIncidentCell
          (BandPackingSymmetryVectorAction a
            (BandPackingSymmetryVectorAction b x)) j ∈
              (BandPackingSymmetryTileAction a (BandPackingSymmetryTileAction b U)).cells)
      exact (ihb x T U).trans (iha _ _ _)

private theorem partialValueCov :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (h : PartialOdometer), ∀ (k : PartialOdometer), ∀ (x :
            GaussianInt), x ∈ h.domain → x ∈ k.domain → h.value x = k.value x →
            (BandPackingSymmetryPartialOdometerAction g h).value (BandPackingSymmetryVectorAction
            g x) = (BandPackingSymmetryPartialOdometerAction g k).value
            (BandPackingSymmetryVectorAction g x) ) := by
  classical
  have forward (g : BandPackingSymmetry) (h : PartialOdometer) (x : GaussianInt)
      (hx : x ∈ h.domain) :
      BandPackingSymmetryVectorAction g x ∈
        (BandPackingSymmetryPartialOdometerAction g h).domain := by
    change BandPackingSymmetryVectorAction g x ∈
      ((BandPackingSymmetryPartialOdometerAction g h).domain : Set GaussianInt)
    rw [(BandPackingSymmetryPartialOdometerActionFormulas g h h).1]
    exact ⟨x, hx, rfl⟩
  intro g
  induction g with
  | identity => intro h k x hx hk he; exact he
  | shift w =>
      intro h k x hx hk he
      simp [BandPackingSymmetryVectorAction, BandPackingSymmetryPartialOdometerAction,
        hx, hk, he]
  | negate =>
      intro h k x hx hk he
      have hx' := forward .negate h x hx
      have hk' := forward .negate k x hk
      have inv (z : GaussianInt) : -GaussianQuarterTurn (GaussianQuarterTurn z) = z := by
        ext <;> simp [GaussianQuarterTurn]
      rw [(BandPackingSymmetryPartialOdometerActionFormulas .negate h k).2.2.2.1 _ hx',
        (BandPackingSymmetryPartialOdometerActionFormulas .negate k h).2.2.2.1 _ hk']
      simp only [BandPackingSymmetryVectorAction, inv]
      exact he
  | conjugate =>
      intro h k x hx hk he
      have hx' := forward .conjugate h x hx
      have hk' := forward .conjugate k x hk
      have inv (z : GaussianInt) :
          -GaussianReflection (-GaussianReflection z) = z := by
        ext <;> simp [GaussianReflection]
      rw [(BandPackingSymmetryPartialOdometerActionFormulas .conjugate h k).2.2.2.2.1 _ hx',
        (BandPackingSymmetryPartialOdometerActionFormulas .conjugate k h).2.2.2.2.1 _ hk']
      simp only [BandPackingSymmetryVectorAction, inv]
      exact he
  | comp a b iha ihb =>
      intro h k x hx hk he
      have hb := ihb h k x hx hk he
      have hxb := forward b h x hx
      have hkb := forward b k x hk
      rw [(BandPackingSymmetryPartialOdometerActionFormulas a h k).2.2.2.2.2.1 a b,
        (BandPackingSymmetryPartialOdometerActionFormulas a k h).2.2.2.2.2.1 a b]
      change (BandPackingSymmetryPartialOdometerAction a
          (BandPackingSymmetryPartialOdometerAction b h)).value
          (BandPackingSymmetryVectorAction a (BandPackingSymmetryVectorAction b x)) =
        (BandPackingSymmetryPartialOdometerAction a
          (BandPackingSymmetryPartialOdometerAction b k)).value
          (BandPackingSymmetryVectorAction a (BandPackingSymmetryVectorAction b x))
      exact iha _ _ _ hxb hkb hb

private theorem affineFacts :
    (by
      classical
      exact
        let affineQuarter : GaussianInt × GaussianInt → GaussianInt × GaussianInt :=
          fun z => (GaussianQuarterTurn z.1, -GaussianQuarterTurn z.2)
        ∀ k : BandPackingSymmetry, (∀ y, ∀ z, BandPackingSymmetryAffineVectorAction k (y + z) =
            BandPackingSymmetryAffineVectorAction k y + BandPackingSymmetryAffineVectorAction k
            z) ∧ (∀ y, BandPackingSymmetryAffineVectorAction k (-y) =
            -BandPackingSymmetryAffineVectorAction k y) ∧ (∀ y,
            BandPackingSymmetryAffineVectorAction k (affineQuarter y) = if
            BandPackingSymmetryReversesOrientation k then -affineQuarter
            (BandPackingSymmetryAffineVectorAction k y) else affineQuarter
            (BandPackingSymmetryAffineVectorAction k y)) ) := by
  classical
  intro affineQuarter k
  induction k with
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
          BandPackingSymmetryReversesOrientation, affineQuarter,
          GaussianQuarterTurn]; ring
  | negate =>
      refine ⟨?_, ?_, ?_⟩
      · intro y z
        ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianQuarterTurn] <;> ring
      · intro y
        ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianQuarterTurn]
      · intro y
        ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianQuarterTurn,
          BandPackingSymmetryReversesOrientation, affineQuarter]
  | conjugate =>
      refine ⟨?_, ?_, ?_⟩
      · intro y z
        ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianReflection] <;> ring
      · intro y
        ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianReflection]
      · intro y
        ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianReflection,
          BandPackingSymmetryReversesOrientation, affineQuarter,
          GaussianQuarterTurn]
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
          (BandPackingSymmetryAffineVectorAction b (affineQuarter y)) = _
        rw [ihb.2.2]
        cases ha : BandPackingSymmetryReversesOrientation a <;>
          cases hb : BandPackingSymmetryReversesOrientation b <;>
          simp [ha, hb, iha.2.1, iha.2.2,
            BandPackingSymmetryReversesOrientation,
            BandPackingSymmetryAffineVectorAction]

private theorem affineFirst :
    (by
      classical
      exact
        ∀ (k : BandPackingSymmetry), ∀ (z : GaussianInt × GaussianInt),
            (BandPackingSymmetryAffineVectorAction k z).1 = BandPackingSymmetryVectorAction k z.1
            ) := by
  classical
  intro k
  induction k with
  | identity => intro z; rfl
  | negate => intro z; rfl
  | conjugate => intro z; rfl
  | shift w => intro z; rfl
  | comp a b iha ihb =>
      intro z
      change (BandPackingSymmetryAffineVectorAction a
        (BandPackingSymmetryAffineVectorAction b z)).1 =
        BandPackingSymmetryVectorAction a
          (BandPackingSymmetryVectorAction b z.1)
      rw [iha, ihb]

private abbrev circleCurvature := ApollonianSuperharmonic.BandPackingSymmetryCurvature.preserved

private abbrev positiveSupport := ApollonianSuperharmonic.TileOdometerSlopeNonempty.cells

private theorem hq0 :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (C : CircleCoordinates), ∀ (q : Fin (4 : ℕ) →
            CircleCoordinates), (q (0 : Fin (4 : ℕ)) = C) → (
        let q' := BandPackingSymmetryQuadrupleAction g q
        q' 0 = BandPackingSymmetryCircleAction g C) ) := by
  classical
  intro g C q hqC q'
  simpa [q', BandPackingSymmetryQuadrupleAction] using
    congrArg (BandPackingSymmetryCircleAction g) hqC

private theorem hqi :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (C' : CircleCoordinates), ∀ (T : ProtoTile), ∀ (T' :
            ProtoTile), ∀ (h : PartialOdometer), ∀ (h' : PartialOdometer), ∀ (q : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (i : Fin (3 : ℕ)), (q i.succ = C') → (∀ (e : Bool),
            (TileCentroid T' - TileCentroid T = (if e = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2
            : ℝ) • (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1
            : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (q
            (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).1))) → ((C'.1 = (0 :
            ℤ) ∨ ∃ (p : ℝ × ℝ) (p' : ℝ × ℝ), PartialOdometerSlope h = some p ∧
            PartialOdometerSlope h' = some p' ∧ p'.1 - p.1 = (if e = true then (1 : ℝ) else (-1 :
            ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 :
            Fin (3 : ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q
            (i + (1 : Fin (3 : ℕ))).succ)).im : ℝ)) ∧ p'.2 - p.2 = (if e = true then (1 : ℝ) else
            (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i +
            (1 : Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
            (q (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → (
        let q' := BandPackingSymmetryQuadrupleAction g q
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        q' (sigma i).succ = BandPackingSymmetryCircleAction g C'))) ) := by
  classical
  intro g C' T T' h h' q i hqC' e hcent hslope q' sigma
  have hidx : q' (sigma i).succ =
      BandPackingSymmetryCircleAction g (q i.succ) := by
    cases hor : BandPackingSymmetryReversesOrientation g <;> fin_cases i <;>
      simp [q', sigma, BandPackingSymmetryQuadrupleAction, hor]
    all_goals rfl
  rw [hidx]
  exact congrArg (BandPackingSymmetryCircleAction g) hqC'

private theorem hcentM :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i :
            Fin (3 : ℕ)), ∀ (e : Bool), (TileCentroid T' - TileCentroid T = (if e = true then (1
            : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (i + (2 :
            Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint
            (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).2,
            (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin
            (3 : ℕ))).succ))).1))) → (
        let W := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
        let A := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
        let M : GaussianInt × GaussianInt :=
          (W - GaussianQuarterTurn W, A + GaussianQuarterTurn A)
        let eReal : ℝ := if e then 1 else -1
        let k : ℝ := eReal / 2
        TileCentroid T' - TileCentroid T = k • GaussianRealPoint M.1) ) := by
  classical
  intro T T' q i e hcent W A M eReal k
  have hpoint : GaussianRealPoint M.1 =
      GaussianRealPoint W - (-(GaussianRealPoint W).2,
        (GaussianRealPoint W).1) := by
    ext <;> simp [M, GaussianRealPoint, GaussianQuarterTurn]
  rw [show k = eReal * (1 / 2) by dsimp [k]; ring]
  rw [hpoint]
  simpa [eReal, smul_smul, smul_eq_mul] using hcent

private theorem hWphase :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 :
            ℕ)), ∀ (delta : Bool), (BandPackingSymmetryScopedPhase g q delta) → (
        let q' := BandPackingSymmetryQuadrupleAction g q
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        let W := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
        let W' := BandVectors.1 (q' ((sigma i + 2).succ))
          (q' ((sigma i + 1).succ))
        W' = (if delta then (-1 : GaussianInt) else 1) * (if
            BandPackingSymmetryReversesOrientation g then GaussianQuarterTurn
            (BandPackingSymmetryVectorAction g W) else BandPackingSymmetryVectorAction g W)) ) := by
  classical
  intro g q i delta hphase q' sigma W W'
  simpa [W', W, q', sigma, BandPackingSymmetryReversesOrientation] using
    (hphase i).2.2

private theorem hactM :
    (by
      classical
      exact
        let affineQuarter : GaussianInt × GaussianInt → GaussianInt × GaussianInt :=
          fun z => (GaussianQuarterTurn z.1, -GaussianQuarterTurn z.2)
        (∀ k : BandPackingSymmetry, (∀ y, ∀ z, BandPackingSymmetryAffineVectorAction k (y + z) =
            BandPackingSymmetryAffineVectorAction k y + BandPackingSymmetryAffineVectorAction k
            z) ∧ (∀ y, BandPackingSymmetryAffineVectorAction k (-y) =
            -BandPackingSymmetryAffineVectorAction k y) ∧ (∀ y,
            BandPackingSymmetryAffineVectorAction k (affineQuarter y) = if
            BandPackingSymmetryReversesOrientation k then -affineQuarter
            (BandPackingSymmetryAffineVectorAction k y) else affineQuarter
            (BandPackingSymmetryAffineVectorAction k y))) → (∀ (g : BandPackingSymmetry), ∀ (q :
            Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let W := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
        let A := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
        let Z : GaussianInt × GaussianInt := (W, A)
        let M : GaussianInt × GaussianInt :=
          (W - GaussianQuarterTurn W, A + GaussianQuarterTurn A)
        (M = Z + -affineQuarter Z) → (BandPackingSymmetryAffineVectorAction g M = if
            BandPackingSymmetryReversesOrientation g then BandPackingSymmetryAffineVectorAction g
            Z + affineQuarter (BandPackingSymmetryAffineVectorAction g Z) else
            BandPackingSymmetryAffineVectorAction g Z - affineQuarter
            (BandPackingSymmetryAffineVectorAction g Z))) ) := by
  classical
  intro affineQuarter affineFacts g q i W A Z M hpat
  calc
    _ = BandPackingSymmetryAffineVectorAction g (Z + -affineQuarter Z) :=
      congrArg (BandPackingSymmetryAffineVectorAction g) hpat
    _ = BandPackingSymmetryAffineVectorAction g Z +
        BandPackingSymmetryAffineVectorAction g (-affineQuarter Z) :=
      (affineFacts g).1 _ _
    _ = BandPackingSymmetryAffineVectorAction g Z -
        BandPackingSymmetryAffineVectorAction g (affineQuarter Z) := by
      rw [(affineFacts g).2.1]
      simp [sub_eq_add_neg]
    _ = _ := by
      rw [(affineFacts g).2.2]
      cases BandPackingSymmetryReversesOrientation g <;>
        ext <;> simp [affineQuarter, GaussianQuarterTurn]; ring

private theorem hAphase :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 :
            ℕ)),  ∀ (delta : Bool), (∀ (i : Fin (3 : ℕ)),
        let e := if delta = true then (-1 : GaussianInt) else (1 : GaussianInt);
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
            -GaussianQuarterTurn cyclic.2 else cyclic.2) → (
        let q' := BandPackingSymmetryQuadrupleAction g q
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        let W := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
        let A := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
        let Z : GaussianInt × GaussianInt := (W, A)
        let A' := BandVectors.2 (q' ((sigma i + 2).succ))
          (q' ((sigma i + 1).succ))
        A' = (if delta then (-1 : GaussianInt) else 1) * (if
            BandPackingSymmetryReversesOrientation g then -GaussianQuarterTurn
            (BandPackingSymmetryAffineVectorAction g Z).2 else
            (BandPackingSymmetryAffineVectorAction g Z).2)) ) := by
  classical
  intro g q i delta hcyc q' sigma W A Z A'
  simpa [A', Z, q', sigma, BandPackingSymmetryReversesOrientation] using
    (hcyc i).2

private theorem hMphase :
    (by
      classical
      exact
        let affineQuarter := fun (z : GaussianInt × GaussianInt) =>
          (GaussianQuarterTurn z.1,
            -GaussianQuarterTurn z.2);
        ∀ (g : BandPackingSymmetry)
          (q : Fin (4 : ℕ) → CircleCoordinates)
          (i : Fin (3 : ℕ)) (delta : Bool),
          let q' := BandPackingSymmetryQuadrupleAction g q;
          let sigma := fun (j : Fin (3 : ℕ)) =>
            if
                BandPackingSymmetryReversesOrientation g =
                  true then
              -j
            else j;
          let W :=
            BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ)
              (q (i + (1 : Fin (3 : ℕ))).succ);
          let A :=
            BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
              (q (i + (1 : Fin (3 : ℕ))).succ);
          let Z := (W, A);
          let M :=
            (W - GaussianQuarterTurn W,
              A + GaussianQuarterTurn A);
          let W' :=
            BandVectors.1
              (q' (sigma i + (2 : Fin (3 : ℕ))).succ)
              (q' (sigma i + (1 : Fin (3 : ℕ))).succ);
          let A' :=
            BandVectors.2
              (q' (sigma i + (2 : Fin (3 : ℕ))).succ)
              (q' (sigma i + (1 : Fin (3 : ℕ))).succ);
          (W' =
              (if delta = true then (-1 : GaussianInt) else (1 : GaussianInt)) *
                if
                    BandPackingSymmetryReversesOrientation g =
                      true then
                  GaussianQuarterTurn
                    (BandPackingSymmetryVectorAction g W)
                else BandPackingSymmetryVectorAction g W) →
            (BandPackingSymmetryAffineVectorAction g Z).1 =
                BandPackingSymmetryVectorAction g Z.1 →
              (BandPackingSymmetryAffineVectorAction g M =
                  if
                      BandPackingSymmetryReversesOrientation g =
                        true then
                    BandPackingSymmetryAffineVectorAction g Z +
                      affineQuarter
                        (BandPackingSymmetryAffineVectorAction g
                          Z)
                  else
                    BandPackingSymmetryAffineVectorAction g Z -
                      affineQuarter
                        (BandPackingSymmetryAffineVectorAction g
                          Z)) →
                (A' =
                    (if delta = true then (-1 : GaussianInt) else (1 : GaussianInt)) *
                      if
                          BandPackingSymmetryReversesOrientation
                              g =
                            true then
                        -GaussianQuarterTurn
                            (BandPackingSymmetryAffineVectorAction
                                g Z).2
                      else
                        (BandPackingSymmetryAffineVectorAction g
                            Z).2) →
                  (W' - GaussianQuarterTurn W',
                      A' + GaussianQuarterTurn A') =
                    if delta = true then
                      -BandPackingSymmetryAffineVectorAction g M
                    else
                      BandPackingSymmetryAffineVectorAction g M) := by
  classical
  intro affineQuarter g q i delta q' sigma W A Z M W' A' hWphase haffFst hactM hAphase
  rw [hWphase, hAphase, ← haffFst, hactM]
  cases delta <;> cases hor : BandPackingSymmetryReversesOrientation g <;>
    ext <;> simp [affineQuarter, GaussianQuarterTurn] <;> ring

private theorem hcentGoal :
    (by
      classical
      exact
        (∀ (k : BandPackingSymmetry),
            ∀ (z : GaussianInt × GaussianInt),
              (BandPackingSymmetryAffineVectorAction k z).1 =
                BandPackingSymmetryVectorAction k z.1) →
          ∀ (g : BandPackingSymmetry),
            ∀ (C' : CircleCoordinates),
              ∀ (T : ProtoTile),
                ∀ (T' : ProtoTile),
                  ∀ (h : PartialOdometer),
                    ∀ (h' : PartialOdometer),
                      ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
                        ∀ (i : Fin (3 : ℕ)),
                          ∀ (e : Bool),
                            TileCentroid T' - TileCentroid T =
                                (if e = true then (1 : ℝ) else (-1 : ℝ)) •
                                (1 / 2 : ℝ) •
                                (GaussianRealPoint
                                (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ)) -
                                (-(GaussianRealPoint
                                (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ))).2,
                                (GaussianRealPoint
                                (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ))).1)) →
                              (C'.1 = (0 : ℤ) ∨
                                ∃ (p : ℝ × ℝ) (p' : ℝ × ℝ),
                                PartialOdometerSlope h = some p ∧
                                PartialOdometerSlope h' = some p' ∧
                                p'.1 - p.1 =
                                (if e = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
                                ((↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ)).re :
                                ℝ) -
                                (↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ)).im :
                                ℝ)) ∧
                                p'.2 - p.2 =
                                (if e = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
                                ((↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ)).im :
                                ℝ) +
                                (↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ)).re :
                                ℝ))) →
                                ∀ (delta : Bool),
                                (∀ (i : Fin (3 : ℕ)),
                                let e :=
                                if delta = true then (-1 : GaussianInt)
                              else (1 : GaussianInt);
                              let incoming :=
                                BandPackingSymmetryAffineVectorAction g
                                (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))),
                                BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))));
                              let cyclic :=
                                BandPackingSymmetryAffineVectorAction g
                                (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ),
                                BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ));
                              BandVectors.2
                                (BandPackingSymmetryQuadrupleAction g q
                                ((fun (i : Fin (3 : ℕ)) =>
                                if BandPackingSymmetryReversesOrientation g = true then -i
                              else i)
                                i).succ)
                                (BandPackingSymmetryQuadrupleAction g q
                                (0 : Fin (4 : ℕ))) =
                                e * incoming.2 ∧
                                BandVectors.2
                                (BandPackingSymmetryQuadrupleAction g q
                                ((fun (i : Fin (3 : ℕ)) =>
                                if BandPackingSymmetryReversesOrientation g = true then -i
                              else i)
                                i +
                                (2 : Fin (3 : ℕ))).succ)
                                (BandPackingSymmetryQuadrupleAction g q
                                ((fun (i : Fin (3 : ℕ)) =>
                                if BandPackingSymmetryReversesOrientation g = true then -i
                              else i)
                                i +
                                (1 : Fin (3 : ℕ))).succ) =
                                e *
                                if BandPackingSymmetryReversesOrientation g = true then
                                -GaussianQuarterTurn cyclic.2
                              else cyclic.2) →
                                let q' := BandPackingSymmetryQuadrupleAction g q;
                              let sigma : Fin 3 → Fin 3 := fun j =>
                                if BandPackingSymmetryReversesOrientation g then -j
                              else j;
                              let e' := xor e delta;
                              let W := BandVectors.1 (q (i + 2).succ) (q (i + 1).succ);
                              let A := BandVectors.2 (q (i + 2).succ) (q (i + 1).succ);
                              let M : GaussianInt × GaussianInt :=
                                (W - GaussianQuarterTurn W, A + GaussianQuarterTurn A);
                              let W' :=
                                BandVectors.1 (q' (sigma i + 2).succ)
                                (q' (sigma i + 1).succ);
                              let A' :=
                                BandVectors.2 (q' (sigma i + 2).succ)
                                (q' (sigma i + 1).succ);
                              let eReal : ℝ := if e then 1 else -1;
                              let k : ℝ := eReal / 2;
                              TileCentroid T' - TileCentroid T =
                                k • GaussianRealPoint M.1 →
                                TileCentroid (BandPackingSymmetryTileAction g T') -
                                TileCentroid (BandPackingSymmetryTileAction g T) =
                                k •
                                GaussianRealPoint
                                (BandPackingSymmetryAffineVectorAction g
                                (M.1, (0 : GaussianInt))).1 ∧
                                BandPackingSymmetrySlopeAction g T' ((0 : ℝ), (0 : ℝ)) -
                                BandPackingSymmetrySlopeAction g T ((0 : ℝ), (0 : ℝ)) =
                                k •
                                GaussianRealPoint
                                (BandPackingSymmetryAffineVectorAction g
                                (M.1, (0 : GaussianInt))).2 →
                                (W' =
                                (if delta then (-1 : GaussianInt) else 1) *
                                if BandPackingSymmetryReversesOrientation g then
                                GaussianQuarterTurn (BandPackingSymmetryVectorAction g W)
                              else BandPackingSymmetryVectorAction g W) →
                                ((W' - GaussianQuarterTurn W',
                                A' + GaussianQuarterTurn A') =
                                if delta then -BandPackingSymmetryAffineVectorAction g M
                              else BandPackingSymmetryAffineVectorAction g M) →
                                (W' - GaussianQuarterTurn W',
                                A' + GaussianQuarterTurn A').1 =
                                (if delta = true then
                                -BandPackingSymmetryAffineVectorAction g M
                              else BandPackingSymmetryAffineVectorAction g M).1 →
                                TileCentroid (BandPackingSymmetryTileAction g T') -
                                TileCentroid (BandPackingSymmetryTileAction g T) =
                                (if e' then (1 : ℝ) else -1) •
                                (1 / 2 : ℝ) •
                                (GaussianRealPoint W' -
                                (-(GaussianRealPoint W').2, (GaussianRealPoint W').1))
    ) := by
  classical
  intro affineFirst g C' T T' h h' q i e hcent hslope delta hcyc q' sigma e' W A M W' A' eReal k
      hcentM htr hWphase hMphase hmFst
  have hreal : GaussianRealPoint (W' - GaussianQuarterTurn W') =
      GaussianRealPoint W' -
        (-(GaussianRealPoint W').2, (GaussianRealPoint W').1) := by
    ext <;> simp [GaussianRealPoint, GaussianQuarterTurn]
  have hfst : (BandPackingSymmetryAffineVectorAction g (M.1, 0)).1 =
      (BandPackingSymmetryAffineVectorAction g M).1 := by
    rw [affineFirst, affineFirst]
  rw [← hreal]
  have htr' : TileCentroid (BandPackingSymmetryTileAction g T') -
      TileCentroid (BandPackingSymmetryTileAction g T) =
    k • GaussianRealPoint (BandPackingSymmetryAffineVectorAction g M).1 := by
    simpa only [hfst] using htr.1
  calc
    _ = k • GaussianRealPoint (BandPackingSymmetryAffineVectorAction g M).1 := htr'
    _ = (if e' then (1 : ℝ) else -1) • ((1 / 2 : ℝ) •
        GaussianRealPoint (W' - GaussianQuarterTurn W')) := by
      have hpointSign : GaussianRealPoint (W' - GaussianQuarterTurn W') =
          (if delta then (-1 : ℝ) else 1) •
            GaussianRealPoint (BandPackingSymmetryAffineVectorAction g M).1 := by
        have hh := congrArg GaussianRealPoint hmFst
        cases delta <;> simpa [GaussianRealPoint, smul_eq_mul] using hh
      rw [hpointSign]
      cases e <;> cases delta <;>
        simp only [Bool.false_eq_true, ↓reduceIte, GaussianRealPoint, Int.reduceNeg,
            GaussianInt.intCast_re, GaussianInt.intCast_im, Prod.smul_mk, smul_eq_mul,
            Bool.bne_true, Bool.not_false, one_div, neg_smul, one_smul, Prod.neg_mk, mul_neg,
            Prod.mk.injEq, k, eReal, e', bne_self_eq_false, Bool.bne_false, neg_neg] <;> ring <;>
                trivial
    _ = _ := by rfl

private theorem hsr :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), (Finset.Nonempty
            T.cells → PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g h) =
            Option.map (BandPackingSymmetrySlopeAction g T) (PartialOdometerSlope h)) → (∀ (p : ℝ
            × ℝ), (PartialOdometerSlope h = some p) → ((Finset.Nonempty T.cells) →
            (PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g h) = some
            (BandPackingSymmetrySlopeAction g T p)))) ) := by
  classical
  intro g T h hST p hsp hTne
  rw [hST hTne, hsp]
  rfl

private abbrev hsr' := ApollonianSuperharmonic.MarkedCovarianceGeometry.hsr

private theorem hsourceSlope :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
          ∀ (i : Fin (3 : ℕ)),
            ∀ (e : Bool),
              let W := BandVectors.1 (q (i + 2).succ) (q (i + 1).succ);
              let A := BandVectors.2 (q (i + 2).succ) (q (i + 1).succ);
              let M : GaussianInt × GaussianInt :=
                (W - GaussianQuarterTurn W, A + GaussianQuarterTurn A);
              let eReal : ℝ := if e then 1 else -1;
              let k : ℝ := eReal / 2;
              ∀ (p : ℝ × ℝ),
                ∀ (p' : ℝ × ℝ),
                  p'.1 - p.1 =
                      (if e = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
                        ((↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ)).re :
                            ℝ) -
                          (↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ)).im :
                            ℝ)) →
                    p'.2 - p.2 =
                        (if e = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
                          ((↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ)).im :
                              ℝ) +
                            (↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ)).re :
                              ℝ)) →
                      p' - p = k • GaussianRealPoint M.2
    )
            := by
  classical
  intro q i e W A M eReal k p p' hRe hIm
  have hRe' : p'.1 - p.1 = (if e then (1 : ℝ) else -1) * (1 / 2) *
      (((GaussianInt.toComplex A).re) - (GaussianInt.toComplex A).im) := by
    simpa [A] using hRe
  have hIm' : p'.2 - p.2 = (if e then (1 : ℝ) else -1) * (1 / 2) *
      (((GaussianInt.toComplex A).im) + (GaussianInt.toComplex A).re) := by
    simpa [A] using hIm
  apply Prod.ext
  · calc
      p'.1 - p.1 = (if e then (1 : ℝ) else -1) * (1 / 2) *
          (((GaussianInt.toComplex A).re) - (GaussianInt.toComplex A).im) := hRe'
      _ = (k • GaussianRealPoint M.2).1 := by
        cases e <;> simp [A, M, k, eReal, GaussianRealPoint,
          GaussianQuarterTurn, smul_eq_mul] <;> ring
  · calc
      p'.2 - p.2 = (if e then (1 : ℝ) else -1) * (1 / 2) *
          (((GaussianInt.toComplex A).im) + (GaussianInt.toComplex A).re) := hIm'
      _ = (k • GaussianRealPoint M.2).2 := by
        cases e <;> simp [A, M, k, eReal, GaussianRealPoint,
          GaussianQuarterTurn, smul_eq_mul]; ring

private theorem hdiff :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (q : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (e : Bool),
        let W := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
        let A := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
        let M : GaussianInt × GaussianInt :=
          (W - GaussianQuarterTurn W, A + GaussianQuarterTurn A)
        let eReal : ℝ := if e then 1 else -1
        let k : ℝ := eReal / 2
        ∀ (p : ℝ × ℝ), ∀ (p' : ℝ × ℝ), (TileCentroid (BandPackingSymmetryTileAction g T') -
            TileCentroid (BandPackingSymmetryTileAction g T) = k • GaussianRealPoint
            (BandPackingSymmetryAffineVectorAction g (M.1, M.2)).1 ∧
            BandPackingSymmetrySlopeAction g T' p' - BandPackingSymmetrySlopeAction g T p = k •
            GaussianRealPoint (BandPackingSymmetryAffineVectorAction g (M.1, M.2)).2) → (
        let r := BandPackingSymmetrySlopeAction g T p
        let r' := BandPackingSymmetrySlopeAction g T' p'
        r' - r = k • GaussianRealPoint (BandPackingSymmetryAffineVectorAction g M).2) ) := by
  classical
  intro g T T' q i e W A M eReal k p p' htrSlope r r'
  simpa [r, r'] using htrSlope.2

private abbrev hactM2 :=
  ApollonianSuperharmonic.MarkedCovarianceGeometry.hactM

private theorem hMphase2 :
    (by
      classical
        exact
        let affineQuarter : GaussianInt × GaussianInt → GaussianInt × GaussianInt :=
          fun z => (GaussianQuarterTurn z.1, -GaussianQuarterTurn z.2);
        (∀ (k : BandPackingSymmetry),
            ∀ (z : GaussianInt × GaussianInt),
              (BandPackingSymmetryAffineVectorAction k z).1 =
                BandPackingSymmetryVectorAction k z.1) →
          (∀ (g : BandPackingSymmetry),
            ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
              ∀ (i : Fin (3 : ℕ)),
                ∀ (delta : Bool),
                  (let q' := BandPackingSymmetryQuadrupleAction g q;
                  let sigma : Fin 3 → Fin 3 := fun j =>
                    if BandPackingSymmetryReversesOrientation g then -j else j;
                  let W := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ));
                  let A := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ));
                  let Z : GaussianInt × GaussianInt := (W, A);
                  let M : GaussianInt × GaussianInt :=
                    (W - GaussianQuarterTurn W, A + GaussianQuarterTurn A);
                  let W' :=
                    BandVectors.1 (q' ((sigma i + 2).succ))
                      (q' ((sigma i + 1).succ));
                  let A' :=
                    BandVectors.2 (q' ((sigma i + 2).succ))
                      (q' ((sigma i + 1).succ));
                  (W' =
                      (if delta then (-1 : GaussianInt) else 1) *
                        (if BandPackingSymmetryReversesOrientation g then
                          GaussianQuarterTurn (BandPackingSymmetryVectorAction g W)
                        else BandPackingSymmetryVectorAction g W)) →
                    ((A' =
                        (if delta then (-1 : GaussianInt) else 1) *
                          (if BandPackingSymmetryReversesOrientation g then
                            -GaussianQuarterTurn
                                (BandPackingSymmetryAffineVectorAction g Z).2
                          else (BandPackingSymmetryAffineVectorAction g Z).2)) →
                      ((BandPackingSymmetryAffineVectorAction g M =
                          if BandPackingSymmetryReversesOrientation g then
                            BandPackingSymmetryAffineVectorAction g Z +
                              affineQuarter
                                (BandPackingSymmetryAffineVectorAction g Z)
                          else
                            BandPackingSymmetryAffineVectorAction g Z -
                              affineQuarter
                                (BandPackingSymmetryAffineVectorAction g Z)) →
                        ((W' - GaussianQuarterTurn W',
                            A' + GaussianQuarterTurn A') =
                          if delta then -(BandPackingSymmetryAffineVectorAction g M)
                          else BandPackingSymmetryAffineVectorAction g M)))))) := by
  classical
  intro affineQuarter affineFirst g q i delta q' sigma W A Z M W' A' hWphase2 hAphase2 hactM2
  rw [hWphase2, hAphase2, ← affineFirst g Z, hactM2]
  cases delta <;> cases hor : BandPackingSymmetryReversesOrientation g <;>
    ext <;> simp [affineQuarter, GaussianQuarterTurn] <;> ring

private theorem hpointSignAt762 :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry)
          (q : Fin (4 : ℕ) → CircleCoordinates)
          (i : Fin (3 : ℕ)) (delta : Bool),
          let q' := BandPackingSymmetryQuadrupleAction g q;
          let sigma := fun (j : Fin (3 : ℕ)) =>
            if
                BandPackingSymmetryReversesOrientation g =
                  true then
              -j
            else j;
          let W :=
            BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ)
              (q (i + (1 : Fin (3 : ℕ))).succ);
          let A :=
            BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
              (q (i + (1 : Fin (3 : ℕ))).succ);
          let M :=
            (W - GaussianQuarterTurn W,
              A + GaussianQuarterTurn A);
          let W' :=
            BandVectors.1
              (q' (sigma i + (2 : Fin (3 : ℕ))).succ)
              (q' (sigma i + (1 : Fin (3 : ℕ))).succ);
          let A' :=
            BandVectors.2
              (q' (sigma i + (2 : Fin (3 : ℕ))).succ)
              (q' (sigma i + (1 : Fin (3 : ℕ))).succ);
          ((W' - GaussianQuarterTurn W',
                A' + GaussianQuarterTurn A') =
              if delta = true then
                -BandPackingSymmetryAffineVectorAction g M
              else BandPackingSymmetryAffineVectorAction g M) →
            GaussianRealPoint
                (A' + GaussianQuarterTurn A') =
              (if delta = true then (-1 : ℝ) else (1 : ℝ)) •
                GaussianRealPoint
                  (BandPackingSymmetryAffineVectorAction g M).2) := by
  classical
  intro g q i delta q' sigma W A M W' A' hMphase2
  have hh := congrArg (fun z : GaussianInt × GaussianInt =>
    GaussianRealPoint z.2) hMphase2
  cases delta <;> simpa [GaussianRealPoint, smul_eq_mul] using hh

private theorem hdiff' :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry)
          (T T' : ProtoTile)
          (q : Fin (4 : ℕ) → CircleCoordinates)
          (i : Fin (3 : ℕ)) (e delta : Bool),
          let q' := BandPackingSymmetryQuadrupleAction g q;
          let sigma := fun (j : Fin (3 : ℕ)) =>
            if
                BandPackingSymmetryReversesOrientation g =
                  true then
              -j
            else j;
          let e' := e ^^ delta;
          let W :=
            BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ)
              (q (i + (1 : Fin (3 : ℕ))).succ);
          let A :=
            BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
              (q (i + (1 : Fin (3 : ℕ))).succ);
          let M :=
            (W - GaussianQuarterTurn W,
              A + GaussianQuarterTurn A);
          let A' :=
            BandVectors.2
              (q' (sigma i + (2 : Fin (3 : ℕ))).succ)
              (q' (sigma i + (1 : Fin (3 : ℕ))).succ);
          let eReal := if e = true then (1 : ℝ) else (-1 : ℝ);
          let k := eReal / (2 : ℝ);
          ∀ (p p' : ℝ × ℝ),
            let r := BandPackingSymmetrySlopeAction g T p;
            let r' := BandPackingSymmetrySlopeAction g T' p';
            r' - r =
                k •
                  GaussianRealPoint
                    (BandPackingSymmetryAffineVectorAction g
                        M).2 →
              GaussianRealPoint
                    (A' + GaussianQuarterTurn A') =
                  (if delta = true then (-1 : ℝ) else (1 : ℝ)) •
                    GaussianRealPoint
                      (BandPackingSymmetryAffineVectorAction g
                          M).2 →
                r' - r =
                  (if e' = true then (1 : ℝ) else (-1 : ℝ)) •
                    (1 / 2 : ℝ) •
                      GaussianRealPoint
                        (A' + GaussianQuarterTurn A')) := by
  classical
  intro g T T' q i e delta q' sigma e' W A M A' eReal k p p' r r' hdiff hpointSign
  rw [hdiff, hpointSign]
  cases e <;> cases delta <;>
    ext <;> simp [e', k, eReal, smul_smul, smul_eq_mul] <;> ring

private theorem finiteCompanion :
    (by
      classical
      exact
        ∀ (L : GaussianInt → GaussianInt), ∀ (rev : Bool), ∀ (delta : Bool), ∀ (s : Fin 4), ∀ (a
            : GaussianInt), ∀ (a' : GaussianInt), (∀ z, L (-z) = -L z) →
          (∀ z, L (GaussianQuarterTurn z) =
            if rev then -GaussianQuarterTurn (L z) else GaussianQuarterTurn (L z)) →
          a' = (if delta then -L a else L a) →
        let s' : Fin 4 := if rev then -s - 1 + (if delta then 2 else 0)
            else s + (if delta then 2 else 0);
          L ((⟨0, 1⟩ : GaussianInt)^s.val *
            (if Even s.val then GaussianQuarterTurn a else a)) =
          (⟨0, 1⟩ : GaussianInt)^s'.val *
            (if Even s'.val then GaussianQuarterTurn a' else a') ) := by
  classical
  intro L rev delta s a a' hneg hquarter hphase
  dsimp
  have qm (z : GaussianInt) : GaussianQuarterTurn z =
      (⟨0, 1⟩ : GaussianInt) * z := by
    ext <;> simp [GaussianQuarterTurn]
  have unit2 : (⟨0, 1⟩ : GaussianInt)^2 = -1 := by
    simp only [pow_two]
    ext <;> norm_num
  have unit3 : (⟨0, 1⟩ : GaussianInt)^3 = -⟨0, 1⟩ := by
    rw [pow_succ, unit2]
    norm_num
  have qneg (z : GaussianInt) :
      GaussianQuarterTurn (-z) = -GaussianQuarterTurn z := by
    ext <;> simp [GaussianQuarterTurn]
  have p2 (z : GaussianInt) : (⟨0, 1⟩ : GaussianInt)^2 * z = -z := by
    rw [unit2]
    simp
  have p3 (z : GaussianInt) : (⟨0, 1⟩ : GaussianInt)^3 * z =
      -GaussianQuarterTurn z := by
    rw [unit3]
    calc
      (-(⟨0, 1⟩ : GaussianInt)) * z =
          -((⟨0, 1⟩ : GaussianInt) * z) := by simp
      _ = -GaussianQuarterTurn z := by rw [qm]
  have ev0 : Even 0 := ⟨0, by omega⟩
  have ev2 : Even 2 := ⟨1, by omega⟩
  have odd3 : ¬ Even 3 := by rintro ⟨r, hr⟩; omega
  cases hrev : rev <;> cases hdel : delta <;> fin_cases s
  all_goals
    norm_num [Fin.val_neg, Fin.val_add, Fin.val_sub] at ⊢
    simp [ev0, ev2, odd3, p2, p3,
      hphase, hquarter, hneg, hrev, hdel, qneg, ← qm]

private abbrev allNeg := ApollonianSuperharmonic.LatticeAdjacentPackingSymmetryFacts.vectorNegation

private theorem allQuarter :
    (by
      classical
      exact
        (∀ (k : BandPackingSymmetry), ∀ (z : GaussianInt), BandPackingSymmetryVectorAction k (-z)
            = -BandPackingSymmetryVectorAction k z) → (∀ (k : BandPackingSymmetry), ∀ (z :
            GaussianInt), BandPackingSymmetryVectorAction k (GaussianQuarterTurn z) = if
            BandPackingSymmetryReversesOrientation k then -GaussianQuarterTurn
            (BandPackingSymmetryVectorAction k z) else GaussianQuarterTurn
            (BandPackingSymmetryVectorAction k z)) ) := by
  classical
  intro allNeg k
  induction k with
  | identity => intro z; rfl
  | negate => intro z; rfl
  | conjugate =>
      intro z
      ext <;> simp [BandPackingSymmetryVectorAction,
        BandPackingSymmetryReversesOrientation, GaussianQuarterTurn, GaussianReflection]
  | shift w => intro z; rfl
  | comp a b iha ihb =>
      intro z
      cases ha : BandPackingSymmetryReversesOrientation a <;>
        cases hb : BandPackingSymmetryReversesOrientation b <;>
        simp [BandPackingSymmetryVectorAction, BandPackingSymmetryReversesOrientation,
          ihb, iha, ha, hb, allNeg]

private theorem qmul :
    (by
      classical
      exact
        ∀ (z : GaussianInt), GaussianQuarterTurn z = (⟨0, 1⟩ : GaussianInt) * z ) := by
  classical
  intro z
  ext <;> simp [GaussianQuarterTurn]

private theorem hflipA :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let a := BandVectors.1 (q i.succ) (q 0)
        let b := BandVectors.1 (q 0) (q i.succ)
        (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (q (0 : Fin (4 : ℕ)))
            (q i.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (q i.succ) (q (0 :
            Fin (4 : ℕ)))) → ((∀ (z : GaussianInt), GaussianQuarterTurn z = (⟨0, 1⟩ :
            GaussianInt) * z) → (b = GaussianQuarterTurn a)) ) := by
  classical
  intro q i a b hflip qmul
  calc
    b = (⟨0, 1⟩ : GaussianInt) * a := hflip.1
    _ = GaussianQuarterTurn a := (qmul a).symm

private theorem hflipB :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let q' := BandPackingSymmetryQuadrupleAction g q
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        let a' := BandVectors.1 (q' (sigma i).succ) (q' 0)
        let b' := BandVectors.1 (q' 0) (q' (sigma i).succ)
        (BandVectors.1 (q' (0 : Fin (4 : ℕ))) (q' (sigma i).succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.1 (q' (sigma i).succ) (q' (0 : Fin (4 : ℕ))) ∧
            BandVectors.2 (q' (0 : Fin (4 : ℕ))) (q' (sigma i).succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (q' (sigma i).succ) (q' (0 : Fin (4 : ℕ)))) → ((∀ (z :
            GaussianInt), GaussianQuarterTurn z = (⟨0, 1⟩ : GaussianInt) * z) → (b' =
            GaussianQuarterTurn a')) ) := by
  classical
  intro g q i q' sigma a' b' hflip' qmul
  calc
    b' = (⟨0, 1⟩ : GaussianInt) * a' := hflip'.1
    _ = GaussianQuarterTurn a' := (qmul a').symm

private theorem hphase :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry),
          ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
            ∀ (i : Fin (3 : ℕ)),
              ∀ (delta : Bool),
                BandPackingSymmetryScopedPhase g q delta →
                  let q' := BandPackingSymmetryQuadrupleAction g q
                  let sigma : Fin 3 → Fin 3 := fun j =>
                    if BandPackingSymmetryReversesOrientation g then -j else j
                  let a := BandVectors.1 (q i.succ) (q 0)
                  let a' := BandVectors.1 (q' (sigma i).succ) (q' 0)
                  a' =
                    if delta then -BandPackingSymmetryVectorAction g a
                    else BandPackingSymmetryVectorAction g a
    ) := by
  classical
  intro g q i delta hdelta q' sigma a a'
  have hh := hdelta i
  dsimp [BandPackingSymmetryScopedPhase, sigma, a', a] at hh
  cases delta <;> simpa using hh.1

private theorem linNeg :
    (by
      classical
      exact
        (∀ (k : BandPackingSymmetry), ∀ (z : GaussianInt), BandPackingSymmetryVectorAction k (-z)
            = -BandPackingSymmetryVectorAction k z) → (∀ (g : BandPackingSymmetry), ∀ (z :
            GaussianInt), BandPackingSymmetryVectorAction g (-z) =
            -BandPackingSymmetryVectorAction g z) ) := by
  classical
  intro allNeg g z
  exact allNeg g z

private theorem linQuarter :
    (by
      classical
      exact
        (∀ (k : BandPackingSymmetry), ∀ (z : GaussianInt), BandPackingSymmetryVectorAction k
            (GaussianQuarterTurn z) = if BandPackingSymmetryReversesOrientation k then
            -GaussianQuarterTurn (BandPackingSymmetryVectorAction k z) else GaussianQuarterTurn
            (BandPackingSymmetryVectorAction k z)) → (∀ (g : BandPackingSymmetry), ∀ (z :
            GaussianInt), BandPackingSymmetryVectorAction g (GaussianQuarterTurn z) = if
            BandPackingSymmetryReversesOrientation g then -GaussianQuarterTurn
            (BandPackingSymmetryVectorAction g z) else GaussianQuarterTurn
            (BandPackingSymmetryVectorAction g z)) ) := by
  classical
  intro allQuarter g z
  exact allQuarter g z

private theorem hdisp :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (s : Fin (4 : ℕ)), ∀ (delta : Bool),
        let s' : Fin 4 := if BandPackingSymmetryReversesOrientation g then
          -s - 1 + (if delta then 2 else 0) else s + (if delta then 2 else 0)
        (∀ (L : GaussianInt → GaussianInt), ∀ (rev : Bool), ∀ (delta : Bool), ∀ (s : Fin 4), ∀ (a
            : GaussianInt), ∀ (a' : GaussianInt), (∀ z, L (-z) = -L z) →
          (∀ z, L (GaussianQuarterTurn z) =
            if rev then -GaussianQuarterTurn (L z) else GaussianQuarterTurn (L z)) →
          a' = (if delta then -L a else L a) →
        let s' : Fin 4 := if rev then -s - 1 + (if delta then 2 else 0)
            else s + (if delta then 2 else 0);
          L ((⟨0, 1⟩ : GaussianInt)^s.val *
            (if Even s.val then GaussianQuarterTurn a else a)) =
          (⟨0, 1⟩ : GaussianInt)^s'.val *
            (if Even s'.val then GaussianQuarterTurn a' else a')) → (∀ (q : Fin (4 : ℕ) →
                CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let q' := BandPackingSymmetryQuadrupleAction g q
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        let a := BandVectors.1 (q i.succ) (q 0)
        let b := BandVectors.1 (q 0) (q i.succ)
        let a' := BandVectors.1 (q' (sigma i).succ) (q' 0)
        let b' := BandVectors.1 (q' 0) (q' (sigma i).succ)
        let d := (⟨0, 1⟩ : GaussianInt)^s.val * (if Even s.val then b else a)
        let d' := (⟨0, 1⟩ : GaussianInt)^s'.val *
          (if Even s'.val then b' else a')
        (b = GaussianQuarterTurn a) → ((b' = GaussianQuarterTurn a') → ((a' = if delta then
            -BandPackingSymmetryVectorAction g a else BandPackingSymmetryVectorAction g a) → ((∀
            (z : GaussianInt), BandPackingSymmetryVectorAction g (-z) =
            -BandPackingSymmetryVectorAction g z) → ((∀ (z : GaussianInt),
            BandPackingSymmetryVectorAction g (GaussianQuarterTurn z) = if
            BandPackingSymmetryReversesOrientation g then -GaussianQuarterTurn
            (BandPackingSymmetryVectorAction g z) else GaussianQuarterTurn
            (BandPackingSymmetryVectorAction g z)) → (BandPackingSymmetryVectorAction g d =
            d')))))) ) := by
  classical
  intro g s delta s' finiteCompanion q i q' sigma a b a' b' d d' hflipA hflipB hphase linNeg
      linQuarter
  dsimp [d, d']
  rw [hflipA, hflipB]
  exact finiteCompanion (BandPackingSymmetryVectorAction g)
    (BandPackingSymmetryReversesOrientation g) delta s a a'
    linNeg linQuarter hphase

private theorem htile :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 :
            ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (delta : Bool), ∀ (T : ProtoTile),
        let q' := BandPackingSymmetryQuadrupleAction g q
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        let s' : Fin 4 := if BandPackingSymmetryReversesOrientation g then
          -s - 1 + (if delta then 2 else 0) else s + (if delta then 2 else 0)
        let a := BandVectors.1 (q i.succ) (q 0)
        let b := BandVectors.1 (q 0) (q i.succ)
        let a' := BandVectors.1 (q' (sigma i).succ) (q' 0)
        let b' := BandVectors.1 (q' 0) (q' (sigma i).succ)
        let d := (⟨0, 1⟩ : GaussianInt)^s.val * (if Even s.val then b else a)
        let d' := (⟨0, 1⟩ : GaussianInt)^s'.val *
          (if Even s'.val then b' else a')
        let oldRight := TileTranslation T d
        let newRight := TileTranslation (BandPackingSymmetryTileAction g T) d'
        (BandPackingSymmetryVectorAction g d = d') → ((∀ (T : ProtoTile), ∀ (v : GaussianInt),
            BandPackingSymmetryTileAction g (TileTranslation T v) = TileTranslation
            (BandPackingSymmetryTileAction g T) (BandPackingSymmetryVectorAction g v)) →
            (BandPackingSymmetryTileAction g oldRight = newRight)) ) := by
  classical
  intro g q i s delta T q' sigma s' a b a' b' d d' oldRight newRight hdisp htranslation
  dsimp [oldRight, newRight]
  rw [htranslation T d, hdisp]

private theorem hinjAt948 :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), Function.Injective (BandPackingSymmetryVectorAction g) ) := by
  classical
  intro g
  rcases (BandPackingSymmetryInversePhaseCancellation).2 g with
    ⟨inv, _, _, _, _, _, _, hleft, _, _, _, _⟩
  intro u v huv
  calc
    u = BandPackingSymmetryVectorAction inv
        (BandPackingSymmetryVectorAction g u) := (hleft u).symm
    _ = BandPackingSymmetryVectorAction inv
        (BandPackingSymmetryVectorAction g v) := congrArg _ huv
    _ = v := hleft v

private theorem hfoot :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 :
            ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (delta : Bool), ∀ (T : ProtoTile),
        let q' := BandPackingSymmetryQuadrupleAction g q
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        let s' : Fin 4 := if BandPackingSymmetryReversesOrientation g then
          -s - 1 + (if delta then 2 else 0) else s + (if delta then 2 else 0)
        let a := BandVectors.1 (q i.succ) (q 0)
        let b := BandVectors.1 (q 0) (q i.succ)
        let a' := BandVectors.1 (q' (sigma i).succ) (q' 0)
        let b' := BandVectors.1 (q' 0) (q' (sigma i).succ)
        let d := (⟨0, 1⟩ : GaussianInt)^s.val * (if Even s.val then b else a)
        let d' := (⟨0, 1⟩ : GaussianInt)^s'.val *
          (if Even s'.val then b' else a')
        let oldRight := TileTranslation T d
        let newRight := TileTranslation (BandPackingSymmetryTileAction g T) d'
        (∀ (T : ProtoTile), FootprintVertices (BandPackingSymmetryTileAction g T) =
            BandPackingSymmetryVectorAction g '' FootprintVertices T) →
            ((BandPackingSymmetryTileAction g oldRight = newRight) → (FootprintVertices newRight
            = BandPackingSymmetryVectorAction g '' FootprintVertices oldRight)) ) := by
  classical
  intro g q i s delta T q' sigma s' a b a' b' d d' oldRight newRight hfootprint htile
  calc
    FootprintVertices newRight =
        FootprintVertices (BandPackingSymmetryTileAction g oldRight) :=
      congrArg FootprintVertices htile.symm
    _ = BandPackingSymmetryVectorAction g '' FootprintVertices oldRight := hfootprint oldRight

end MarkedCovarianceGeometry

namespace MarkedCovarianceAssembly

private theorem forwardSub :
    (by
      classical
      exact
        (∀ (g : BandPackingSymmetry),
            ∀ (h : PartialOdometer),
              ∀ (k : PartialOdometer),
                ∀ x ∈ h.domain,
                  x ∈ k.domain →
                    h.value x = k.value x →
                      (BandPackingSymmetryPartialOdometerAction g h).value
                          (BandPackingSymmetryVectorAction g x) =
                        (BandPackingSymmetryPartialOdometerAction g k).value
                          (BandPackingSymmetryVectorAction g x)) →
          (∀ (g : BandPackingSymmetry),
              ∀ (U : ProtoTile),
                ∀ (V : ProtoTile),
                  ∀ (x : ℝ × ℝ),
                    ∀ (y : ℝ × ℝ),
                      ∀ (v : GaussianInt),
                        ∀ (a : GaussianInt),
                          ∀ (k : ℝ),
                            TileCentroid V - TileCentroid U = k • GaussianRealPoint v →
                              x - y = k • GaussianRealPoint a →
                                TileCentroid (BandPackingSymmetryTileAction g V) -
                                TileCentroid (BandPackingSymmetryTileAction g U) =
                                k •
                                GaussianRealPoint
                                (BandPackingSymmetryAffineVectorAction g (v, a)).1 ∧
                                BandPackingSymmetrySlopeAction g V x -
                                BandPackingSymmetrySlopeAction g U y =
                                k •
                                GaussianRealPoint
                                (BandPackingSymmetryAffineVectorAction g (v, a)).2) →
            (let affineQuarter := fun (z : GaussianInt × GaussianInt) =>
                (GaussianQuarterTurn z.1, -GaussianQuarterTurn z.2);
              ∀ (k : BandPackingSymmetry),
                (∀ (y : GaussianInt × GaussianInt),
                    ∀ (z : GaussianInt × GaussianInt),
                      BandPackingSymmetryAffineVectorAction k (y + z) =
                        BandPackingSymmetryAffineVectorAction k y +
                          BandPackingSymmetryAffineVectorAction k z) ∧
                  (∀ (y : GaussianInt × GaussianInt),
                      BandPackingSymmetryAffineVectorAction k (-y) =
                        -BandPackingSymmetryAffineVectorAction k y) ∧
                    ∀ (y : GaussianInt × GaussianInt),
                      BandPackingSymmetryAffineVectorAction k (affineQuarter y) =
                        if BandPackingSymmetryReversesOrientation k = true then
                          -affineQuarter (BandPackingSymmetryAffineVectorAction k y)
                        else affineQuarter (BandPackingSymmetryAffineVectorAction k y)) →
              (∀ (k : BandPackingSymmetry),
                  ∀ (z : GaussianInt × GaussianInt),
                    (BandPackingSymmetryAffineVectorAction k z).1 =
                      BandPackingSymmetryVectorAction k z.1) →
                (∀ (k : BandPackingSymmetry),
                    ∀ (C : CircleCoordinates),
                      (BandPackingSymmetryCircleAction k C).1 = C.1) →
                  (∀ (C : CircleCoordinates),
                      ∀ (U : ProtoTile),
                        ∀ (k : PartialOdometer),
                          ∀ (p : ℝ × ℝ),
                            TileOdometer C U k →
                              PartialOdometerSlope k = some p → Finset.Nonempty U.cells) →
                    ∀ (g : BandPackingSymmetry),
                      ∀ (C : CircleCoordinates),
                        ∀ (C' : CircleCoordinates),
                          ∀ (T : ProtoTile),
                            ∀ (T' : ProtoTile),
                              ∀ (h : PartialOdometer),
                                ∀ (h' : PartialOdometer),
                                TileSubodometer C C' T T' h h' →
                                TileSubodometer (BandPackingSymmetryCircleAction g C)
                                (BandPackingSymmetryCircleAction g C')
                                (BandPackingSymmetryTileAction g T)
                                (BandPackingSymmetryTileAction g T')
                                (BandPackingSymmetryPartialOdometerAction g h)
                                (BandPackingSymmetryPartialOdometerAction g h')
    ) := by
  classical
  intro partialValueCov differenceTransport affineFacts affineFirst circleCurvature
      positiveSupport g C C' T T' h h' hsub
  let affineQuarter : GaussianInt × GaussianInt → GaussianInt × GaussianInt :=
    fun z => (GaussianQuarterTurn z.1, -GaussianQuarterTurn z.2)
  rcases hsub with ⟨hO, hO', hfootSub, hdomSub, hvalueSub, hwitness⟩
  obtain ⟨hOT, hdomT, hST⟩ := BandPackingSymmetryTileOdometerCovariance g C T h hO
  obtain ⟨hOT', hdomT', hST'⟩ := BandPackingSymmetryTileOdometerCovariance g C' T' h' hO'
  rcases BandPackingSymmetryTilingTransport g with
    ⟨_, _, _, _, _, _, _, hfootprint, _, _, _⟩
  refine ⟨hOT, hOT', ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [hfootprint T'] at hy
    rw [hfootprint T]
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, hfootSub hx, rfl⟩
  · intro y hy
    change y ∈ ((BandPackingSymmetryPartialOdometerAction g h').domain :
      Set GaussianInt) at hy
    rw [hdomT'] at hy
    change y ∈ ((BandPackingSymmetryPartialOdometerAction g h).domain :
      Set GaussianInt)
    rw [hdomT]
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, hdomSub hx, rfl⟩
  · intro y hy
    change y ∈ ((BandPackingSymmetryPartialOdometerAction g h').domain :
      Set GaussianInt) at hy
    rw [hdomT'] at hy
    rcases hy with ⟨x, hx, rfl⟩
    exact partialValueCov g h h' x (hdomSub hx) hx (hvalueSub x hx)
  · rcases hwitness with ⟨q, i, hq, hqC, hqC', e, hcent, hslope⟩
    obtain ⟨delta, hphase, hcyc⟩ :=
      BandPackingSymmetryAffineVectorCovariance g q hq
    let q' := BandPackingSymmetryQuadrupleAction g q
    let sigma : Fin 3 → Fin 3 := fun j =>
      if BandPackingSymmetryReversesOrientation g then -j else j
    let e' := xor e delta
    have hq' : ProperBandQuadruple q' :=
      BandPackingSymmetryProperCovariance g q hq
    have hq0 := MarkedCovarianceGeometry.hq0 g C q hqC
    have hqi := MarkedCovarianceGeometry.hqi g C' T T' h h' q i hqC' e hcent hslope
    let W := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
    let A := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
    let Z : GaussianInt × GaussianInt := (W, A)
    let M : GaussianInt × GaussianInt :=
      (W - GaussianQuarterTurn W, A + GaussianQuarterTurn A)
    let eReal : ℝ := if e then 1 else -1
    let k : ℝ := eReal / 2
    have hcentM := MarkedCovarianceGeometry.hcentM T T' q i e hcent
    have hWphase := MarkedCovarianceGeometry.hWphase g q i delta hphase
    have hAphase := MarkedCovarianceGeometry.hAphase g q i delta hcyc
    refine ⟨q', sigma i, hq', hq0, hqi, e', ?_, ?_⟩
    · have htr := differenceTransport g T T' (0, 0) (0, 0) M.1 0 k
        hcentM (by ext <;> norm_num [GaussianRealPoint])
      have haffFst := affineFirst g Z
      have hpat : M = Z + -affineQuarter Z := by
        ext <;> simp [M, Z, affineQuarter, GaussianQuarterTurn]; ring
      have hactM := MarkedCovarianceGeometry.hactM affineFacts g q i hpat
      have hMphase := MarkedCovarianceGeometry.hMphase g q i delta hWphase
          haffFst hactM hAphase
      have hmFst := congrArg Prod.fst hMphase
      have hcentGoal := MarkedCovarianceGeometry.hcentGoal affineFirst g C' T T' h h' q i e
          hcent hslope delta hcyc hcentM htr hWphase hMphase hmFst
      exact hcentGoal
    · by_cases hzero : (q i.succ).1 = 0
      · left
        rw [circleCurvature, ← hqC']
        exact hzero
      · right
        rcases hslope with hz | ⟨p, p', hsp, hsp', hRe, hIm⟩
        · have heq := congrArg Prod.fst hqC'
          exact False.elim (hzero (by simpa [heq] using hz))
        have hTne := positiveSupport C T h p hO hsp
        have heq := congrArg Prod.fst hqC'
        have hT'ne := positiveSupport C' T' h' p' hO' hsp'
        have hsr := MarkedCovarianceGeometry.hsr g T h hST p hsp hTne
        have hsr' := MarkedCovarianceGeometry.hsr' g T' h' hST' p' hsp' hT'ne
        have hsourceSlope := MarkedCovarianceGeometry.hsourceSlope q i e p p' hRe hIm
        have htrSlope := differenceTransport g T T' p' p M.1 M.2 k
          hcentM hsourceSlope
        let r := BandPackingSymmetrySlopeAction g T p
        let r' := BandPackingSymmetrySlopeAction g T' p'
        have hdiff := MarkedCovarianceGeometry.hdiff g T T' q i e p p' htrSlope
        have hpat2 : M = Z + -affineQuarter Z := by
          ext <;> simp [M, Z, affineQuarter, GaussianQuarterTurn]; ring
        have hactM2 := MarkedCovarianceGeometry.hactM2 affineFacts g q i hpat2
        have hMphase2 := MarkedCovarianceGeometry.hMphase2 affineFirst g q i delta hWphase
            hAphase hactM2
        have hpointSign := MarkedCovarianceGeometry.hpointSignAt762 g q i delta hMphase2
        have hdiff' := MarkedCovarianceGeometry.hdiff' g T T' q i e delta p p' hdiff hpointSign
        refine ⟨r, r', hsr, hsr', ?_, ?_⟩
        · cases e <;> cases delta <;>
            have hr := congrArg Prod.fst hdiff' <;>
            convert hr using 1 <;>
            simp [GaussianRealPoint, GaussianQuarterTurn, e',
              smul_eq_mul] <;> ring
        · cases e <;> cases delta <;>
            have hr := congrArg Prod.snd hdiff' <;>
            convert hr using 1 <;>
            simp [GaussianRealPoint, GaussianQuarterTurn, e',
              smul_eq_mul] <;> ring

end MarkedCovarianceAssembly

theorem BandPackingSymmetryMarkedDataCovariance :
    (∀ (g : BandPackingSymmetry), ∀ (C : CircleCoordinates), ∀ (C' : CircleCoordinates), ∀ (T :
        ProtoTile), ∀ (T' : ProtoTile), ∀ (h : PartialOdometer), ∀ (h' : PartialOdometer),
        TileSubodometer C C' T T' h h' ↔
        TileSubodometer
          (BandPackingSymmetryCircleAction g C)
          (BandPackingSymmetryCircleAction g C')
          (BandPackingSymmetryTileAction g T)
          (BandPackingSymmetryTileAction g T')
          (BandPackingSymmetryPartialOdometerAction g h)
          (BandPackingSymmetryPartialOdometerAction g h')) ∧
    (∀ (g : BandPackingSymmetry), ∀ (x : GaussianInt), ∀ (T : ProtoTile), ∀ (U : ProtoTile), (∀ j
        : Fin 4,
          LatticeVertexIncidentCell x j ∈ T.cells ∨
            LatticeVertexIncidentCell x j ∈ U.cells) ↔
        (∀ j : Fin 4,
          LatticeVertexIncidentCell
              (BandPackingSymmetryVectorAction g x) j ∈
                (BandPackingSymmetryTileAction g T).cells ∨
            LatticeVertexIncidentCell
              (BandPackingSymmetryVectorAction g x) j ∈
                (BandPackingSymmetryTileAction g U).cells)) ∧
    ∀ (g : BandPackingSymmetry), ∀ (q : Fin 4 -> CircleCoordinates), (ProperBandQuadruple q) → (∀
        (i : Fin 3), ∀ (s : Fin 4), ∀ (delta : Bool), (BandPackingSymmetryScopedPhase g q delta)
        → (∀ (T : ProtoTile), ∀ (x : GaussianInt),
    let q' := BandPackingSymmetryQuadrupleAction g q
      let sigma : Fin 3 -> Fin 3 := fun j =>
        if BandPackingSymmetryReversesOrientation g then -j else j
      let s' : Fin 4 :=
        if BandPackingSymmetryReversesOrientation g then
          -s - 1 + (if delta then 2 else 0)
        else s + (if delta then 2 else 0)
      let oldRight := TileTranslation T
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (if Even s.val then BandVectors.1 (q 0) (q i.succ)
            else BandVectors.1 (q i.succ) (q 0)))
      let newRight := TileTranslation (BandPackingSymmetryTileAction g T)
        ((⟨0, 1⟩ : GaussianInt) ^ s'.val *
          (if Even s'.val then BandVectors.1 (q' 0) (q' (sigma i).succ)
            else BandVectors.1 (q' (sigma i).succ) (q' 0)))
      BandPackingSymmetryTileAction g oldRight = newRight ∧
        (x ∈ FootprintVertices oldRight ↔
          BandPackingSymmetryVectorAction g x ∈ FootprintVertices newRight))) := by
-- BODY
  classical
  have negCellMap (x : GaussianInt) (j : Fin 4) := MarkedCovarianceGeometry.negCellMap x j
  have negStar (x : GaussianInt) (T U : ProtoTile) := MarkedCovarianceGeometry.negStar negCellMap
      x T U
  have conjugateCellMap (x : GaussianInt) (j : Fin 4) :=
      MarkedCovarianceGeometry.conjugateCellMap x j
  have conjugateCells (T : ProtoTile) := MarkedCovarianceGeometry.conjugateCells T
  have conjugateStar (x : GaussianInt) (T U : ProtoTile) :=
      MarkedCovarianceGeometry.conjugateStar conjugateCellMap conjugateCells x T U
  have starCov := MarkedCovarianceGeometry.starCov negStar conjugateStar
  have partialValueCov := MarkedCovarianceGeometry.partialValueCov
  have differenceTransport := P5625T1CentroidSlopeDifferenceCovariance.2
  have affineFacts := MarkedCovarianceGeometry.affineFacts
  have affineFirst := MarkedCovarianceGeometry.affineFirst
  have circleCurvature := MarkedCovarianceGeometry.circleCurvature
  have positiveSupport := MarkedCovarianceGeometry.positiveSupport
  have forwardSub := MarkedCovarianceAssembly.forwardSub partialValueCov differenceTransport
      affineFacts affineFirst circleCurvature positiveSupport
  have finiteCompanion := MarkedCovarianceGeometry.finiteCompanion
  have allNeg := MarkedCovarianceGeometry.allNeg
  have allQuarter := MarkedCovarianceGeometry.allQuarter allNeg
  refine ⟨?_, ?_, ?_⟩
  · intro g C C' T T' h h'
    constructor
    · exact forwardSub g C C' T T' h h'
    · intro hsub'
      rcases (BandPackingSymmetryInversePhaseCancellation).2 g with
        ⟨inv, hcl, _, _, _, htl, _, _, _, hpl, _, _⟩
      have hback := forwardSub inv
        (BandPackingSymmetryCircleAction g C)
        (BandPackingSymmetryCircleAction g C')
        (BandPackingSymmetryTileAction g T)
        (BandPackingSymmetryTileAction g T')
        (BandPackingSymmetryPartialOdometerAction g h)
        (BandPackingSymmetryPartialOdometerAction g h') hsub'
      simpa only [hcl, htl, hpl] using hback
  · intro g x T U
    exact starCov g x T U
  · intro g q hq i s delta hdelta T x
    dsimp
    let q' := BandPackingSymmetryQuadrupleAction g q
    let sigma : Fin 3 → Fin 3 := fun j =>
      if BandPackingSymmetryReversesOrientation g then -j else j
    let s' : Fin 4 := if BandPackingSymmetryReversesOrientation g then
      -s - 1 + (if delta then 2 else 0) else s + (if delta then 2 else 0)
    let a := BandVectors.1 (q i.succ) (q 0)
    let b := BandVectors.1 (q 0) (q i.succ)
    let a' := BandVectors.1 (q' (sigma i).succ) (q' 0)
    let b' := BandVectors.1 (q' 0) (q' (sigma i).succ)
    let d := (⟨0, 1⟩ : GaussianInt)^s.val * (if Even s.val then b else a)
    let d' := (⟨0, 1⟩ : GaussianInt)^s'.val *
      (if Even s'.val then b' else a')
    let oldRight := TileTranslation T d
    let newRight := TileTranslation (BandPackingSymmetryTileAction g T) d'
    have hproper' : ProperBandQuadruple q' :=
      BandPackingSymmetryProperCovariance g q hq
    have hflip := (VectorRecursionLaws q hq.1).2.2.2.2 hq i
    have hflip' := (VectorRecursionLaws q' hproper'.1).2.2.2.2 hproper' (sigma i)
    have qmul (z : GaussianInt) := MarkedCovarianceGeometry.qmul z
    have hflipA := MarkedCovarianceGeometry.hflipA q i hflip qmul
    have hflipB := MarkedCovarianceGeometry.hflipB g q i hflip' qmul
    have hphase := MarkedCovarianceGeometry.hphase g q i delta hdelta
    have linNeg := MarkedCovarianceGeometry.linNeg allNeg g
    have linQuarter := MarkedCovarianceGeometry.linQuarter allQuarter g
    have hdisp := MarkedCovarianceGeometry.hdisp g s delta finiteCompanion q i hflipA hflipB
        hphase linNeg linQuarter
    rcases BandPackingSymmetryTilingTransport g with
      ⟨_, _, _, _, _, _, htranslation, hfootprint, _, _, _⟩
    have htile := MarkedCovarianceGeometry.htile g q i s delta T hdisp htranslation
    refine ⟨htile, ?_⟩
    have hinj := MarkedCovarianceGeometry.hinjAt948 g
    have hfoot : FootprintVertices newRight =
        BandPackingSymmetryVectorAction g '' FootprintVertices oldRight :=
            MarkedCovarianceGeometry.hfoot g q i s delta T hfootprint htile
    rw [hfoot]
    change x ∈ FootprintVertices oldRight ↔
      BandPackingSymmetryVectorAction g x ∈
        BandPackingSymmetryVectorAction g '' FootprintVertices oldRight
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, he⟩
      have hxy : y = x := hinj he
      simpa [hxy] using hy

end ApollonianSuperharmonic

end
