/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetry
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryProjectiveVectorCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryProperCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryScopedPhase
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCircleAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryQuadrupleAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryReversesOrientation
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryVectorAction
public import LeanPool.ApollonianSuperharmonic.BandPrototile
public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrence
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileReflectionFormulas

-- [TABLET NODE: BandPackingSymmetryCovariance]

/-!
# BandPackingSymmetryCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SymmetryCovarianceProof

private theorem rsub :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        ∀ (h : BandPackingSymmetry), ∀ (p : ℝ × ℝ), ∀ (t : ℝ × ℝ), R h (p - t) = R h p - R h t )
            := by
  classical
  intro R h p t
  induction h generalizing p t with
  | identity => rfl
  | negate => ext <;> simp [R]; ring
  | conjugate => ext <;> simp [R]; ring
  | shift w => rfl
  | comp h k ih ik => simp [R, ih, ik]

private theorem rsmul :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        ∀ (h : BandPackingSymmetry), ∀ (c : ℝ), ∀ (p : ℝ × ℝ), R h (c • p) = c • R h p ) := by
  classical
  intro R h c p
  induction h generalizing p with
  | identity => rfl
  | negate => ext <;> simp [R]
  | conjugate => ext <;> simp [R]
  | shift w => rfl
  | comp h k ih ik => simp [R, ih, ik]

private theorem rneg :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        (∀ (h : BandPackingSymmetry), ∀ (c : Real), ∀ (p : Real × Real), R h (c • p) = c • R h p)
            → (∀ (h : BandPackingSymmetry), ∀ (p : ℝ × ℝ), R h (-p) = -R h p) ) := by
  classical
  intro R rsmul h p
  simpa using rsmul h (-1) p

private theorem rpoint :
    (by
      classical
      exact
        let L := BandPackingSymmetryVectorAction
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        ∀ (h : BandPackingSymmetry), ∀ (w : GaussianInt), R h (GaussianRealPoint w) =
            GaussianRealPoint (L h w) ) := by
  classical
  intro L R h w
  induction h generalizing w with
  | identity => rfl
  | negate => simp [R, L, BandPackingSymmetryVectorAction,
      GaussianRealPoint, GaussianQuarterTurn]
  | conjugate => simp [R, L, BandPackingSymmetryVectorAction,
      GaussianRealPoint, GaussianReflection]
  | shift w => rfl
  | comp h k ih ik => simp [R, L, BandPackingSymmetryVectorAction, ih, ik]

private theorem rminusq :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        (∀ (h : BandPackingSymmetry), ∀ (p : Real × Real), R h (-p) = -R h p) → (∀ (h :
            BandPackingSymmetry), ∀ (p : ℝ × ℝ), R h (p.2, -p.1) = -R h (-p.2, p.1)) ) := by
  classical
  intro R rneg h p
  rw [show (p.2, -p.1) = -(-p.2, p.1) by simp, rneg]

private theorem rq :
    (by
      classical
      exact
        let O := BandPackingSymmetryReversesOrientation
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        (∀ (h : BandPackingSymmetry), ∀ (p : Real × Real), R h (p.2, -p.1) = -R h (-p.2, p.1)) →
            (∀ (h : BandPackingSymmetry), ∀ (p : ℝ × ℝ), R h (-p.2, p.1) = if O h = true then
            -(-(R h p).2, (R h p).1) else (-(R h p).2, (R h p).1)) ) := by
  classical
  intro O R rminusq h p
  induction h generalizing p with
  | identity => rfl
  | negate => simp [R, O, BandPackingSymmetryReversesOrientation]
  | conjugate => simp [R, O, BandPackingSymmetryReversesOrientation]
  | shift w => rfl
  | comp h k ih ik =>
      change R h (R k (-p.2, p.1)) =
        if xor (O h) (O k) then -(-(R h (R k p)).2, (R h (R k p)).1)
        else (-(R h (R k p)).2, (R h (R k p)).1)
      rw [ik]
      cases hh : O h <;> cases hk : O k <;> simp [hh, rminusq, ih]

private theorem rd :
    (by
      classical
      exact
        let L := BandPackingSymmetryVectorAction
        let O := BandPackingSymmetryReversesOrientation
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        let D : GaussianInt → Real × Real := fun w =>
          (1 / 2 : Real) • (GaussianRealPoint w -
            (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))
        (∀ (h : BandPackingSymmetry), ∀ (p : Real × Real), ∀ (t : Real × Real), R h (p - t) = R h
            p - R h t) → ((∀ (h : BandPackingSymmetry), ∀ (c : Real), ∀ (p : Real × Real), R h (c
            • p) = c • R h p) → ((∀ (h : BandPackingSymmetry), ∀ (w : GaussianInt), R h
            (GaussianRealPoint w) = GaussianRealPoint (L h w)) → ((∀ (h : BandPackingSymmetry), ∀
            (p : Real × Real), R h (-p.2, p.1) = if O h then -(-(R h p).2, (R h p).1) else (-(R h
            p).2, (R h p).1)) → (∀ (h : BandPackingSymmetry), ∀ (w : GaussianInt), R h (D w) = D
            (if O h = true then GaussianQuarterTurn (L h w) else L h w))))) ) := by
  classical
  intro L O R D rsub rsmul rpoint rq h w
  dsimp [D]
  rw [rsmul, rsub, rq, rpoint]
  cases hh : O h <;> ext <;>
    simp [GaussianRealPoint, GaussianQuarterTurn] <;> ring

private theorem dsign :
    (by
      classical
      exact
        let D : GaussianInt → Real × Real := fun w =>
          (1 / 2 : Real) • (GaussianRealPoint w -
            (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))
        ∀ (d : Bool), ∀ (w : GaussianInt), D ((if d = true then (-1 : GaussianInt) else (1 :
            GaussianInt)) * w) = (if d = true then (-1 : ℝ) else (1 : ℝ)) • D w ) := by
  classical
  intro D d w
  cases d <;> ext <;> simp [D, GaussianRealPoint] <;> ring

private theorem grids :
    (by
      classical
      exact
        let B := BandPackingSymmetryTileAction
        let L := BandPackingSymmetryVectorAction
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        ∀ (h : BandPackingSymmetry), ∃ (b : GaussianInt → GaussianInt), ∀ (T : ProtoTile), (B h
            T).cells = Finset.image b T.cells ∧ (B h T).anchor = L h T.anchor ∧ FootprintVertices
            (B h T) = L h '' FootprintVertices T ∧ TileCentroid (B h T) = R h (TileCentroid T) )
            := by
  classical
  intro B L R h
  induction h with
  | identity =>
      refine ⟨id, fun T => ?_⟩
      simp [B, L, R, BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction]
  | negate =>
      refine ⟨fun x => GaussianQuarterTurn x - 1, fun T => ?_⟩
      have ht := TileQuarterTurnFormulas T
      exact ⟨ht.1, ht.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.1⟩
  | conjugate =>
      refine ⟨fun x => GaussianQuarterTurn
        (GaussianQuarterTurn (GaussianReflection x - ⟨0, 1⟩) - 1) - 1,
        fun T => ?_⟩
      have hr := TileReflectionFormulas T
      have hq := TileQuarterTurnFormulas (TileReflection T)
      have hqq := TileQuarterTurnFormulas (TileQuarterTurn (TileReflection T))
      change _ = _ ∧ _ = _ ∧ _ = _ ∧ _ = _
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [B, BandPackingSymmetryTileAction, hqq.1, hq.1, hr.1,
          Finset.image_image, Function.comp_def]
      · ext <;> simp [B, L, BandPackingSymmetryTileAction,
          BandPackingSymmetryVectorAction, TileQuarterTurn, TileReflection,
          GaussianQuarterTurn, GaussianReflection]
      · simp only [B, BandPackingSymmetryTileAction,
          hqq.2.2.2.2.2.1, hq.2.2.2.2.2.1, hr.2.2.2.2.2.1, Set.image_image]
        congr 1
      · simp [B, R, BandPackingSymmetryTileAction,
          hqq.2.2.2.2.1, hq.2.2.2.2.1, hr.2.2.2.2.1]
  | shift w =>
      refine ⟨id, fun T => ?_⟩
      simp [B, L, R, BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction]
  | comp h k ih ik =>
      obtain ⟨b, hb⟩ := ih
      obtain ⟨c, hc⟩ := ik
      refine ⟨b ∘ c, fun T => ?_⟩
      have ht := hb (B k T)
      have kt := hc T
      simp [B, L, R, BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction,
        ht.1, ht.2.1, ht.2.2.1, ht.2.2.2, kt.1, kt.2.1, kt.2.2.1, kt.2.2.2,
        Finset.image_image, Set.image_image]

private theorem sigmaInv :
    (by
      classical
      exact
        let O := BandPackingSymmetryReversesOrientation
        let sigma (h : BandPackingSymmetry) (i : Fin 3) : Fin 3 :=
          if O h then -i else i
        ∀ (h : BandPackingSymmetry), ∀ (i : Fin (3 : ℕ)), sigma h (sigma h i) = i ) := by
  classical
  intro O sigma h i
  cases hh : O h <;> simp [sigma, hh]

private theorem parent :
    (by
      classical
      exact
        let A := BandPackingSymmetryCircleAction
        let O := BandPackingSymmetryReversesOrientation
        let Q := BandPackingSymmetryQuadrupleAction
        let sigma (h : BandPackingSymmetry) (i : Fin 3) : Fin 3 :=
          if O h then -i else i
        ∀ (h : BandPackingSymmetry), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 :
            ℕ)), Q h q (sigma h i).succ = A h (q i.succ) ) := by
  classical
  intro A O Q sigma h q i
  have neg1 : -(1 : Fin 3) = 2 := rfl
  have neg2 : -(2 : Fin 3) = 1 := rfl
  cases hh : O h <;> fin_cases i <;>
    simp [Q, sigma, A, O, BandPackingSymmetryQuadrupleAction, hh, neg1, neg2]

private theorem transport :
    (by
      classical
      exact
        let A := BandPackingSymmetryCircleAction
        let B := BandPackingSymmetryTileAction
        let L := BandPackingSymmetryVectorAction
        let O := BandPackingSymmetryReversesOrientation
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        let D : GaussianInt → Real × Real := fun w =>
          (1 / 2 : Real) • (GaussianRealPoint w -
            (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))
        (∀ (h : BandPackingSymmetry), ∀ (p : Real × Real), ∀ (t : Real × Real), R h (p - t) = R h
            p - R h t) → ((∀ (h : BandPackingSymmetry), ∀ (c : Real), ∀ (p : Real × Real), R h (c
            • p) = c • R h p) → ((∀ (h : BandPackingSymmetry), ∀ (w : GaussianInt), R h (D w) = D
            (if O h then GaussianQuarterTurn (L h w) else L h w)) → ((∀ (d : Bool), ∀ (w :
            GaussianInt), D ((if d then (-1 : GaussianInt) else 1) * w) = (if d then (-1 : Real)
            else 1) • D w) → ((∀ (h : BandPackingSymmetry), ∃ b : GaussianInt → GaussianInt, ∀ T
            : ProtoTile, (B h T).cells = T.cells.image b ∧ (B h T).anchor = L h T.anchor ∧
            FootprintVertices (B h T) = L h '' FootprintVertices T ∧ TileCentroid (B h T) = R h
            (TileCentroid T)) → (
        let Q := BandPackingSymmetryQuadrupleAction
        let sigma (h : BandPackingSymmetry) (i : Fin 3) : Fin 3 :=
          if O h then -i else i
        (∀ (h : BandPackingSymmetry), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), Q h q
            (sigma h i).succ = A h (q i.succ)) → (∀ (h : BandPackingSymmetry), ∀ (q : Fin (4 : ℕ)
            → CircleCoordinates), ∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (d : Bool), ∀ (i : Fin
            (3 : ℕ)), ∀ (s : Bool), BandPackingSymmetryScopedPhase h q d → BandPrototile (A h (q
            i.succ)) (B h U) → FootprintVertices U ⊆ FootprintVertices T → TileCentroid U -
            TileCentroid T = (if s = true then (1 : ℝ) else (-1 : ℝ)) • D (BandVectors.1 (q (i +
            (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)) → BandSubtileOccurrence (Q
            h q) (B h T) (sigma h i) (s ^^ d) (B h U))))))) ) := by
  classical
  intro A B L O R D rsub rsmul rd dsign grids Q sigma parent h q T U d i s hd hp hf hc
  obtain ⟨b, hb⟩ := grids h
  refine ⟨?_, ?_, ?_⟩
  · rw [parent]
    exact hp
  · rw [(hb U).2.2.1, (hb T).2.2.1]
    exact Set.image_mono hf
  · change TileCentroid (B h U) - TileCentroid (B h T) =
      (if xor s d = true then (1 : Real) else -1) •
        D (BandVectors.1 (Q h q ((sigma h i + 2).succ))
          (Q h q ((sigma h i + 1).succ)))
    rw [(hb U).2.2.2, (hb T).2.2.2, ← rsub, hc, rsmul, rd,
      (hd i).2.2, dsign]
    cases s <;> cases d <;> simp [L, O]

private theorem families :
    (by
      classical
      exact
        let A := BandPackingSymmetryCircleAction
        let B := BandPackingSymmetryTileAction
        let L := BandPackingSymmetryVectorAction
        let O := BandPackingSymmetryReversesOrientation
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        let D : GaussianInt → Real × Real := fun w =>
          (1 / 2 : Real) • (GaussianRealPoint w -
            (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))
        (∀ (h : BandPackingSymmetry), ∃ b : GaussianInt → GaussianInt, ∀ T : ProtoTile, (B h
            T).cells = T.cells.image b ∧ (B h T).anchor = L h T.anchor ∧ FootprintVertices (B h
            T) = L h '' FootprintVertices T ∧ TileCentroid (B h T) = R h (TileCentroid T)) → (
        let Q := BandPackingSymmetryQuadrupleAction
        let sigma (h : BandPackingSymmetry) (i : Fin 3) : Fin 3 :=
          if O h then -i else i
        (∀ (h : BandPackingSymmetry), ∀ (i : Fin 3), sigma h (sigma h i) = i) → ((∀ (h :
            BandPackingSymmetry), ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (U :
            ProtoTile), ∀ (d : Bool), ∀ (i : Fin 3), ∀ (s : Bool),
            (BandPackingSymmetryScopedPhase h q d) → ((BandPrototile (A h (q i.succ)) (B h U)) →
            ((FootprintVertices U ⊆ FootprintVertices T) → ((TileCentroid U - TileCentroid T =
            (if s = true then (1 : Real) else -1) • D (BandVectors.1 (q ((i + 2).succ)) (q ((i +
            1).succ)))) → (BandSubtileOccurrence (Q h q) (B h T) (sigma h i) (xor s d) (B h
            U)))))) → (∀ (h : BandPackingSymmetry), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (T
            : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ProperBandQuadruple q → (∀ (i :
            Fin (3 : ℕ)), ∀ (s : Bool), BandPrototile (A h (q i.succ)) (B h (S i s))) → (∀ (i :
            Fin (3 : ℕ)), ∀ (s : Bool), FootprintVertices (S i s) ⊆ FootprintVertices T) → (∀ (i
            : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (S i s) - TileCentroid T = (if s = true
            then (1 : ℝ) else (-1 : ℝ)) • D (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i
            + (1 : Fin (3 : ℕ))).succ))) → (∀ (x : LatticeCell), x ∈ T.cells ↔ ∃ (i : Fin (3 :
            ℕ)) (s : Bool), x ∈ (S i s).cells) → ∃ (d : Bool) (e : Fin (3 : ℕ) × Bool ≃ Fin (3 :
            ℕ) × Bool) (S' : Fin (3 : ℕ) → Bool → ProtoTile), BandPackingSymmetryScopedPhase h q
            d ∧ (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), (e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool)
            (i, s) = (sigma h i, s ^^ d)) ∧ (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), S' ((e : Fin (3 :
            ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)).1 ((e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) ×
            Bool) (i, s)).2 = B h (S i s)) ∧ (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            BandSubtileOccurrence (Q h q) (B h T) i s (S' i s)) ∧ ∀ (x : LatticeCell), x ∈ (B h
            T).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S' i s).cells))) ) := by
  classical
  intro A B L O R D grids Q sigma sigmaInv transport h q T S hq hp hf hc hu
  obtain ⟨d, hd, _⟩ := BandPackingSymmetryProjectiveVectorCovariance h q hq
  have labelInv : Function.Involutive (fun p : Fin 3 × Bool =>
      (sigma h p.1, xor p.2 d)) := by
    rintro ⟨i, s⟩
    change (sigma h (sigma h i), xor (xor s d) d) = (i, s)
    rw [sigmaInv]
    cases s <;> cases d <;> rfl
  let e : (Fin 3 × Bool) ≃ (Fin 3 × Bool) :=
    { toFun := fun p => (sigma h p.1, xor p.2 d)
      invFun := fun p => (sigma h p.1, xor p.2 d)
      left_inv := labelInv
      right_inv := labelInv }
  let S' : Fin 3 → Bool → ProtoTile := fun j u =>
    B h (S (e.symm (j, u)).1 (e.symm (j, u)).2)
  have he (i : Fin 3) (s : Bool) : e (i, s) = (sigma h i, xor s d) := rfl
  have hs (i : Fin 3) (s : Bool) :
      S' (e (i, s)).1 (e (i, s)).2 = B h (S i s) := by
    change B h (S (e.symm (e (i, s))).1 (e.symm (e (i, s))).2) = _
    rw [e.symm_apply_apply]
  refine ⟨d, e, S', hd, he, hs, ?_, ?_⟩
  · intro j u
    obtain ⟨⟨i, s⟩, hij⟩ := e.surjective (j, u)
    have ht := transport h q T (S i s) d i s hd (hp i s) (hf i s) (hc i s)
    change BandSubtileOccurrence (Q h q) (B h T)
      (e (i, s)).1 (e (i, s)).2 (B h (S i s)) at ht
    rw [← hs i s, hij] at ht
    exact ht
  · obtain ⟨b, hb⟩ := grids h
    have unionImage (x : GaussianInt) :
        x ∈ (B h T).cells ↔ ∃ i s, x ∈ (B h (S i s)).cells := by
      rw [(hb T).1]
      constructor
      · rintro hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨i, s, hy⟩ := (hu y).mp hy
        refine ⟨i, s, ?_⟩
        rw [(hb (S i s)).1]
        exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
      · rintro ⟨i, s, hx⟩
        rw [(hb (S i s)).1] at hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_image.mpr ⟨y, (hu y).mpr ⟨i, s, hy⟩, rfl⟩
    intro x
    rw [unionImage]
    constructor
    · rintro ⟨i, s, hx⟩
      exact ⟨(e (i, s)).1, (e (i, s)).2, by rw [hs]; exact hx⟩
    · rintro ⟨j, u, hx⟩
      obtain ⟨⟨i, s⟩, hij⟩ := e.surjective (j, u)
      refine ⟨i, s, ?_⟩
      rw [← hs i s, hij]
      exact hx

private theorem lineAction :
    (by
      classical
      exact
        let A := BandPackingSymmetryCircleAction
        ∀ (h : BandPackingSymmetry), ∀ (w : GaussianInt), w = (1 : GaussianInt) ∨ w = (-1 :
            GaussianInt) → ∃ (w' : GaussianInt), (w' = (1 : GaussianInt) ∨ w' = (-1 :
            GaussianInt)) ∧ A h ((0 : ℤ), w) = ((0 : ℤ), w') ) := by
  classical
  intro A h w hw
  induction h generalizing w with
  | identity => exact ⟨w, hw, rfl⟩
  | negate =>
      refine ⟨-w, ?_, rfl⟩
      rcases hw with rfl | rfl <;> simp
  | conjugate =>
      refine ⟨GaussianReflection w, ?_, rfl⟩
      rcases hw with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  | shift z =>
      exact ⟨w, hw, by simp [A, BandPackingSymmetryCircleAction]⟩
  | comp h k ih ik =>
      obtain ⟨w', hw', hk⟩ := ik w hw
      obtain ⟨w'', hw'', hh⟩ := ih w' hw'
      exact ⟨w'', hw'', by simpa [A, BandPackingSymmetryCircleAction, hk] using hh⟩

private theorem unitAction :
    (by
      classical
      exact
        let A := BandPackingSymmetryCircleAction
        ∀ (h : BandPackingSymmetry), ∀ (z : GaussianInt), ∃ (z' : GaussianInt), A h ((1 : ℤ), (1
            : GaussianInt) + (2 : GaussianInt) * z) = ((1 : ℤ), (1 : GaussianInt) + (2 :
            GaussianInt) * z') ) := by
  classical
  intro A h z
  induction h generalizing z with
  | identity => exact ⟨z, rfl⟩
  | negate =>
      refine ⟨-1-z, ?_⟩
      apply Prod.ext
      · rfl
      · change -(1 + 2 * z) = 1 + 2 * (-1-z)
        ring
  | conjugate =>
      refine ⟨GaussianReflection z, ?_⟩
      apply Prod.ext
      · rfl
      · ext <;> simp [A, BandPackingSymmetryCircleAction, GaussianReflection]
  | shift w =>
      refine ⟨z+w, ?_⟩
      apply Prod.ext
      · rfl
      · change 1 + 2 * z + 2 * (1 : GaussianInt) * w = 1 + 2 * (z+w)
        ring
  | comp h k ih ik =>
      obtain ⟨z', hk⟩ := ik z
      obtain ⟨z'', hh⟩ := ih z'
      exact ⟨z'', by simpa [A, BandPackingSymmetryCircleAction, hk] using hh⟩

private theorem tileExt :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (U : ProtoTile), T.cells = U.cells → T.anchor = U.anchor → T = U )
            := by
  classical
  intro T U hc ha
  cases T
  cases U
  congr

private theorem forward :
    (by
      classical
      exact
        let A := BandPackingSymmetryCircleAction
        let B := BandPackingSymmetryTileAction
        let L := BandPackingSymmetryVectorAction
        let O := BandPackingSymmetryReversesOrientation
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        let D : GaussianInt → Real × Real := fun w =>
          (1 / 2 : Real) • (GaussianRealPoint w -
            (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))
        (∀ (h : BandPackingSymmetry), ∃ b : GaussianInt → GaussianInt, ∀ T : ProtoTile, (B h
            T).cells = T.cells.image b ∧ (B h T).anchor = L h T.anchor ∧ FootprintVertices (B h
            T) = L h '' FootprintVertices T ∧ TileCentroid (B h T) = R h (TileCentroid T)) → (
        let Q := BandPackingSymmetryQuadrupleAction
        let sigma (h : BandPackingSymmetry) (i : Fin 3) : Fin 3 :=
          if O h then -i else i
        (∀ (h : BandPackingSymmetry), ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (S
            : Fin 3 → Bool → ProtoTile), (ProperBandQuadruple q) → ((∀ i, ∀ s, BandPrototile (A h
            (q i.succ)) (B h (S i s))) → ((∀ i, ∀ s, FootprintVertices (S i s) ⊆
            FootprintVertices T) → ((∀ i, ∀ s, TileCentroid (S i s) - TileCentroid T = (if s =
            true then (1 : Real) else -1) • D (BandVectors.1 (q ((i + 2).succ)) (q ((i +
            1).succ)))) → ((∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (S i s).cells) → (∃ (d : Bool) (e :
            (Fin 3 × Bool) ≃ (Fin 3 × Bool)) (S' : Fin 3 → Bool → ProtoTile),
            BandPackingSymmetryScopedPhase h q d ∧ (∀ i, ∀ s, e (i, s) = (sigma h i, xor s d)) ∧
            (∀ i, ∀ s, S' (e (i, s)).1 (e (i, s)).2 = B h (S i s)) ∧ (∀ i, ∀ s,
            BandSubtileOccurrence (Q h q) (B h T) i s (S' i s)) ∧ ∀ x, x ∈ (B h T).cells ↔ ∃ i s,
            x ∈ (S' i s).cells)))))) → ((∀ (h : BandPackingSymmetry), ∀ (w : GaussianInt), (w = 1
            ∨ w = -1) → (∃ w', (w' = 1 ∨ w' = -1) ∧ A h (0, w) = (0, w'))) → ((∀ (h :
            BandPackingSymmetry), ∀ (z : GaussianInt), ∃ z', A h (1, 1 + 2 * z) = (1, 1 + 2 *
            z')) → ((∀ (T : ProtoTile), ∀ (U : ProtoTile), (T.cells = U.cells) → ((T.anchor =
            U.anchor) → (T = U))) → (∀ (C : CircleCoordinates), ∀ (T : ProtoTile), BandPrototile
            C T → ∀ (h : BandPackingSymmetry), BandPrototile (A h C) (B h T)))))) ) := by
  classical
  intro A B L O R D grids Q sigma families lineAction unitAction tileExt C T ht
  induction ht with
  | line w x hw =>
      intro h
      obtain ⟨w', hw', ha⟩ := lineAction h w hw
      obtain ⟨b, hb⟩ := grids h
      have ht : B h ⟨∅, x⟩ = ⟨∅, L h x⟩ :=
        tileExt _ _ (by simpa using (hb ⟨∅, x⟩).1) (hb ⟨∅, x⟩).2.1
      rw [ha, ht]
      exact BandPrototile.line w' (L h x) hw'
  | unit z x anchor =>
      intro h
      obtain ⟨z', ha⟩ := unitAction h z
      obtain ⟨b, hb⟩ := grids h
      have ht : B h ⟨{x}, anchor⟩ = ⟨{b x}, L h anchor⟩ :=
        tileExt _ _ (by simpa using (hb ⟨{x}, anchor⟩).1)
          (hb ⟨{x}, anchor⟩).2.1
      rw [ha, ht]
      exact BandPrototile.unit z' (b x) (L h anchor)
  | @decompose q hq S T hS hu hf hc ih =>
      intro h
      obtain ⟨d, e, S', hd, he, hs, ho, hu'⟩ :=
        families h q T S hq (fun i s => ih i s h) hf hc hu
      change BandPrototile (Q h q 0) (B h T)
      exact BandPrototile.decompose (BandPackingSymmetryProperCovariance h q hq)
        (fun i s => (ho i s).1) hu' (fun i s => (ho i s).2.1)
        (fun i s => (ho i s).2.2)

private theorem tileN :
    (by
      classical
      exact
        ∀ (T : ProtoTile), TileQuarterTurn (TileQuarterTurn (TileQuarterTurn (TileQuarterTurn
            T))) = T ) := by
  classical
  intro T
  cases T with
  | mk cells anchor =>
      apply congrArg₂ ProtoTile.mk
      · simp only [TileQuarterTurn, Finset.image_image, Function.comp_def]
        have hm : (fun x : GaussianInt => GaussianQuarterTurn
            (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn x - 1) - 1) - 1)
              - 1) = id := by
          funext x
          ext <;> simp [GaussianQuarterTurn]
        rw [hm, Finset.image_id]
      · ext <;> simp [TileQuarterTurn, GaussianQuarterTurn]

private theorem tileK :
    (by
      classical
      exact
        let B := BandPackingSymmetryTileAction
        ∀ (T : ProtoTile), B BandPackingSymmetry.conjugate (B BandPackingSymmetry.conjugate T) =
            T ) := by
  classical
  intro B T
  cases T with
  | mk cells anchor =>
      apply congrArg₂ ProtoTile.mk
      · simp only [B, BandPackingSymmetryTileAction, TileQuarterTurn, TileReflection,
          Finset.image_image, Function.comp_def]
        have hm : (fun x : GaussianInt => GaussianQuarterTurn
            (GaussianQuarterTurn (GaussianReflection (GaussianQuarterTurn
              (GaussianQuarterTurn (GaussianReflection x - ⟨0, 1⟩) - 1) - 1) -
                ⟨0, 1⟩) - 1) - 1) = id := by
          funext x
          ext <;> simp [GaussianQuarterTurn, GaussianReflection]
        rw [hm, Finset.image_id]
      · ext <;> simp [B, BandPackingSymmetryTileAction, TileQuarterTurn,
          TileReflection, GaussianQuarterTurn, GaussianReflection]

private theorem inverse :
    (by
      classical
      exact
        let A := BandPackingSymmetryCircleAction
        let B := BandPackingSymmetryTileAction
        (∀ (T : ProtoTile), TileQuarterTurn (TileQuarterTurn (TileQuarterTurn (TileQuarterTurn
            T))) = T) → ((∀ (T : ProtoTile), B .conjugate (B .conjugate T) = T) → (∀ (h :
            BandPackingSymmetry), ∃ (k : BandPackingSymmetry), (∀ (C : CircleCoordinates), A k (A
            h C) = C) ∧ ∀ (T : ProtoTile), B k (B h T) = T)) ) := by
  classical
  intro A B tileN tileK h
  induction h with
  | identity => exact ⟨.identity, fun _ => rfl, fun _ => rfl⟩
  | negate =>
      refine ⟨.comp .negate (.comp .negate .negate), ?_, tileN⟩
      intro C
      cases C
      simp [A, BandPackingSymmetryCircleAction]
  | conjugate =>
      refine ⟨.conjugate, ?_, tileK⟩
      intro C
      cases C
      apply Prod.ext
      · rfl
      · ext <;> simp [A, BandPackingSymmetryCircleAction, GaussianReflection]
  | shift w =>
      refine ⟨.shift (-w), ?_, fun _ => rfl⟩
      intro C
      cases C
      apply Prod.ext
      · rfl
      · simp only [A, BandPackingSymmetryCircleAction]
        ring
  | comp h k ih ik =>
      obtain ⟨hi, hc, ht⟩ := ih
      obtain ⟨ki, kc, kt⟩ := ik
      refine ⟨.comp ki hi, ?_, ?_⟩
      · intro C
        simp only [A, BandPackingSymmetryCircleAction, hc, kc]
      · intro T
        simp only [B, BandPackingSymmetryTileAction, ht, kt]

private theorem covariance :
    (by
      classical
      exact
        let A := BandPackingSymmetryCircleAction
        let B := BandPackingSymmetryTileAction
        (∀ (C : CircleCoordinates), ∀ (T : ProtoTile), (BandPrototile C T) → (∀ h :
            BandPackingSymmetry, BandPrototile (A h C) (B h T))) → ((∀ (h : BandPackingSymmetry),
            ∃ k : BandPackingSymmetry, (∀ C, A k (A h C) = C) ∧ (∀ T, B k (B h T) = T)) → (∀ (h :
            BandPackingSymmetry), ∀ (C : CircleCoordinates), ∀ (T : ProtoTile), BandPrototile C T
            ↔ BandPrototile (A h C) (B h T))) ) := by
  classical
  intro A B forward inverse h C T
  constructor
  · intro ht
    exact forward C T ht h
  · intro ht
    obtain ⟨k, hk, ht'⟩ := inverse h
    simpa only [hk, ht'] using forward (A h C) (B h T) ht k

private theorem curvature :
    (by
      classical
      exact
        let A := BandPackingSymmetryCircleAction
        ∀ (h : BandPackingSymmetry), ∀ (C : CircleCoordinates), (A h C).1 = C.1 ) := by
  classical
  intro A h C
  induction h generalizing C with
  | identity => rfl
  | negate => rfl
  | conjugate => rfl
  | shift w => rfl
  | comp h k ih ik => simp [A, BandPackingSymmetryCircleAction, ih, ik]

end SymmetryCovarianceProof

theorem BandPackingSymmetryCovariance (g : BandPackingSymmetry) :
    (∀ C, (BandPackingSymmetryCircleAction g C).1 = C.1) ∧
    (∀ C T, BandPrototile C T ↔
      BandPrototile (BandPackingSymmetryCircleAction g C)
        (BandPackingSymmetryTileAction g T)) ∧
    ∀ (q : Fin 4 → CircleCoordinates) (T : ProtoTile)
        (S : Fin 3 → Bool → ProtoTile),
      ProperBandQuadruple q → BandPrototile (q 0) T →
      (∀ i s, BandSubtileOccurrence q T i s (S i s)) →
      (∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (S i s).cells) →
      let sigma : Fin 3 → Fin 3 := fun i =>
        if BandPackingSymmetryReversesOrientation g then -i else i
      ∃ (negative : Bool) (e : (Fin 3 × Bool) ≃ (Fin 3 × Bool))
          (S' : Fin 3 → Bool → ProtoTile),
        BandPackingSymmetryScopedPhase g q negative ∧
        (∀ i s, e (i, s) = (sigma i, xor s negative)) ∧
        (∀ i s, S' (e (i, s)).1 (e (i, s)).2 =
          BandPackingSymmetryTileAction g (S i s)) ∧
        (∀ i s, BandSubtileOccurrence
          (BandPackingSymmetryQuadrupleAction g q)
          (BandPackingSymmetryTileAction g T) i s (S' i s)) ∧
        ∀ x, x ∈ (BandPackingSymmetryTileAction g T).cells ↔
          ∃ i s, x ∈ (S' i s).cells := by
-- BODY
  classical
  let A := BandPackingSymmetryCircleAction
  let B := BandPackingSymmetryTileAction
  let L := BandPackingSymmetryVectorAction
  let O := BandPackingSymmetryReversesOrientation
  -- The real action tracks centroid and signed-offset transport.
  let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
    BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
      (fun p => (-p.1, p.2)) (fun _ p => p)
      (fun _ _ f k p => f (k p))
  let D : GaussianInt → Real × Real := fun w =>
    (1 / 2 : Real) • (GaussianRealPoint w -
      (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))
  have rsub (h : BandPackingSymmetry) (p t : Real × Real) :
      R h (p - t) = R h p - R h t := SymmetryCovarianceProof.rsub h p t
  have rsmul (h : BandPackingSymmetry) (c : Real) (p : Real × Real) :
      R h (c • p) = c • R h p := SymmetryCovarianceProof.rsmul h c p
  have rneg (h : BandPackingSymmetry) (p : Real × Real) :
      R h (-p) = -R h p := SymmetryCovarianceProof.rneg rsmul h p
  have rpoint (h : BandPackingSymmetry) (w : GaussianInt) :
      R h (GaussianRealPoint w) = GaussianRealPoint (L h w) := SymmetryCovarianceProof.rpoint h w
  have rminusq (h : BandPackingSymmetry) (p : Real × Real) :
      R h (p.2, -p.1) = -R h (-p.2, p.1) := SymmetryCovarianceProof.rminusq rneg h p
  have rq (h : BandPackingSymmetry) (p : Real × Real) :
      R h (-p.2, p.1) = if O h then
        -(-(R h p).2, (R h p).1) else (-(R h p).2, (R h p).1) := SymmetryCovarianceProof.rq
            rminusq h p
  have rd (h : BandPackingSymmetry) (w : GaussianInt) :
      R h (D w) = D (if O h then GaussianQuarterTurn (L h w) else L h w) :=
          SymmetryCovarianceProof.rd rsub rsmul rpoint rq h w
  have dsign (d : Bool) (w : GaussianInt) :
      D ((if d then (-1 : GaussianInt) else 1) * w) =
        (if d then (-1 : Real) else 1) • D w := SymmetryCovarianceProof.dsign d w
  have grids (h : BandPackingSymmetry) : ∃ b : GaussianInt → GaussianInt,
      ∀ T : ProtoTile,
        (B h T).cells = T.cells.image b ∧
        (B h T).anchor = L h T.anchor ∧
        FootprintVertices (B h T) = L h '' FootprintVertices T ∧
        TileCentroid (B h T) = R h (TileCentroid T) := SymmetryCovarianceProof.grids h
  let Q := BandPackingSymmetryQuadrupleAction
  let sigma (h : BandPackingSymmetry) (i : Fin 3) : Fin 3 :=
    if O h then -i else i
  have sigmaInv (h : BandPackingSymmetry) (i : Fin 3) :
      sigma h (sigma h i) = i := SymmetryCovarianceProof.sigmaInv h i
  have parent (h : BandPackingSymmetry) (q : Fin 4 → CircleCoordinates) (i : Fin 3) :
      Q h q (sigma h i).succ = A h (q i.succ) := SymmetryCovarianceProof.parent h q i
  have transport (h : BandPackingSymmetry) (q : Fin 4 → CircleCoordinates)
      (T U : ProtoTile) (d : Bool) (i : Fin 3) (s : Bool)
      (hd : BandPackingSymmetryScopedPhase h q d)
      (hp : BandPrototile (A h (q i.succ)) (B h U))
      (hf : FootprintVertices U ⊆ FootprintVertices T)
      (hc : TileCentroid U - TileCentroid T =
        (if s = true then (1 : Real) else -1) •
          D (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ)))) :
      BandSubtileOccurrence (Q h q) (B h T) (sigma h i) (xor s d) (B h U) :=
          SymmetryCovarianceProof.transport rsub rsmul rd dsign grids parent h q T U d i s hd hp
          hf hc
  -- Relabel all six pieces using a single phase for the proper tuple.
  have families (h : BandPackingSymmetry) (q : Fin 4 → CircleCoordinates)
      (T : ProtoTile) (S : Fin 3 → Bool → ProtoTile)
      (hq : ProperBandQuadruple q)
      (hp : ∀ i s, BandPrototile (A h (q i.succ)) (B h (S i s)))
      (hf : ∀ i s, FootprintVertices (S i s) ⊆ FootprintVertices T)
      (hc : ∀ i s, TileCentroid (S i s) - TileCentroid T =
        (if s = true then (1 : Real) else -1) •
          D (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))))
      (hu : ∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (S i s).cells) :
      ∃ (d : Bool) (e : (Fin 3 × Bool) ≃ (Fin 3 × Bool))
          (S' : Fin 3 → Bool → ProtoTile),
        BandPackingSymmetryScopedPhase h q d ∧
        (∀ i s, e (i, s) = (sigma h i, xor s d)) ∧
        (∀ i s, S' (e (i, s)).1 (e (i, s)).2 = B h (S i s)) ∧
        (∀ i s, BandSubtileOccurrence (Q h q) (B h T) i s (S' i s)) ∧
        ∀ x, x ∈ (B h T).cells ↔ ∃ i s, x ∈ (S' i s).cells := SymmetryCovarianceProof.families
            grids sigmaInv transport h q T S hq hp hf hc hu
  have lineAction (h : BandPackingSymmetry) (w : GaussianInt) (hw : w = 1 ∨ w = -1) :
      ∃ w', (w' = 1 ∨ w' = -1) ∧ A h (0, w) = (0, w') := SymmetryCovarianceProof.lineAction h w hw
  have unitAction (h : BandPackingSymmetry) (z : GaussianInt) :
      ∃ z', A h (1, 1 + 2 * z) = (1, 1 + 2 * z') := SymmetryCovarianceProof.unitAction h z
  have tileExt (T U : ProtoTile) (hc : T.cells = U.cells) (ha : T.anchor = U.anchor) :
      T = U := SymmetryCovarianceProof.tileExt T U hc ha
  -- Constructor induction uses only the immediate children's hypotheses.
  have forward (C : CircleCoordinates) (T : ProtoTile) (ht : BandPrototile C T) :
      ∀ h : BandPackingSymmetry, BandPrototile (A h C) (B h T) := SymmetryCovarianceProof.forward
          grids families lineAction unitAction tileExt C T ht
  have tileN (T : ProtoTile) :
      TileQuarterTurn (TileQuarterTurn (TileQuarterTurn (TileQuarterTurn T))) = T :=
          SymmetryCovarianceProof.tileN T
  have tileK (T : ProtoTile) : B .conjugate (B .conjugate T) = T := SymmetryCovarianceProof.tileK T
  -- Three negations undo the quarter-turn action while undoing the circle negation.
  have inverse (h : BandPackingSymmetry) : ∃ k : BandPackingSymmetry,
      (∀ C, A k (A h C) = C) ∧ (∀ T, B k (B h T) = T) := SymmetryCovarianceProof.inverse tileN
          tileK h
  have covariance (h : BandPackingSymmetry) (C : CircleCoordinates) (T : ProtoTile) :
      BandPrototile C T ↔ BandPrototile (A h C) (B h T) := SymmetryCovarianceProof.covariance
          forward inverse h C T
  have curvature (h : BandPackingSymmetry) (C : CircleCoordinates) :
      (A h C).1 = C.1 := SymmetryCovarianceProof.curvature h C
  refine ⟨curvature g, covariance g, ?_⟩
  intro q T S hq hT ho hu
  exact families g q T S hq
    (fun i s => forward _ _ (ho i s).1 g)
    (fun i s => (ho i s).2.1) (fun i s => (ho i s).2.2) hu

end ApollonianSuperharmonic

end
