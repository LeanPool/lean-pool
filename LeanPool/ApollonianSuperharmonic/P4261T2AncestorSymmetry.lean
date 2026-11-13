/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryDomainTransport

public import LeanPool.ApollonianSuperharmonic.AncestorOdometer
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileOdometerCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTilingTransport

-- [TABLET NODE: P4261T2AncestorSymmetry]

/-!
# P4261T2AncestorSymmetry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace AncestorSymmetryGeometry

private theorem hInclusion :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (k : PartialOdometer), ∀ (h : PartialOdometer), (k.domain
            ⊆ h.domain) → ((BandPackingSymmetryPartialOdometerAction g k).domain ⊆
            (BandPackingSymmetryPartialOdometerAction g h).domain) ) := by
  classical
  intro g k h hIncl
  change ((BandPackingSymmetryPartialOdometerAction g k).domain : Set GaussianInt) ⊆
    ((BandPackingSymmetryPartialOdometerAction g h).domain : Set GaussianInt)
  rw [(BandPackingSymmetryPartialOdometerActionFormulas g k h).1,
    (BandPackingSymmetryPartialOdometerActionFormulas g h k).1]
  exact Set.image_mono hIncl

private abbrev actionForward := BandPackingSymmetryDomainTransport.forward

private theorem literalRestriction :
    (by
      classical
      exact
        (∀ (a : BandPackingSymmetry), ∀ (p : PartialOdometer), ∀ (x : GaussianInt), (x ∈
            p.domain) → (BandPackingSymmetryVectorAction a x ∈
            (BandPackingSymmetryPartialOdometerAction a p).domain)) → (∀ (g :
            BandPackingSymmetry), ∀ (k : PartialOdometer), ∀ (h : PartialOdometer), (k.domain ⊆
            h.domain) → ((∀ x, x ∈ k.domain → k.value x = h.value x) → (∀ x, x ∈ k.domain →
            (BandPackingSymmetryPartialOdometerAction g k).value (BandPackingSymmetryVectorAction
            g x) = (BandPackingSymmetryPartialOdometerAction g h).value
            (BandPackingSymmetryVectorAction g x)))) ) := by
  classical
  intro actionForward g k h hsub heq
  induction g generalizing k h with
  | identity => exact heq
  | shift w =>
      intro x hx
      simp only [BandPackingSymmetryVectorAction,
        BandPackingSymmetryPartialOdometerAction, hx, hsub hx, ite_eq_left]
      rw [heq x hx]
  | negate =>
      intro x hx
      have hinv (z : GaussianInt) :
          -GaussianQuarterTurn (GaussianQuarterTurn z) = z := by
        ext <;> simp [GaussianQuarterTurn]
      simp only [BandPackingSymmetryVectorAction,
        BandPackingSymmetryPartialOdometerAction,
        Finset.mem_image_of_mem GaussianQuarterTurn hx,
        Finset.mem_image_of_mem GaussianQuarterTurn (hsub hx), ite_eq_left, hinv]
      exact heq x hx
  | conjugate =>
      intro x hx
      have hinv (z : GaussianInt) :
          -GaussianReflection (-GaussianReflection z) = z := by
        ext <;> simp [GaussianReflection]
      simp only [BandPackingSymmetryVectorAction,
        BandPackingSymmetryPartialOdometerAction,
        Finset.mem_image_of_mem (fun z => -GaussianReflection z) hx,
        Finset.mem_image_of_mem (fun z => -GaussianReflection z) (hsub hx), ite_eq_left, hinv]
      exact heq x hx
  | comp a b ia ib =>
      intro x hx
      have hbsub : (BandPackingSymmetryPartialOdometerAction b k).domain ⊆
          (BandPackingSymmetryPartialOdometerAction b h).domain := by
        intro y hy
        change y ∈ ((BandPackingSymmetryPartialOdometerAction b k).domain : Set GaussianInt) at hy
        rw [(BandPackingSymmetryPartialOdometerActionFormulas b k k).1] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        exact actionForward b h z (hsub hz)
      have hbeq : ∀ y,
          y ∈ (BandPackingSymmetryPartialOdometerAction b k).domain →
          (BandPackingSymmetryPartialOdometerAction b k).value y =
            (BandPackingSymmetryPartialOdometerAction b h).value y := by
        intro y hy
        change y ∈ ((BandPackingSymmetryPartialOdometerAction b k).domain : Set GaussianInt) at hy
        rw [(BandPackingSymmetryPartialOdometerActionFormulas b k k).1] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        exact ib k h hsub heq z hz
      exact ia (BandPackingSymmetryPartialOdometerAction b k)
        (BandPackingSymmetryPartialOdometerAction b h) hbsub hbeq _
        (actionForward b k x hx)

private theorem rsub :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p) (fun _ _ f k p => f (k p))
        ∀ (a : BandPackingSymmetry), ∀ (p : Real × Real), ∀ (t : Real × Real), R a (p - t) = R a
            p - R a t ) := by
  classical
  intro R a p t
  induction a generalizing p t with
  | identity => rfl
  | negate => ext <;> simp [R]; ring
  | conjugate => ext <;> simp [R]; ring
  | shift w => rfl
  | comp a b ia ib => simp [R, ia, ib]

private theorem rsmul :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p) (fun _ _ f k p => f (k p))
        ∀ (a : BandPackingSymmetry), ∀ (c : Real), ∀ (p : Real × Real), R a (c • p) = c • R a p )
            := by
  classical
  intro R a c p
  induction a generalizing p with
  | identity => rfl
  | negate => ext <;> simp [R]
  | conjugate => ext <;> simp [R]
  | shift w => rfl
  | comp a b ia ib => simp [R, ia, ib]

private theorem rneg :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p) (fun _ _ f k p => f (k p))
        (∀ (a : BandPackingSymmetry), ∀ (c : Real), ∀ (p : Real × Real), R a (c • p) = c • R a p)
            → (∀ (a : BandPackingSymmetry), ∀ (p : Real × Real), R a (-p) = -R a p) ) := by
  classical
  intro R rsmul a p
  simpa using rsmul a (-1) p

private theorem rminusq :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p) (fun _ _ f k p => f (k p))
        (∀ (a : BandPackingSymmetry), ∀ (p : Real × Real), R a (-p) = -R a p) → (∀ (a :
            BandPackingSymmetry), ∀ (p : Real × Real), R a (p.2, -p.1) = -R a (-p.2, p.1)) ) := by
  classical
  intro R rneg a p
  rw [show (p.2, -p.1) = -(-p.2, p.1) by simp, rneg]

private theorem rpoint :
    (by
      classical
      exact
        let L := BandPackingSymmetryVectorAction
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p) (fun _ _ f k p => f (k p))
        ∀ (a : BandPackingSymmetry), ∀ (w : GaussianInt), R a (GaussianRealPoint w) =
            GaussianRealPoint (L a w) ) := by
  classical
  intro L R a w
  induction a generalizing w with
  | identity => rfl
  | negate => simp [R, L, BandPackingSymmetryVectorAction, GaussianRealPoint,
      GaussianQuarterTurn]
  | conjugate => simp [R, L, BandPackingSymmetryVectorAction, GaussianRealPoint,
      GaussianReflection]
  | shift w => rfl
  | comp a b ia ib => simp [R, L, BandPackingSymmetryVectorAction, ia, ib]

private theorem rq :
    (by
      classical
      exact
        let O := BandPackingSymmetryReversesOrientation
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p) (fun _ _ f k p => f (k p))
        let J : (Real × Real) → (Real × Real) := fun p => (-p.2, p.1)
        (∀ (a : BandPackingSymmetry), ∀ (p : Real × Real), R a (-p) = -R a p) → (∀ (a :
            BandPackingSymmetry), ∀ (p : Real × Real), R a (J p) = if O a then -J (R a p) else J
            (R a p)) ) := by
  classical
  intro O R J rneg a p
  induction a generalizing p with
  | identity => rfl
  | negate => simp [R, J, O, BandPackingSymmetryReversesOrientation]
  | conjugate => simp [R, J, O, BandPackingSymmetryReversesOrientation]
  | shift w => rfl
  | comp a b ia ib =>
      change R a (R b (-p.2, p.1)) =
        if xor (O a) (O b) then -(-(R a (R b p)).2, (R a (R b p)).1)
        else (-(R a (R b p)).2, (R a (R b p)).1)
      rw [ib]
      cases ha : O a <;> cases hb : O b
      · simp only [Bool.xor_false]
        simpa [J, ha] using ia (R b p)
      · simp only [Bool.xor_true, ite_true]
        rw [rneg, ia]
        simp [J, ha]
      · simp only [Bool.xor_false, ite_true]
        simpa [J, ha] using ia (R b p)
      · simp only [Bool.xor_true, ite_true]
        rw [rneg, ia]
        simp [J, ha]

private theorem offsetCov :
    (by
      classical
      exact
        let L := BandPackingSymmetryVectorAction
        let O := BandPackingSymmetryReversesOrientation
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p) (fun _ _ f k p => f (k p))
        let J : (Real × Real) → (Real × Real) := fun p => (-p.2, p.1)
        let offset : GaussianInt → Real × Real := fun w =>
          (1 / 2 : Real) • (GaussianRealPoint w - J (GaussianRealPoint w))
        (∀ (a : BandPackingSymmetry), ∀ (p : Real × Real), ∀ (t : Real × Real), R a (p - t) = R a
            p - R a t) → ((∀ (a : BandPackingSymmetry), ∀ (c : Real), ∀ (p : Real × Real), R a (c
            • p) = c • R a p) → ((∀ (a : BandPackingSymmetry), ∀ (w : GaussianInt), R a
            (GaussianRealPoint w) = GaussianRealPoint (L a w)) → ((∀ (a : BandPackingSymmetry), ∀
            (p : Real × Real), R a (J p) = if O a then -J (R a p) else J (R a p)) → (∀ (a :
            BandPackingSymmetry), ∀ (w : GaussianInt), R a (offset w) = offset (if O a then
            GaussianQuarterTurn (L a w) else L a w))))) ) := by
  classical
  intro L O R J offset rsub rsmul rpoint rq a w
  dsimp [offset]
  rw [rsmul, rsub, rq, rpoint]
  cases ho : O a <;> ext <;>
    simp [GaussianRealPoint, GaussianQuarterTurn, J] <;> ring

private theorem offsetSign :
    (by
      classical
      exact
        let J : (Real × Real) → (Real × Real) := fun p => (-p.2, p.1)
        let offset : GaussianInt → Real × Real := fun w =>
          (1 / 2 : Real) • (GaussianRealPoint w - J (GaussianRealPoint w))
        ∀ (d : Bool), ∀ (w : GaussianInt), offset ((if d then (-1 : GaussianInt) else 1) * w) =
            (if d then (-1 : Real) else 1) • offset w ) := by
  classical
  intro J offset d w
  cases d <;> ext <;> simp [offset, GaussianRealPoint, J] <;> ring

private theorem centroidCov :
    (by
      classical
      exact
        let B := BandPackingSymmetryTileAction
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p) (fun _ _ f k p => f (k p))
        ∀ (a : BandPackingSymmetry), ∀ (V : ProtoTile), TileCentroid (B a V) = R a (TileCentroid
            V) ) := by
  classical
  intro B R a V
  induction a generalizing V with
  | identity => rfl
  | shift w => rfl
  | negate => exact (TileQuarterTurnFormulas V).2.2.2.2.1
  | conjugate =>
      simp only [B, BandPackingSymmetryTileAction]
      rw [(TileQuarterTurnFormulas (TileQuarterTurn (TileReflection V))).2.2.2.2.1,
        (TileQuarterTurnFormulas (TileReflection V)).2.2.2.2.1,
        (TileReflectionFormulas V).2.2.2.2.1]
      simp [R]
  | comp a b ia ib => simp [B, R, BandPackingSymmetryTileAction, ia, ib]

private theorem parentSlot :
    (by
      classical
      exact
        let A := BandPackingSymmetryCircleAction
        let O := BandPackingSymmetryReversesOrientation
        let Q := BandPackingSymmetryQuadrupleAction
        ∀ (a : BandPackingSymmetry), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), Q a q (if
            O a then -i else i).succ = A a (q i.succ) ) := by
  classical
  intro A O Q a q i
  have neg1 : -(1 : Fin 3) = 2 := rfl
  have neg2 : -(2 : Fin 3) = 1 := rfl
  cases ho : O a <;> fin_cases i <;>
    simp [Q, A, O, BandPackingSymmetryQuadrupleAction,
      ho, neg1, neg2]

private theorem linkCov :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry),
        let A := BandPackingSymmetryCircleAction
        let B := BandPackingSymmetryTileAction
        let L := BandPackingSymmetryVectorAction
        let O := BandPackingSymmetryReversesOrientation
        let Q := BandPackingSymmetryQuadrupleAction
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p) (fun _ _ f k p => f (k p))
        let J : (Real × Real) → (Real × Real) := fun p => (-p.2, p.1)
        let offset : GaussianInt → Real × Real := fun w =>
          (1 / 2 : Real) • (GaussianRealPoint w - J (GaussianRealPoint w))
        (∀ (a : BandPackingSymmetry), ∀ (p : Real × Real), ∀ (t : Real × Real), R a (p - t) = R a
            p - R a t) → ((∀ (a : BandPackingSymmetry), ∀ (c : Real), ∀ (p : Real × Real), R a (c
            • p) = c • R a p) → ((∀ (a : BandPackingSymmetry), ∀ (w : GaussianInt), R a (offset
            w) = offset (if O a then GaussianQuarterTurn (L a w) else L a w)) → ((∀ (d : Bool), ∀
            (w : GaussianInt), offset ((if d then (-1 : GaussianInt) else 1) * w) = (if d then
            (-1 : Real) else 1) • offset w) → ((∀ (a : BandPackingSymmetry), ∀ (V : ProtoTile),
            TileCentroid (B a V) = R a (TileCentroid V)) → ((∀ (a : BandPackingSymmetry), ∀ (q :
            Fin 4 → CircleCoordinates), ∀ (i : Fin 3), Q a q (if O a then -i else i).succ = A a
            (q i.succ)) → (∀ (X : CircleCoordinates × ProtoTile), ∀ (Y : CircleCoordinates ×
            ProtoTile), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Bool),
            (ProperBandQuadruple q) → ((q 0 = Y.1) → ((q i.succ = X.1) → ((BandPrototile Y.1 Y.2)
            → ((BandPrototile X.1 X.2) → ((FootprintVertices X.2 ⊆ FootprintVertices Y.2) →
            ((TileCentroid X.2 - TileCentroid Y.2 =
            (if s then (1 : Real) else -1) • offset
              (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ)))) → (∃ s', ProperBandQuadruple
                  (Q g q) ∧ (Q g q) 0 = (A g Y.1) ∧ (Q g q) (if O g then -i else i).succ = A g
                  X.1 ∧ BandPrototile (A g Y.1) (B g Y.2) ∧ BandPrototile (A g X.1) (B g X.2) ∧
                  FootprintVertices (B g X.2) ⊆ FootprintVertices (B g Y.2) ∧ TileCentroid (B g
                  X.2) - TileCentroid (B g Y.2) = (if s' then (1 : Real) else -1) • offset
                  (BandVectors.1 ((Q g q) (((if O g then -i else i) + 2).succ)) ((Q g q) (((if O
                  g then -i else i) + 1).succ)))))))))))))))) ) := by
  classical
  intro g A B L O Q R J offset rsub rsmul offsetCov offsetSign centroidCov parentSlot X Y q i s
      hq hq0 hqi hY hX hfoot hcent
  obtain ⟨d, hd, _⟩ := BandPackingSymmetryProjectiveVectorCovariance g q hq
  let sigma : Fin 3 → Fin 3 := fun j => if O g then -j else j
  let w := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
  let w' := BandVectors.1 (Q g q ((sigma i + 2).succ))
    (Q g q ((sigma i + 1).succ))
  have hw : w' = (if d then (-1 : GaussianInt) else 1) *
      (if O g then GaussianQuarterTurn (L g w) else L g w) := by
    have hh := (hd i).2.2
    simpa [w', sigma, Q, O, BandPackingSymmetryQuadrupleAction] using hh
  let eps : Real := if d then -1 else 1
  have centroid : TileCentroid (B g X.2) - TileCentroid (B g Y.2) =
      (if s then (1 : Real) else -1) • offset
        (if O g then GaussianQuarterTurn (L g w) else L g w) := by
    rw [centroidCov, centroidCov, ← rsub, hcent, rsmul, offsetCov]
  have w'eq : w' = BandVectors.1 (Q g q ((if O g then -i else i) + 2).succ)
      (Q g q ((if O g then -i else i) + 1).succ) := by rfl
  have sign : (if s then (1 : Real) else -1) * eps =
      (if xor s d then (1 : Real) else -1) := by
    cases s <;> cases d <;> norm_num [eps]
  refine ⟨xor s d, BandPackingSymmetryProperCovariance g q hq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Q, BandPackingSymmetryQuadrupleAction] using congrArg (A g) hq0
  · rw [parentSlot]
    simp [hqi]
  · exact (BandPackingSymmetryCovariance g).2.1 Y.1 Y.2 |>.mp hY
  · exact (BandPackingSymmetryCovariance g).2.1 X.1 X.2 |>.mp hX
  · rw [(BandPackingSymmetryTilingTransport g).2.2.2.2.2.2.2.1,
      (BandPackingSymmetryTilingTransport g).2.2.2.2.2.2.2.1]
    exact Set.image_mono hfoot
  · rw [← w'eq, hw, offsetSign]
    cases s <;> cases d <;> simp [centroid]

private theorem edgeCov :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry),
        let A := BandPackingSymmetryCircleAction
        let B := BandPackingSymmetryTileAction
        let O := BandPackingSymmetryReversesOrientation
        let Q := BandPackingSymmetryQuadrupleAction
        let J : (Real × Real) → (Real × Real) := fun p => (-p.2, p.1)
        let offset : GaussianInt → Real × Real := fun w =>
          (1 / 2 : Real) • (GaussianRealPoint w - J (GaussianRealPoint w))
        (∀ (X : CircleCoordinates × ProtoTile), ∀ (Y : CircleCoordinates × ProtoTile), ∀ (q : Fin
            4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Bool), (ProperBandQuadruple q) → ((q 0
            = Y.1) → ((q i.succ = X.1) → ((BandPrototile Y.1 Y.2) → ((BandPrototile X.1 X.2) →
            ((FootprintVertices X.2 ⊆ FootprintVertices Y.2) → ((TileCentroid X.2 - TileCentroid
            Y.2 = (if s then (1 : Real) else -1) • offset (BandVectors.1 (q ((i + 2).succ)) (q
            ((i + 1).succ)))) → (∃ s', ProperBandQuadruple (Q g q) ∧ (Q g q) 0 = (A g Y.1) ∧ (Q g
            q) (if O g then -i else i).succ = A g X.1 ∧ BandPrototile (A g Y.1) (B g Y.2) ∧
            BandPrototile (A g X.1) (B g X.2) ∧ FootprintVertices (B g X.2) ⊆ FootprintVertices
            (B g Y.2) ∧ TileCentroid (B g X.2) - TileCentroid (B g Y.2) = (if s' then (1 : Real)
            else -1) • offset (BandVectors.1 ((Q g q) (((if O g then -i else i) + 2).succ)) ((Q g
            q) (((if O g then -i else i) + 1).succ))))))))))) → (
        let F : CircleCoordinates × ProtoTile → CircleCoordinates × ProtoTile :=
          fun z => (A g z.1, B g z.2)
        let Edge : (CircleCoordinates × ProtoTile) →
            (CircleCoordinates × ProtoTile) → Prop := fun X Y =>
          ∃ q : Fin 4 → CircleCoordinates, ∃ i : Fin 3, ∃ s : Bool,
            ProperBandQuadruple q ∧ q 0 = Y.1 ∧ q i.succ = X.1 ∧
            BandPrototile Y.1 Y.2 ∧ BandPrototile X.1 X.2 ∧
            FootprintVertices X.2 ⊆ FootprintVertices Y.2 ∧
            TileCentroid X.2 - TileCentroid Y.2 =
              (if s then (1 : Real) else -1) • offset
                (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ)))
        ∀ {X : CircleCoordinates × ProtoTile}, ∀ {Y : CircleCoordinates × ProtoTile}, (Edge X Y)
            → (Edge (F X) (F Y))) ) := by
  classical
  intro g A B O Q J offset linkCov F Edge X Y hedge
  rcases hedge with ⟨q, i, s, hq, hq0, hqi, hY, hX, hfoot, hcent⟩
  obtain ⟨s', hq', hq0', hqi', hY', hX', hfoot', hcent'⟩ :=
    linkCov X Y q i s hq hq0 hqi hY hX hfoot hcent
  refine ⟨Q g q, (if O g then -i else i), s', hq', hq0', hqi',
    hY', hX', hfoot', ?_⟩
  simpa [F] using hcent'

private theorem hAnc' :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (C : CircleCoordinates), ∀ (D : CircleCoordinates), ∀ (U :
            ProtoTile), ∀ (T : ProtoTile), (AncestorTile C D U T) → (
        let A := BandPackingSymmetryCircleAction
        let B := BandPackingSymmetryTileAction
        let J : (Real × Real) → (Real × Real) := fun p => (-p.2, p.1)
        let offset : GaussianInt → Real × Real := fun w =>
          (1 / 2 : Real) • (GaussianRealPoint w - J (GaussianRealPoint w))
        let F : CircleCoordinates × ProtoTile → CircleCoordinates × ProtoTile :=
          fun z => (A g z.1, B g z.2)
        let Edge : (CircleCoordinates × ProtoTile) →
            (CircleCoordinates × ProtoTile) → Prop := fun X Y =>
          ∃ q : Fin 4 → CircleCoordinates, ∃ i : Fin 3, ∃ s : Bool,
            ProperBandQuadruple q ∧ q 0 = Y.1 ∧ q i.succ = X.1 ∧
            BandPrototile Y.1 Y.2 ∧ BandPrototile X.1 X.2 ∧
            FootprintVertices X.2 ⊆ FootprintVertices Y.2 ∧
            TileCentroid X.2 - TileCentroid Y.2 =
              (if s then (1 : Real) else -1) • offset
                (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ)))
        (∀ {X : CircleCoordinates × ProtoTile}, ∀ {Y : CircleCoordinates × ProtoTile}, (Edge X Y)
            → (Edge (F X) (F Y))) → (Relation.ReflTransGen Edge (F (C, U)) (F (D, T)))) ) := by
  classical
  intro g C D U T hAnc A B J offset F Edge edgeCov
  change Relation.ReflTransGen Edge (C, U) (D, T) at hAnc
  refine Relation.ReflTransGen.head_induction_on
    (motive := fun a _ => Relation.ReflTransGen Edge (F a) (F (D, T)))
    hAnc ?_ ?_
  · exact Relation.ReflTransGen.refl
  · intro a b hedge hrest ih
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (edgeCov hedge)) ih

end AncestorSymmetryGeometry

theorem P4261T2AncestorSymmetry
    (g : BandPackingSymmetry) (C D : CircleCoordinates)
    (U T : ProtoTile) (k h : PartialOdometer)
    (ha : AncestorOdometer C D U T k h) :
    AncestorOdometer (BandPackingSymmetryCircleAction g C)
      (BandPackingSymmetryCircleAction g D)
      (BandPackingSymmetryTileAction g U) (BandPackingSymmetryTileAction g T)
      (BandPackingSymmetryPartialOdometerAction g k)
      (BandPackingSymmetryPartialOdometerAction g h) := by
-- BODY
  classical
  rcases ha with ⟨hTile, hAnc, hDom, hIncl, hVal⟩
  have hTile' := BandPackingSymmetryTileOdometerCovariance g D T h hTile
  have hFoot := BandPackingSymmetryTilingTransport g
  have hOdo := BandPackingSymmetryPartialOdometerActionFormulas g k h
  have hDomain :
      ((BandPackingSymmetryPartialOdometerAction g k).domain : Set GaussianInt) =
        FootprintVertices (BandPackingSymmetryTileAction g U) := by
    rw [hOdo.1, hDom, hFoot.2.2.2.2.2.2.2.1]
  have hInclusion := AncestorSymmetryGeometry.hInclusion g k h hIncl
  have actionForward (a : BandPackingSymmetry) (p : PartialOdometer)
      (x : GaussianInt) (hx : x ∈ p.domain) := AncestorSymmetryGeometry.actionForward a p x hx
  have literalRestriction (g : BandPackingSymmetry) (k h : PartialOdometer)
      (hsub : k.domain ⊆ h.domain)
      (heq : ∀ x, x ∈ k.domain → k.value x = h.value x) :=
          AncestorSymmetryGeometry.literalRestriction actionForward g k h hsub heq
  let A := BandPackingSymmetryCircleAction
  let B := BandPackingSymmetryTileAction
  let L := BandPackingSymmetryVectorAction
  let O := BandPackingSymmetryReversesOrientation
  let Q := BandPackingSymmetryQuadrupleAction
  let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
    BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
      (fun p => (-p.1, p.2)) (fun _ p => p) (fun _ _ f k p => f (k p))
  let J : (Real × Real) → (Real × Real) := fun p => (-p.2, p.1)
  let offset : GaussianInt → Real × Real := fun w =>
    (1 / 2 : Real) • (GaussianRealPoint w - J (GaussianRealPoint w))
  have rsub (a : BandPackingSymmetry) (p t : Real × Real) := AncestorSymmetryGeometry.rsub a p t
  have rsmul (a : BandPackingSymmetry) (c : Real) (p : Real × Real) :=
      AncestorSymmetryGeometry.rsmul a c p
  have rneg (a : BandPackingSymmetry) (p : Real × Real) := AncestorSymmetryGeometry.rneg rsmul a p
  have rminusq (a : BandPackingSymmetry) (p : Real × Real) := AncestorSymmetryGeometry.rminusq
      rneg a p
  have rpoint (a : BandPackingSymmetry) (w : GaussianInt) := AncestorSymmetryGeometry.rpoint a w
  have rq (a : BandPackingSymmetry) (p : Real × Real) := AncestorSymmetryGeometry.rq rneg a p
  have offsetCov (a : BandPackingSymmetry) (w : GaussianInt) :=
      AncestorSymmetryGeometry.offsetCov rsub rsmul rpoint rq a w
  have offsetSign (d : Bool) (w : GaussianInt) := AncestorSymmetryGeometry.offsetSign d w
  have centroidCov (a : BandPackingSymmetry) (V : ProtoTile) :=
      AncestorSymmetryGeometry.centroidCov a V
  have parentSlot (a : BandPackingSymmetry) (q : Fin 4 → CircleCoordinates)
      (i : Fin 3) := AncestorSymmetryGeometry.parentSlot a q i
  have linkCov (X Y : CircleCoordinates × ProtoTile)
      (q : Fin 4 → CircleCoordinates) (i : Fin 3) (s : Bool)
      (hq : ProperBandQuadruple q) (hq0 : q 0 = Y.1)
      (hqi : q i.succ = X.1) (hY : BandPrototile Y.1 Y.2)
      (hX : BandPrototile X.1 X.2)
      (hfoot : FootprintVertices X.2 ⊆ FootprintVertices Y.2)
      (hcent : TileCentroid X.2 - TileCentroid Y.2 =
        (if s then (1 : Real) else -1) • offset
          (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ)))) :=
              AncestorSymmetryGeometry.linkCov g rsub rsmul offsetCov offsetSign centroidCov
              parentSlot X Y q i s hq hq0 hqi hY hX hfoot hcent
  refine ⟨hTile'.1, ?_, hDomain, hInclusion, ?_⟩
  · let F : CircleCoordinates × ProtoTile → CircleCoordinates × ProtoTile :=
      fun z => (A g z.1, B g z.2)
    let Edge : (CircleCoordinates × ProtoTile) →
        (CircleCoordinates × ProtoTile) → Prop := fun X Y =>
      ∃ q : Fin 4 → CircleCoordinates, ∃ i : Fin 3, ∃ s : Bool,
        ProperBandQuadruple q ∧ q 0 = Y.1 ∧ q i.succ = X.1 ∧
        BandPrototile Y.1 Y.2 ∧ BandPrototile X.1 X.2 ∧
        FootprintVertices X.2 ⊆ FootprintVertices Y.2 ∧
        TileCentroid X.2 - TileCentroid Y.2 =
          (if s then (1 : Real) else -1) • offset
            (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ)))
    have edgeCov {X Y : CircleCoordinates × ProtoTile} (hedge : Edge X Y) :=
        AncestorSymmetryGeometry.edgeCov g linkCov (X := X) (Y := Y) hedge
    have hAnc' := AncestorSymmetryGeometry.hAnc' g C D U T hAnc edgeCov
    change AncestorTile (A g C) (A g D) (B g U) (B g T)
    change Relation.ReflTransGen Edge (F (C, U)) (F (D, T))
    exact hAnc'
  · intro y hy
    change y ∈ ((BandPackingSymmetryPartialOdometerAction g k).domain : Set GaussianInt) at hy
    rw [(BandPackingSymmetryPartialOdometerActionFormulas g k k).1] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact literalRestriction g k h hIncl hVal x hx

end ApollonianSuperharmonic

end
