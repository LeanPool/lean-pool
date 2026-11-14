/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandRegimeClassification
public import LeanPool.ApollonianSuperharmonic.BandParentRotationOccurrenceCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileOdometerCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryGlobalOdometerTransport

-- [TABLET NODE: P4120T1RootNormalization]

/-!
# P4120T1RootNormalization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RootNormalizationGeometry

private theorem hroot' :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), (BandPrototile (q (0 : Fin (4 :
            ℕ))) T) → (∀ (a : Fin (3 : ℕ)), ∀ (s : BandPackingSymmetry),
        let qa : Fin 4 → CircleCoordinates :=
          ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]
        let q' := BandPackingSymmetryQuadrupleAction s qa
        let T' := BandPackingSymmetryTileAction s T
        BandPrototile (q' 0) T') ) := by
  classical
  intro q T hT a s qa q' T'
  have hb := (BandPackingSymmetryCovariance s).2.1 (qa 0) T
  have ht := hb.mp hT
  simpa [q', T', BandPackingSymmetryQuadrupleAction] using ht

private theorem hodo' :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (h : PartialOdometer),
            (TileOdometer (q (0 : Fin (4 : ℕ))) T h) → (∀ (a : Fin (3 : ℕ)), ∀ (s :
            BandPackingSymmetry),
        let qa : Fin 4 → CircleCoordinates :=
          ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]
        let q' := BandPackingSymmetryQuadrupleAction s qa
        let T' := BandPackingSymmetryTileAction s T
        let h' := BandPackingSymmetryPartialOdometerAction s h
        TileOdometer (q' 0) T' h') ) := by
  classical
  intro q T h hodo a s qa q' T' h'
  have ho := (BandPackingSymmetryTileOdometerCovariance s (q 0) T h hodo).1
  simpa [qa, q', T', h', BandPackingSymmetryQuadrupleAction,
    BandPackingSymmetryPartialOdometerAction] using ho

private theorem geom :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        ∀ (r : BandPackingSymmetry), ∀ U : ProtoTile, FootprintVertices
            (BandPackingSymmetryTileAction r U) = BandPackingSymmetryVectorAction r ''
            FootprintVertices U ∧ BoundaryFootprintVertices (BandPackingSymmetryTileAction r U) =
            BandPackingSymmetryVectorAction r '' BoundaryFootprintVertices U ∧ TileCentroid
            (BandPackingSymmetryTileAction r U) = R r (TileCentroid U) ) := by
  classical
  intro R r U
  induction r generalizing U with
  | identity => simp [R, BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction]
  | negate =>
      rcases TileQuarterTurnFormulas U with ⟨_, _, _, _, hc, hf, _, hb, _⟩
      have hmap : GaussianQuarterTurn =
          BandPackingSymmetryVectorAction .negate := by
        funext z
        rfl
      rw [BandPackingSymmetryTileAction, hf, hb, hc, hmap]
      exact ⟨rfl, rfl, by simp [R]⟩
  | conjugate =>
      rcases TileReflectionFormulas U with ⟨_, _, _, _, hc0, hf0, _, hb0, _⟩
      rcases TileQuarterTurnFormulas (TileReflection U) with
        ⟨_, _, _, _, hc1, hf1, _, hb1, _⟩
      rcases TileQuarterTurnFormulas (TileQuarterTurn (TileReflection U)) with
        ⟨_, _, _, _, hc2, hf2, _, hb2, _⟩
      have hmap : (fun z => GaussianQuarterTurn (GaussianQuarterTurn
          (GaussianReflection z))) =
          BandPackingSymmetryVectorAction .conjugate := by
        funext z
        ext <;> simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn,
          GaussianReflection]
      constructor
      · rw [BandPackingSymmetryTileAction, hf2, hf1, hf0,
          Set.image_image, Set.image_image, hmap]
      constructor
      · rw [BandPackingSymmetryTileAction, hb2, hb1, hb0,
          Set.image_image, Set.image_image, hmap]
      · change TileCentroid
          (TileQuarterTurn (TileQuarterTurn (TileReflection U))) = _
        rw [hc2, hc1, hc0]
        simp [R]
  | shift w => simp [R, BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction]
  | comp g h ihg ihh =>
      have hg := ihg (BandPackingSymmetryTileAction h U)
      have hh := ihh U
      rcases hg with ⟨hgf, hgb, hgc⟩
      rcases hh with ⟨hhf, hhb, hhc⟩
      constructor
      · simp [BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction, Set.image_image,
          hgf, hhf]
      constructor
      · simp [BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction, Set.image_image,
          hgb, hhb]
      · simp [BandPackingSymmetryTileAction, R, hgc, hhc]

private theorem hinj :
    (by
      classical
      exact
        ∀ (r : BandPackingSymmetry), Function.Injective (BandPackingSymmetryVectorAction r) ) := by
  classical
  intro r
  induction r with
  | identity => intro x y hxy; exact hxy
  | negate =>
      intro x y hxy
      change GaussianQuarterTurn x = GaussianQuarterTurn y at hxy
      have hh := congrArg GaussianQuarterTurn hxy
      rcases x with ⟨xr, xi⟩
      rcases y with ⟨yr, yi⟩
      simp [GaussianQuarterTurn] at hh ⊢
      omega
  | conjugate =>
      intro x y hxy
      change -GaussianReflection x = -GaussianReflection y at hxy
      have hn : GaussianReflection x = GaussianReflection y := neg_injective hxy
      have hh := congrArg GaussianReflection hn
      rcases x with ⟨xr, xi⟩
      rcases y with ⟨yr, yi⟩
      simp [GaussianReflection] at hh ⊢
      omega
  | shift w => intro x y hxy; exact hxy
  | comp r t ihr iht =>
      intro x y hxy
      exact iht (ihr hxy)

private theorem rinj :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        ∀ (r : BandPackingSymmetry), Function.Injective (R r) ) := by
  classical
  intro R r
  induction r with
  | identity => intro x y hxy; exact hxy
  | negate =>
      intro x y hxy
      change (-x.2, x.1) = (-y.2, y.1) at hxy
      exact Prod.ext (by simpa using congrArg Prod.snd hxy)
        (by simpa using congrArg Prod.fst hxy)
  | conjugate =>
      intro x y hxy
      change (-x.1, x.2) = (-y.1, y.2) at hxy
      exact Prod.ext (by simpa using congrArg Prod.fst hxy)
        (by simpa using congrArg Prod.snd hxy)
  | shift w => intro x y hxy; exact hxy
  | comp r t ihr iht =>
      intro x y hxy
      exact iht (ihr hxy)

private theorem rpoint :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        ∀ (r : BandPackingSymmetry), ∀ (z : GaussianInt), R r (GaussianRealPoint z) =
            GaussianRealPoint (BandPackingSymmetryVectorAction r z) ) := by
  classical
  intro R r z
  induction r generalizing z with
  | identity => rfl
  | negate => simp [R, BandPackingSymmetryVectorAction, GaussianRealPoint,
      GaussianQuarterTurn]
  | conjugate => simp [R, BandPackingSymmetryVectorAction, GaussianRealPoint,
      GaussianReflection]
  | shift w => rfl
  | comp r t ihr iht => simp [R, BandPackingSymmetryVectorAction, ihr, iht]

private theorem hidx :
    (by
      classical
      exact
        ∀ (a : Fin (3 : ℕ)), ∀ (i : Fin 3), a + (i - a) = i ) := by
  classical
  intro a i
  apply Fin.ext
  simp

private theorem he :
    (by
      classical
      exact
        ∀ (a : Fin (3 : ℕ)), ∀ (s : BandPackingSymmetry), ∀ (d : Bool), ∀ (e₁ : Fin (3 : ℕ) ×
            Bool ≃ Fin (3 : ℕ) × Bool), (∀ (i : Fin (3 : ℕ)), ∀ (s_1 : Bool), (e₁ : Fin
            (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s_1) = ((fun (i : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation s = true then -i else i) i, s_1 ^^ d)) → (
        let shift : (Fin 3 × Bool) ≃ (Fin 3 × Bool) :=
          { toFun := fun p => (p.1 - a, p.2)
            invFun := fun p => (p.1 + a, p.2)
            left_inv := by
              rintro ⟨i, t⟩
              apply Prod.ext
              · apply Fin.ext
                simp
              · rfl
            right_inv := by
              rintro ⟨i, t⟩
              apply Prod.ext
              · apply Fin.ext
                simp
              · rfl }
        let e : (Fin 3 × Bool) ≃ (Fin 3 × Bool) := shift.trans e₁
        ∀ (i : Fin 3), ∀ (t : Bool), e (i, t) = ((if BandPackingSymmetryReversesOrientation s
            then -(i - a) else i - a), xor t d))) := by
  classical
  intro a s d e₁ he₁ shift e i t
  simp [e, shift, Equiv.trans_apply, he₁]

private theorem hSact :
    (by
      classical
      exact
        ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (a : Fin (3 : ℕ)), ∀ (s : BandPackingSymmetry),
        let Sa : Fin 3 → Bool → ProtoTile := fun i t => S (a + i) t
        ∀ (e₁ : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool), ∀ (S' : Fin (3 : ℕ) → Bool →
            ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s_1 : Bool), S' ((e₁ : Fin (3 : ℕ) ×
            Bool → Fin (3 : ℕ) × Bool) (i, s_1)).1 ((e₁ : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) ×
            Bool) (i, s_1)).2 = BandPackingSymmetryTileAction s (Sa i s_1)) → (
        let shift : (Fin 3 × Bool) ≃ (Fin 3 × Bool) :=
          { toFun := fun p => (p.1 - a, p.2)
            invFun := fun p => (p.1 + a, p.2)
            left_inv := by
              rintro ⟨i, t⟩
              apply Prod.ext
              · apply Fin.ext
                simp
              · rfl
            right_inv := by
              rintro ⟨i, t⟩
              apply Prod.ext
              · apply Fin.ext
                simp
              · rfl }
        let e : (Fin 3 × Bool) ≃ (Fin 3 × Bool) := shift.trans e₁
        (∀ (i : Fin 3), a + (i - a) = i) → (∀ (i : Fin 3), ∀ (t : Bool), S' (e (i, t)).1 (e (i,
            t)).2 = BandPackingSymmetryTileAction s (S i t)))) := by
  classical
  intro S a s Sa e₁ S' hS₁ shift e hidx i t
  rw [show (e (i, t)).1 = (e₁ (i - a, t)).1 by rfl,
    show (e (i, t)).2 = (e₁ (i - a, t)).2 by rfl]
  rw [hS₁]
  congr 1
  dsimp [Sa]
  rw [hidx]

private theorem hparent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (a : Fin (3 : ℕ)), ∀ (s : BandPackingSymmetry),
        let qa : Fin 4 → CircleCoordinates :=
          ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]
        let q' := BandPackingSymmetryQuadrupleAction s qa
        ∀ (j : Fin 3), q' (if BandPackingSymmetryReversesOrientation s then -j else j).succ =
            BandPackingSymmetryCircleAction s (qa j.succ) ) := by
  classical
  intro q a s qa q' j
  have hn1 : -(1 : Fin 3) = 2 := rfl
  have hn2 : -(2 : Fin 3) = 1 := rfl
  cases hr : BandPackingSymmetryReversesOrientation s <;> fin_cases j <;>
    simp [q', qa, BandPackingSymmetryQuadrupleAction, hr, hn1, hn2]

private theorem hcurvature :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (a : Fin (3 : ℕ)), ∀ (s : BandPackingSymmetry),
        let qa : Fin 4 → CircleCoordinates :=
          ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]
        (∀ (C : CircleCoordinates), (BandPackingSymmetryCircleAction s C).1 = C.1) → (
        let q' := BandPackingSymmetryQuadrupleAction s qa
        ∀ (d : Bool), ∀ (e₁ : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool),
        let shift : (Fin 3 × Bool) ≃ (Fin 3 × Bool) :=
          { toFun := fun p => (p.1 - a, p.2)
            invFun := fun p => (p.1 + a, p.2)
            left_inv := by
              rintro ⟨i, t⟩
              apply Prod.ext
              · apply Fin.ext
                simp
              · rfl
            right_inv := by
              rintro ⟨i, t⟩
              apply Prod.ext
              · apply Fin.ext
                simp
              · rfl }
        let e : (Fin 3 × Bool) ≃ (Fin 3 × Bool) := shift.trans e₁
        (∀ (i : Fin 3), a + (i - a) = i) → ((∀ (i : Fin 3), ∀ (t : Bool), e (i, t) = ((if
            BandPackingSymmetryReversesOrientation s then -(i - a) else i - a), xor t d)) → ((∀
                (j : Fin 3), q' (if BandPackingSymmetryReversesOrientation s then -j else j).succ =
            BandPackingSymmetryCircleAction s (qa j.succ)) → ((∀ (j : Fin 3), qa j.succ = q (a +
            j).succ) → (∀ (i : Fin 3), ∀ (t : Bool), (q' (e (i, t)).1.succ).1 = (q
                i.succ).1)))))) := by
  classical
  intro q a s qa hcureq q' d e₁ shift e hidx he hparent hqaIdx i t
  rw [he, hparent, hcureq]
  rw [hqaIdx, hidx]

private theorem himage :
    (by
      classical
      exact
        ∀ (s : BandPackingSymmetry), (∀ (r : BandPackingSymmetry), Function.Injective
            (BandPackingSymmetryVectorAction r)) → (∀ (z : GaussianInt), ∀ (A : Set GaussianInt),
            (BandPackingSymmetryVectorAction s z ∈ BandPackingSymmetryVectorAction s '' A) ↔ z ∈
            A) ) := by
  classical
  intro s hinj z A
  constructor
  · rintro ⟨y, hy, hzy⟩
    have : y = z := hinj s hzy
    simpa [this] using hy
  · intro hz
    exact ⟨z, hz, rfl⟩

private theorem hx' :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), (x ∈ FootprintVertices T) → (∀ (s :
            BandPackingSymmetry),
        let T' := BandPackingSymmetryTileAction s T
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        (∀ (U : ProtoTile), FootprintVertices (BandPackingSymmetryTileAction s U) =
            BandPackingSymmetryVectorAction s '' FootprintVertices U ∧ BoundaryFootprintVertices
            (BandPackingSymmetryTileAction s U) = BandPackingSymmetryVectorAction s ''
            BoundaryFootprintVertices U ∧ TileCentroid (BandPackingSymmetryTileAction s U) = R s
            (TileCentroid U)) → ((∀ (z : GaussianInt), ∀ (A : Set GaussianInt),
            (BandPackingSymmetryVectorAction s z ∈ BandPackingSymmetryVectorAction s '' A) ↔ z ∈
            A) → (
        let x' := BandPackingSymmetryVectorAction s x
        x' ∈ FootprintVertices T'))) ) := by
  classical
  intro T x hx s T' R hgeom himage x'
  rw [(hgeom T).1]
  exact (himage x (FootprintVertices T)).2 hx

private theorem hxb' :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), (x ∉ BoundaryFootprintVertices T) → (∀ (s :
            BandPackingSymmetry),
        let T' := BandPackingSymmetryTileAction s T
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        (∀ (U : ProtoTile), FootprintVertices (BandPackingSymmetryTileAction s U) =
            BandPackingSymmetryVectorAction s '' FootprintVertices U ∧ BoundaryFootprintVertices
            (BandPackingSymmetryTileAction s U) = BandPackingSymmetryVectorAction s ''
            BoundaryFootprintVertices U ∧ TileCentroid (BandPackingSymmetryTileAction s U) = R s
            (TileCentroid U)) → ((∀ (z : GaussianInt), ∀ (A : Set GaussianInt),
            (BandPackingSymmetryVectorAction s z ∈ BandPackingSymmetryVectorAction s '' A) ↔ z ∈
            A) → (
        let x' := BandPackingSymmetryVectorAction s x
        x' ∉ BoundaryFootprintVertices T'))) ) := by
  classical
  intro T x hxb s T' R hgeom himage x'
  rw [(hgeom T).2.1]
  intro hh
  exact hxb ((himage x (BoundaryFootprintVertices T)).1 hh)

private theorem hfp :
    (by
      classical
      exact
        ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (x : GaussianInt), ∀ (a : Fin (3 : ℕ)), ∀ (s :
            BandPackingSymmetry), ∀ (e₁ : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool), ∀ (S' : Fin
            (3 : ℕ) → Bool → ProtoTile),
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        (∀ (U : ProtoTile), FootprintVertices (BandPackingSymmetryTileAction s U) =
            BandPackingSymmetryVectorAction s '' FootprintVertices U ∧ BoundaryFootprintVertices
            (BandPackingSymmetryTileAction s U) = BandPackingSymmetryVectorAction s ''
            BoundaryFootprintVertices U ∧ TileCentroid (BandPackingSymmetryTileAction s U) = R s
            (TileCentroid U)) → (
        let shift : (Fin 3 × Bool) ≃ (Fin 3 × Bool) :=
          { toFun := fun p => (p.1 - a, p.2)
            invFun := fun p => (p.1 + a, p.2)
            left_inv := by
              rintro ⟨i, t⟩
              apply Prod.ext
              · apply Fin.ext
                simp
              · rfl
            right_inv := by
              rintro ⟨i, t⟩
              apply Prod.ext
              · apply Fin.ext
                simp
              · rfl }
        let e : (Fin 3 × Bool) ≃ (Fin 3 × Bool) := shift.trans e₁
        (∀ (i : Fin 3), ∀ (t : Bool), S' (e (i, t)).1 (e (i, t)).2 =
            BandPackingSymmetryTileAction s (S i t)) → ((∀ (z : GaussianInt), ∀ (A : Set
            GaussianInt), (BandPackingSymmetryVectorAction s z ∈ BandPackingSymmetryVectorAction
            s '' A) ↔ z ∈ A) → (
        let x' := BandPackingSymmetryVectorAction s x
        ∀ (i : Fin 3), ∀ (t : Bool), (x' ∈ FootprintVertices (S' (e (i, t)).1 (e (i, t)).2)) ↔ x
            ∈ FootprintVertices (S i t))))) := by
  classical
  intro S x a s e₁ S' R hgeom shift e hSact himage x' i t
  rw [hSact, (hgeom (S i t)).1]
  exact himage x _

private theorem hbd :
    (by
      classical
      exact
        ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (x : GaussianInt), ∀ (a : Fin (3 : ℕ)), ∀ (s :
            BandPackingSymmetry), ∀ (e₁ : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool), ∀ (S' : Fin
            (3 : ℕ) → Bool → ProtoTile),
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        (∀ (U : ProtoTile), FootprintVertices (BandPackingSymmetryTileAction s U) =
            BandPackingSymmetryVectorAction s '' FootprintVertices U ∧ BoundaryFootprintVertices
            (BandPackingSymmetryTileAction s U) = BandPackingSymmetryVectorAction s ''
            BoundaryFootprintVertices U ∧ TileCentroid (BandPackingSymmetryTileAction s U) = R s
            (TileCentroid U)) → (
        let shift : (Fin 3 × Bool) ≃ (Fin 3 × Bool) :=
          { toFun := fun p => (p.1 - a, p.2)
            invFun := fun p => (p.1 + a, p.2)
            left_inv := by
              rintro ⟨i, t⟩
              apply Prod.ext
              · apply Fin.ext
                simp
              · rfl
            right_inv := by
              rintro ⟨i, t⟩
              apply Prod.ext
              · apply Fin.ext
                simp
              · rfl }
        let e : (Fin 3 × Bool) ≃ (Fin 3 × Bool) := shift.trans e₁
        (∀ (i : Fin 3), ∀ (t : Bool), S' (e (i, t)).1 (e (i, t)).2 =
            BandPackingSymmetryTileAction s (S i t)) → ((∀ (z : GaussianInt), ∀ (A : Set
            GaussianInt), (BandPackingSymmetryVectorAction s z ∈ BandPackingSymmetryVectorAction
            s '' A) ↔ z ∈ A) → (
        let x' := BandPackingSymmetryVectorAction s x
        ∀ (i : Fin 3), ∀ (t : Bool), (x' ∈ BoundaryFootprintVertices (S' (e (i, t)).1 (e (i,
            t)).2)) ↔ x ∈ BoundaryFootprintVertices (S i t))))) := by
  classical
  intro S x a s e₁ S' R hgeom shift e hSact himage x' i t
  rw [hSact, (hgeom (S i t)).2.1]
  exact himage x _

private theorem hcent :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), ∀ (s : BandPackingSymmetry),
        let T' := BandPackingSymmetryTileAction s T
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        (∀ (U : ProtoTile), FootprintVertices (BandPackingSymmetryTileAction s U) =
            BandPackingSymmetryVectorAction s '' FootprintVertices U ∧ BoundaryFootprintVertices
            (BandPackingSymmetryTileAction s U) = BandPackingSymmetryVectorAction s ''
            BoundaryFootprintVertices U ∧ TileCentroid (BandPackingSymmetryTileAction s U) = R s
            (TileCentroid U)) → ((∀ (r : BandPackingSymmetry), Function.Injective (R r)) → ((∀ (r
            : BandPackingSymmetry), ∀ (z : GaussianInt), R r (GaussianRealPoint z) =
            GaussianRealPoint (BandPackingSymmetryVectorAction r z)) → (
        let x' := BandPackingSymmetryVectorAction s x
        (GaussianRealPoint x' = TileCentroid T') ↔ (GaussianRealPoint x = TileCentroid T)))) ) := by
  classical
  intro T x s T' R hgeom rinj rpoint x'
  change (GaussianRealPoint (BandPackingSymmetryVectorAction s x) =
      TileCentroid (BandPackingSymmetryTileAction s T)) ↔ _
  rw [← rpoint s x, (hgeom T).2.2]
  constructor
  · intro hh
    exact rinj s hh
  · intro hh
    exact congrArg (R s) hh

private theorem hcard :
    (by
      classical
      exact
        ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (x : GaussianInt), ∀ (a : Fin (3 : ℕ)), ∀ (s :
            BandPackingSymmetry), ∀ (e₁ : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool), ∀ (S' : Fin
            (3 : ℕ) → Bool → ProtoTile),
        let shift : (Fin 3 × Bool) ≃ (Fin 3 × Bool) :=
          { toFun := fun p => (p.1 - a, p.2)
            invFun := fun p => (p.1 + a, p.2)
            left_inv := by
              rintro ⟨i, t⟩
              apply Prod.ext
              · apply Fin.ext
                simp
              · rfl
            right_inv := by
              rintro ⟨i, t⟩
              apply Prod.ext
              · apply Fin.ext
                simp
              · rfl }
        let e : (Fin 3 × Bool) ≃ (Fin 3 × Bool) := shift.trans e₁
        let x' := BandPackingSymmetryVectorAction s x
        (∀ (i : Fin 3), ∀ (t : Bool), (x' ∈ BoundaryFootprintVertices (S' (e (i, t)).1 (e (i,
            t)).2)) ↔ x ∈ BoundaryFootprintVertices (S i t)) → (Nat.card
            {b : Fin 3 × Bool // x' ∈ BoundaryFootprintVertices (S' b.1 b.2)} = Nat.card
            {b : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (S b.1 b.2)}) ) := by
  classical
  intro S x a s e₁ S' shift e x' hbd
  let A : Type := {b : Fin 3 × Bool //
    x ∈ BoundaryFootprintVertices (S b.1 b.2)}
  let B : Type := {b : Fin 3 × Bool //
    x' ∈ BoundaryFootprintVertices (S' b.1 b.2)}
  let eb : A ≃ B :=
    { toFun := fun b => ⟨e b.1, by
        have hb := (hbd b.1.1 b.1.2)
        simpa using hb.mpr b.2⟩
      invFun := fun b => ⟨e.symm b.1, by
        have hb := hbd (e.symm b.1).1 (e.symm b.1).2
        have hmem : x' ∈ BoundaryFootprintVertices
            (S' (e (e.symm b.1)).1 (e (e.symm b.1)).2) := by
          simpa only [e.apply_symm_apply] using b.2
        exact hb.mp hmem⟩
      left_inv := by intro b; apply Subtype.ext; simp
      right_inv := by intro b; apply Subtype.ext; simp }
  exact Nat.card_congr eb.symm

end RootNormalizationGeometry

theorem P4120T1RootNormalization
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (T : ProtoTile) (S : Fin 3 → Bool → ProtoTile)
    (h : PartialOdometer) (g : IntegerLatticeFunction)
    (hT : BandPrototile (q 0) T) (hodo : TileOdometer (q 0) T h)
    (hext : GlobalOdometerExtends g h)
    (hS : ∀ i s, BandSubtileOccurrence q T i s (S i s))
    (hcells : ∀ z, z ∈ T.cells ↔ ∃ i s, z ∈ (S i s).cells)
    (x : GaussianInt) (hx : x ∈ FootprintVertices T)
    (hxb : x ∉ BoundaryFootprintVertices T) :
    ∃ (q' : Fin 4 → CircleCoordinates) (T' : ProtoTile)
      (S' : Fin 3 → Bool → ProtoTile) (h' : PartialOdometer)
      (g' : IntegerLatticeFunction) (x' : GaussianInt)
      (e : (Fin 3 × Bool) ≃ (Fin 3 × Bool)),
      ProperBandQuadruple q' ∧ BandPrototile (q' 0) T' ∧
      TileOdometer (q' 0) T' h' ∧ GlobalOdometerExtends g' h' ∧
      (∀ i s, BandSubtileOccurrence q' T' i s (S' i s)) ∧
      (∀ z, z ∈ T'.cells ↔ ∃ i s, z ∈ (S' i s).cells) ∧
      x' ∈ FootprintVertices T' ∧ x' ∉ BoundaryFootprintVertices T' ∧
      (∀ a : Fin 3 × Bool,
        (q' (e a).1.succ).1 = (q a.1.succ).1 ∧
        (x' ∈ FootprintVertices (S' (e a).1 (e a).2) ↔
          x ∈ FootprintVertices (S a.1 a.2)) ∧
        (x' ∈ BoundaryFootprintVertices (S' (e a).1 (e a).2) ↔
          x ∈ BoundaryFootprintVertices (S a.1 a.2))) ∧
      Nat.card {a : Fin 3 × Bool // x' ∈ BoundaryFootprintVertices (S' a.1 a.2)} =
        Nat.card {a : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (S a.1 a.2)} ∧
      (GaussianRealPoint x' = TileCentroid T' ↔
        GaussianRealPoint x = TileCentroid T) ∧
      FourNeighborLaplacian g' x' = FourNeighborLaplacian g x ∧
      ((∃ P : FordFareyParameter, 1 < P.q ∧ q' = FordRecursiveQuadruple P) ∨
        (∃ K : DiamondParameter, 1 < K.1 ∧ q' = DiamondRecursiveQuadruple K) ∨
        Nonempty (BandOrderedGeneralConfiguration q')) := by
-- BODY
  classical
  obtain ⟨a, s, hclass⟩ := BandRegimeClassification q hq
  let qa : Fin 4 → CircleCoordinates :=
    ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]
  let Sa : Fin 3 → Bool → ProtoTile := fun i t => S (a + i) t
  have hrot := BandParentRotationOccurrenceCovariance q hq a T hT S hS hcells
  have hqa : ProperBandQuadruple qa := by simpa [qa] using hrot.1
  have hSa : ∀ i t, BandSubtileOccurrence qa T i t (Sa i t) := by
    simpa [qa, Sa] using hrot.2.1
  have hcellSa : ∀ z, z ∈ T.cells ↔ ∃ i t, z ∈ (Sa i t).cells := by
    simpa [Sa] using hrot.2.2
  have hclass' := hclass
  change Xor
      (∃ P : FordFareyParameter,
        1 < P.q ∧ BandPackingSymmetryQuadrupleAction s qa = FordRecursiveQuadruple P)
      (Xor
        (∃ K : DiamondParameter,
          1 < K.1 ∧ BandPackingSymmetryQuadrupleAction s qa = DiamondRecursiveQuadruple K)
        (Nonempty (BandOrderedGeneralConfiguration
          (BandPackingSymmetryQuadrupleAction s qa)))) at hclass'
  have hcureq (C : CircleCoordinates) :
      (BandPackingSymmetryCircleAction s C).1 = C.1 :=
    (BandPackingSymmetryCovariance s).1 C
  let q' := BandPackingSymmetryQuadrupleAction s qa
  let T' := BandPackingSymmetryTileAction s T
  let h' := BandPackingSymmetryPartialOdometerAction s h
  have hproper' : ProperBandQuadruple q' := by
    simpa [q'] using BandPackingSymmetryProperCovariance s qa hqa
  have hroot' := RootNormalizationGeometry.hroot' q T hT a s
  have hcov := (BandPackingSymmetryCovariance s).2.2 qa T Sa
    hqa hT hSa hcellSa
  obtain ⟨d, e₁, S', hd, he₁, hS₁, hocc', hcell'⟩ := hcov
  have hodo' := RootNormalizationGeometry.hodo' q T h hodo a s
  obtain ⟨g', hext', hlap⟩ :=
    BandPackingSymmetryGlobalOdometerTransport s g h x hext
  have geom (r : BandPackingSymmetry) := RootNormalizationGeometry.geom r
  have hgeom := geom s
  have hinj (r : BandPackingSymmetry) := RootNormalizationGeometry.hinj r
  have rinj (r : BandPackingSymmetry) := RootNormalizationGeometry.rinj r
  have rpoint (r : BandPackingSymmetry) (z : GaussianInt) := RootNormalizationGeometry.rpoint r z
  let shift : (Fin 3 × Bool) ≃ (Fin 3 × Bool) :=
    { toFun := fun p => (p.1 - a, p.2)
      invFun := fun p => (p.1 + a, p.2)
      left_inv := by
        rintro ⟨i, t⟩
        apply Prod.ext
        · apply Fin.ext
          simp
        · rfl
      right_inv := by
        rintro ⟨i, t⟩
        apply Prod.ext
        · apply Fin.ext
          simp
        · rfl }
  let e : (Fin 3 × Bool) ≃ (Fin 3 × Bool) := shift.trans e₁
  have hidx (i : Fin 3) := RootNormalizationGeometry.hidx a i
  have he (i : Fin 3) (t : Bool) := RootNormalizationGeometry.he a s d e₁ he₁ i t
  have hSact (i : Fin 3) (t : Bool) := RootNormalizationGeometry.hSact S a s e₁ S' hS₁ hidx i t
  have hparent (j : Fin 3) := RootNormalizationGeometry.hparent q a s j
  have hqaIdx (j : Fin 3) : qa j.succ = q (a + j).succ := by
    fin_cases j <;> simp [qa]
  have hcurvature (i : Fin 3) (t : Bool) := RootNormalizationGeometry.hcurvature q a s hcureq d
      e₁ hidx he hparent hqaIdx i t
  have himage (z : GaussianInt) (A : Set GaussianInt) := RootNormalizationGeometry.himage s hinj z A
  let x' := BandPackingSymmetryVectorAction s x
  have hx' := RootNormalizationGeometry.hx' T x hx s hgeom himage
  have hxb' := RootNormalizationGeometry.hxb' T x hxb s hgeom himage
  have hfp (i : Fin 3) (t : Bool) := RootNormalizationGeometry.hfp S x a s e₁ S' hgeom hSact
      himage i t
  have hbd (i : Fin 3) (t : Bool) := RootNormalizationGeometry.hbd S x a s e₁ S' hgeom hSact
      himage i t
  have hcent := RootNormalizationGeometry.hcent T x s hgeom rinj rpoint
  have hcard := RootNormalizationGeometry.hcard S x a s e₁ S' hbd
  refine ⟨q', T', S', h', g', x', e,
    hproper', hroot', hodo', hext', hocc', ?_, hx', hxb', ?_, hcard,
    hcent, ?_, ?_⟩
  · intro z
    exact hcell' z
  · intro b
    refine ⟨hcurvature b.1 b.2, hfp b.1 b.2, hbd b.1 b.2⟩
  · exact hlap
  · rcases hclass' with ⟨hF, _⟩ | ⟨hrest, _⟩
    · exact Or.inl (by simpa [q'] using hF)
    · rcases hrest with ⟨hD, _⟩ | ⟨hG, _⟩
      · exact Or.inr (Or.inl (by simpa [q'] using hD))
      · exact Or.inr (Or.inr hG)

end ApollonianSuperharmonic

end
