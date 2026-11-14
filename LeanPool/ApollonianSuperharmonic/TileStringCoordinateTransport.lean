/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.AffineTriangularStrip
public import LeanPool.ApollonianSuperharmonic.BandRegularTileTouchingClassification
public import LeanPool.ApollonianSuperharmonic.TileString

-- [TABLET NODE: TileStringCoordinateTransport]

/-!
# TileStringCoordinateTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace StringCoordinateGeometry

private theorem chart :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∃ a b : GaussianInt, 0 < a.re * b.im - a.im *
            b.re ∧ a ∈ TilingLattice C ∧ b ∈ TilingLattice C ∧ (∀ w : TilingLattice C, ∃! z : Int
            × Int, (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b = (w : GaussianInt)) ∧
            ((C.1.1.1 = 1 ∧ ((orientation = true ∧ a = 1 ∧ b = ⟨0, 1⟩) ∨ (orientation = false ∧ a
            = ⟨0, 1⟩ ∧ b = -1))) ∨ (1 < C.1.1.1 ∧ ∃ q : Fin 4 → CircleCoordinates,
            ProperBandQuadruple q ∧ q 0 = C.1.1 ∧ ((a = BandVectors.1 (q 1) (q 0) ∧ b =
            BandVectors.1 (q 2) (q 0)) ∨ (a = BandVectors.1 (q 2) (q 0) ∧ b = BandVectors.1 (q 1)
            (q 0))))) ) := by
  classical
  intro C orientation
  by_cases hc : C.1.1.1 = 1
  · let a : GaussianInt := if orientation then 1 else ⟨0, 1⟩
    let b : GaussianInt := if orientation then ⟨0, 1⟩ else -1
    have hdet : a.re * b.im - a.im * b.re = 1 := by
      cases orientation <;> simp [a, b]
    refine ⟨a, b, by omega, by simp [TilingLattice, hc],
      by simp [TilingLattice, hc], ?_, Or.inl ⟨hc, ?_⟩⟩
    · intro w
      cases ho : orientation
      · refine ⟨((w : GaussianInt).im, -(w : GaussianInt).re), ?_, ?_⟩
        · apply Zsqrtd.ext <;> simp [a, b, ho]
        · intro z hz
          have hr := congrArg Zsqrtd.re hz
          have hi := congrArg Zsqrtd.im hz
          simp [a, b, ho] at hr hi
          exact Prod.ext (by omega) (by omega)
      · refine ⟨((w : GaussianInt).re, (w : GaussianInt).im), ?_, ?_⟩
        · apply Zsqrtd.ext <;> simp [a, b, ho]
        · intro z hz
          have hr := congrArg Zsqrtd.re hz
          have hi := congrArg Zsqrtd.im hz
          simp only [Int.reduceNeg, ho, ↓reduceIte, mul_one, Zsqrtd.smul_val, mul_zero,
              Zsqrtd.re_add, Zsqrtd.re_intCast, add_zero, Zsqrtd.im_add, Zsqrtd.im_intCast,
              zero_add, a, b] at hr hi
          exact Prod.ext hr hi
    · cases ho : orientation <;> simp [a, b, ho]
  · obtain ⟨q, hsemi, hqC, hsmall, _⟩ := Or.resolve_left (BandGenealogy C) hc
    have hq : ProperBandQuadruple q := ⟨hsemi, by simpa [hqC] using hsmall⟩
    let a0 := BandVectors.1 (q 1) (q 0)
    let b0 := BandVectors.1 (q 2) (q 0)
    let d0 := BandVectors.1 (q 3) (q 0)
    have hbasis := TilingLatticeBasis C q hq hqC
    have hsum : a0 + b0 + d0 = 0 := by
      simpa [a0, b0, d0, Fin.sum_univ_succ, add_assoc] using
        (IncomingSuperbasisRelation q hq).1
    let successorQuad : Fin 4 → CircleCoordinates :=
      ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
          2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2), q 0, q 2, q 3]
    have hsuccessor : SemiProperQuadruple successorQuad := by
      simpa [successorQuad] using SemiProperQuadruple.successor hsemi
    have hdet32 : Int.natAbs (d0.re * b0.im - d0.im * b0.re) = C.1.1.1.natAbs := by
      simpa [successorQuad, d0, b0, hqC] using
        (VectorDeterminant successorQuad hsuccessor
          (by simpa [successorQuad, hqC] using C.2)).2
    have hdetneg : d0.re * b0.im - d0.im * b0.re =
        -(a0.re * b0.im - a0.im * b0.re) := by
      have hr := congrArg Zsqrtd.re hsum
      have hi := congrArg Zsqrtd.im hsum
      change a0.re + b0.re + d0.re = 0 at hr
      change a0.im + b0.im + d0.im = 0 at hi
      rw [show d0.re = -(a0.re + b0.re) by omega,
        show d0.im = -(a0.im + b0.im) by omega]
      ring
    have hdetnz : a0.re * b0.im - a0.im * b0.re ≠ 0 := by
      intro hz
      rw [hdetneg, hz] at hdet32
      have habs := Int.natAbs_pos.mpr C.2.ne'
      simp at hdet32
      omega
    have hcgt : 1 < C.1.1.1 := by have hp := C.2; omega
    by_cases hpositive : 0 < a0.re * b0.im - a0.im * b0.re
    · exact ⟨a0, b0, hpositive, hbasis.1, hbasis.2.1, hbasis.2.2.1,
        Or.inr ⟨hcgt, q, hq, hqC, Or.inl ⟨rfl, rfl⟩⟩⟩
    · have hpositive' : 0 < b0.re * a0.im - b0.im * a0.re := by
        have he : b0.re * a0.im - b0.im * a0.re =
            -(a0.re * b0.im - a0.im * b0.re) := by ring
        rw [he]
        omega
      refine ⟨b0, a0, hpositive', hbasis.2.1, hbasis.1, ?_,
        Or.inr ⟨hcgt, q, hq, hqC, Or.inr ⟨rfl, rfl⟩⟩⟩
      intro w
      obtain ⟨z, hz, hzu⟩ := hbasis.2.2.1 w
      refine ⟨(z.2, z.1), by simpa [a0, b0, add_comm] using hz, ?_⟩
      intro y hy
      have heq := hzu (y.2, y.1) (by simpa [a0, b0, add_comm] using hy)
      exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)

private theorem index_mem :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (a ∈ TilingLattice C) → ((b
            ∈ TilingLattice C) → (
        let index := fun z : Int × Int => (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b
        ∀ (z : Int × Int), index z ∈ TilingLattice C)) ) := by
  classical
  intro C a b ha hb index z
  apply (TilingLattice C).add_mem
  · simpa [zsmul_eq_mul] using (TilingLattice C).zsmul_mem ha z.1
  · simpa [zsmul_eq_mul] using (TilingLattice C).zsmul_mem hb z.2

private theorem index_inj :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (∀ (w : ↥(TilingLattice
            C)), ∃! z : ℤ × ℤ, (↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) * b = (↑w :
            GaussianInt)) → (
        let index := fun z : Int × Int => (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b
        (∀ (z : Int × Int), index z ∈ TilingLattice C) → (Function.Injective index)) ) := by
  classical
  intro C a b hcoord index index_mem x y hxy
  obtain ⟨z, hz, hu⟩ := hcoord ⟨index y, index_mem y⟩
  exact (hu x hxy).trans (hu y rfl).symm

private theorem translation_inj :
    (by
      classical
      exact
        ∀ (base : ProtoTile), Function.Injective (TileTranslation base) ) := by
  classical
  intro base x y hxy
  have h := congrArg ProtoTile.anchor hxy
  change base.anchor + x = base.anchor + y at h
  exact add_left_cancel h

private theorem family :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (∀ (w
            : ↥(TilingLattice C)), ∃! z : ℤ × ℤ, (↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt)
            * b = (↑w : GaussianInt)) → (
        let index := fun z : Int × Int => (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b
        let tileAt := fun z : Int × Int => TileTranslation base (index z)
        (∀ (z : Int × Int), index z ∈ TilingLattice C) → ((Function.Injective (TileTranslation
            base)) → (∀ (U : ProtoTile), U ∈ RegularTileFamily base (TilingLattice C) ↔ ∃! z :
            Int × Int, U = tileAt z))) ) := by
  classical
  intro C base a b hcoord index tileAt index_mem translation_inj U
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨z, hz, hzu⟩ := hcoord ⟨u, hu⟩
    refine ⟨z, (congrArg (TileTranslation base) hz).symm, ?_⟩
    intro y hy
    exact hzu y (translation_inj hy.symm)
  · rintro ⟨z, hz, _⟩
    exact ⟨index z, index_mem z, hz⟩


private theorem index_sub :
    (by
      classical
      exact
        ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let index := fun z : Int × Int => (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b
        ∀ (x : Int × Int), ∀ (y : Int × Int), index (y - x) = index y - index x ) := by
  classical
  intro a b index x y
  dsimp [index, Prod.sub_def]
  push_cast
  ring

private theorem difference :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let index := fun z : Int × Int => (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b
        let tileAt := fun z : Int × Int => TileTranslation base (index z)
        (∀ (z : Int × Int), TileCentroid (tileAt z) = ((TileCentroid base).1 + ((index z).re :
            Int), (TileCentroid base).2 + ((index z).im : Int))) → ((∀ (x : Int × Int), ∀ (y :
            Int × Int), index (y - x) = index y - index x) → (∀ (x : Int × Int), ∀ (y : Int ×
            Int), TileCentroid (tileAt y) - TileCentroid (tileAt x) = GaussianRealPoint (index (y
            - x)))) ) := by
  classical
  intro base a b index tileAt centroid index_sub x y
  rw [centroid, centroid, index_sub]
  ext <;> simp [GaussianRealPoint]

private theorem adj :
    (by
      classical
      exact
        ∀ (C : BandCircle),
          ∀ (orientation : Bool),
            ∀ (base : ProtoTile),
              BandPrototile C.1.1 base →
                ∀ (a : GaussianInt),
                  ∀ (b : GaussianInt),
                    (0 : ℤ) < a.re * b.im - a.im * b.re →
                      (∀ (w : ↥(TilingLattice C)),
                          ∃! z : ℤ × ℤ,
                            (↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) * b =
                              (↑w : GaussianInt)) →
                        (C.1.1.1 = (1 : ℤ) ∧
                              (orientation = true ∧
                                a = (1 : GaussianInt) ∧
                                b = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨
                                orientation = false ∧
                                a = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∧
                                b = (-1 : GaussianInt)) ∨
                            (1 : ℤ) < C.1.1.1 ∧
                              ∃ (q : Fin (4 : ℕ) → CircleCoordinates),
                                ProperBandQuadruple q ∧
                                q (0 : Fin (4 : ℕ)) = C.1.1 ∧
                                (a =
                                BandVectors.1 (q (1 : Fin (4 : ℕ)))
                                (q (0 : Fin (4 : ℕ))) ∧
                                b =
                                BandVectors.1 (q (2 : Fin (4 : ℕ)))
                                (q (0 : Fin (4 : ℕ))) ∨
                                a =
                                BandVectors.1 (q (2 : Fin (4 : ℕ)))
                                (q (0 : Fin (4 : ℕ))) ∧
                                b =
                                BandVectors.1 (q (1 : Fin (4 : ℕ)))
                                (q (0 : Fin (4 : ℕ))))) →
                          let index := fun z : Int × Int =>
                            (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b;
                          let tileAt := fun z : Int × Int =>
                            TileTranslation base (index z);
                          let adjacent := fun T U : ProtoTile =>
                            if C.1.1.1 = 1 then
                              ∃ v : GaussianInt,
                                UnitTriangularStep orientation v ∧
                                TileCentroid U - TileCentroid T = GaussianRealPoint v
                            else TileTouching T U;
                          Function.Injective index →
                            (∀ (U : ProtoTile),
                                U ∈ RegularTileFamily base (TilingLattice C) ↔
                                ∃! z : Int × Int, U = tileAt z) →
                              (∀ (z : Int × Int),
                                tileAt z ∈ RegularTileFamily base (TilingLattice C)) →
                                Function.Injective GaussianRealPoint →
                                (∀ (x : Int × Int),
                                ∀ (y : Int × Int), index (y - x) = index y - index x) →
                                (∀ (x : Int × Int),
                                ∀ (y : Int × Int),
                                TileCentroid (tileAt y) - TileCentroid (tileAt x) =
                                GaussianRealPoint (index (y - x))) →
                                ∀ (x : Int × Int),
                                ∀ (y : Int × Int),
                                adjacent (tileAt x) (tileAt y) ↔
                                TriangularLatticeAdjacent x y
    ) := by
  classical
  intro C orientation base hbase a b hdet hcoord hsource index tileAt adjacent index_inj family
      tile_mem point_inj index_sub difference x y
  rw [show adjacent (tileAt x) (tileAt y) =
    (if C.1.1.1 = 1 then ∃ v : GaussianInt, UnitTriangularStep orientation v ∧
      TileCentroid (tileAt y) - TileCentroid (tileAt x) = GaussianRealPoint v
    else TileTouching (tileAt x) (tileAt y)) from rfl]
  rcases hsource with ⟨hc, hs⟩ | ⟨hc, q, hq, hqC, hs⟩
  · rw [ite_eq_left hc, difference]
    rcases hs with ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ <;>
      simp [index, UnitTriangularStep, GaussianRealPoint, ho]
    all_goals simp only [TriangularLatticeAdjacent, Prod.sub_def, Prod.mk.injEq]
    all_goals norm_cast
    all_goals omega
  · rw [ite_eq_right (by omega)]
    rw [BandRegularTileTouchingClassification C q hq hqC base
      (by simpa [hqC] using hbase) (tileAt x) (tileAt y) (tile_mem x) (tile_mem y)]
    have hsum := (IncomingSuperbasisRelation q hq).1
    have hd : BandVectors.1 (q 3) (q 0) = -(a + b) := by
      simp only [Fin.sum_univ_succ] at hsum
      rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> dsimp at hsum ⊢ <;> linear_combination hsum
    have hneg (v : GaussianInt) : -GaussianRealPoint v = GaussianRealPoint (-v) := by
      ext <;> simp [GaussianRealPoint]
    have heq (z : Int × Int) :
        (TileCentroid (tileAt y) - TileCentroid (tileAt x) = GaussianRealPoint (index z)) ↔
          y - x = z := by
      rw [difference, point_inj.eq_iff, index_inj.eq_iff]
    have hsteps : (∃ j : Fin 3,
        TileCentroid (tileAt y) - TileCentroid (tileAt x) =
            GaussianRealPoint (BandVectors.1 (q j.succ) (q 0)) ∨
        TileCentroid (tileAt y) - TileCentroid (tileAt x) =
            -GaussianRealPoint (BandVectors.1 (q j.succ) (q 0))) ↔
      (TileCentroid (tileAt y) - TileCentroid (tileAt x) = GaussianRealPoint a ∨
        TileCentroid (tileAt y) - TileCentroid (tileAt x) = GaussianRealPoint b ∨
        TileCentroid (tileAt y) - TileCentroid (tileAt x) = GaussianRealPoint (-(a + b)) ∨
        TileCentroid (tileAt y) - TileCentroid (tileAt x) = GaussianRealPoint (-a) ∨
        TileCentroid (tileAt y) - TileCentroid (tileAt x) = GaussianRealPoint (-b) ∨
        TileCentroid (tileAt y) - TileCentroid (tileAt x) = GaussianRealPoint (a + b)) := by
      simp only [Fin.exists_fin_succ, hneg]
      rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hd] <;> tauto
    rw [hsteps]
    have h1 : index (1, 0) = a := by simp [index]
    have h2 : index (0, 1) = b := by simp [index]
    have h3 : index (-1, -1) = -(a + b) := by simp [index, neg_add_rev, add_comm]
    have h4 : index (-1, 0) = -a := by simp [index]
    have h5 : index (0, -1) = -b := by simp [index]
    have h6 : index (1, 1) = a + b := by simp [index]
    rw [← h3, ← h4, ← h5, ← h6, ← h1, ← h2]
    simp only [heq, TriangularLatticeAdjacent]

private theorem height :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let index := fun z : Int × Int => (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b
        let tileAt := fun z : Int × Int => TileTranslation base (index z)
        (∀ (z : Int × Int), TileCentroid (tileAt z) = ((TileCentroid base).1 + ((index z).re :
            Int), (TileCentroid base).2 + ((index z).im : Int))) → (∀ (x : Int × Int), ∀ (y : Int
            × Int), ∀ (z : Int × Int), ((TileCentroid (tileAt z)).2 - (TileCentroid (tileAt
            x)).2) * ((TileCentroid (tileAt y)).1 - (TileCentroid (tileAt x)).1) - ((TileCentroid
            (tileAt z)).1 - (TileCentroid (tileAt x)).1) * ((TileCentroid (tileAt y)).2 -
            (TileCentroid (tileAt x)).2) = ((a.re * b.im - a.im * b.re : Int) : Real) *
            TriangularSignedHeight x y z) ) := by
  classical
  intro base a b index tileAt centroid x y z
  rw [centroid, centroid, centroid]
  simp [index, TriangularSignedHeight]
  ring

private theorem map_occurrence :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let index := fun z : Int × Int => (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b
        let tileAt := fun z : Int × Int => TileTranslation base (index z)
        ∀ (xs : List (Int × Int)), ∀ (pre : List ProtoTile), ∀ (T : ProtoTile), ∀ (post : List
            ProtoTile), (xs.map tileAt = pre ++ T :: post) → (∃ left z right, xs = left ++ z ::
            right ∧ pre = left.map tileAt ∧ T = tileAt z ∧ post = right.map tileAt) ) := by
  classical
  intro base a b index tileAt xs pre T post h
  induction pre generalizing xs with
  | nil =>
      cases xs with
      | nil => simp at h
      | cons z rest =>
          have hh : tileAt z = T ∧ rest.map tileAt = post := by simpa using h
          exact ⟨[], z, rest, rfl, rfl, hh.1.symm, hh.2.symm⟩
  | cons U pre ih =>
      cases xs with
      | nil => simp at h
      | cons z rest =>
          have hh : tileAt z = U ∧ rest.map tileAt = pre ++ T :: post := by
            simpa using h
          obtain ⟨left, x, right, hx, hp, ht, hs⟩ := ih rest hh.2
          exact ⟨z :: left, x, right, by simp [hx],
            by simp [hp, hh.1], ht, hs⟩

private theorem map_interior :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let index := fun z : Int × Int => (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b
        let tileAt := fun z : Int × Int => TileTranslation base (index z)
        (∀ (xs : List (Int × Int)), ∀ (pre : List ProtoTile), ∀ (T : ProtoTile), ∀ (post : List
            ProtoTile), (xs.map tileAt = pre ++ T :: post) → (∃ left z right, xs = left ++ z ::
            right ∧ pre = left.map tileAt ∧ T = tileAt z ∧ post = right.map tileAt)) → (∀ (P :
            ProtoTile → Prop), ∀ (xs : List (Int × Int)), (∀ pre, ∀ T, ∀ post, xs.map tileAt =
            pre ++ T :: post → pre ≠ [] → post ≠ [] → P T) ↔ (∀ pre, ∀ z, ∀ post, xs = pre ++ z
            :: post → pre ≠ [] → post ≠ [] → P (tileAt z))) ) := by
  classical
  intro base a b index tileAt map_occurrence P xs
  constructor
  · intro h pre z post he hp ht
    apply h (pre.map tileAt) (tileAt z) (post.map tileAt)
    · simp [he]
    · simpa using hp
    · simpa using ht
  · intro h pre T post he hp ht
    obtain ⟨left, z, right, hx, hl, hz, hr⟩ := map_occurrence xs pre T post he
    rw [hz]
    apply h left z right hx
    · intro hn
      simp [hl, hn] at hp
    · intro hn
      simp [hr, hn] at ht

private theorem internal_strip :
    (by
      classical
      exact
        GaussianInt →
          ∀ (r : ℤ × ℤ),
            ∀ (s : ℤ × ℤ),
              ∀ (xs : List (Int × Int)),
                TriangularStripSegment r s xs ↔
                  xs.head? = some r ∧
                    xs.getLast? = some s ∧
                      xs.Nodup ∧
                        xs.IsChain TriangularLatticeAdjacent ∧
                          ∀ pre,
                            ∀ z,
                              ∀ post,
                                xs = pre ++ z :: post →
                                pre ≠ [] →
                                post ≠ [] →
                                0 ≤ TriangularSignedHeight r s z ∧
                                ∃ u,
                                TriangularLatticeAdjacent z u ∧
                                TriangularSignedHeight r s u < 0
    ) := by
  classical
  intro a r s xs
  by_cases hrs : r = s
  · subst s
    constructor
    · intro h
      have hx : xs = [r] := by simpa [TriangularStripSegment] using h
      subst xs
      refine ⟨by simp, by simp, by simp, List.isChain_singleton r, ?_⟩
      intro pre z post he hp ht
      have hl := congrArg List.length he
      simp at hl
      have hpl : 0 < pre.length := by
        cases pre with
        | nil => simp at hp
        | cons a tail => simp
      omega
    · rintro ⟨hh, ht, hn, hc, hi⟩
      have hne : xs ≠ [] := by intro he; simp [he] at hh
      have hhead : xs.head hne = r := by
        simpa only [List.head?_eq_some_head hne, Option.some.injEq] using hh
      have hlast : xs.getLast hne = r := by
        simpa only [List.getLast?_eq_some_getLast hne, Option.some.injEq] using ht
      obtain ⟨z, hz⟩ := (List.Nodup.head_eq_getLast_iff hne hn).mp
        (hhead.trans hlast.symm)
      have hzr : z = r := by simpa [hz] using hh
      simp [TriangularStripSegment, hz, hzr]
  · obtain ⟨hM, hcross, _⟩ := AffineTriangularStrip.2 r s hrs
    constructor
    · intro h
      simp only [TriangularStripSegment, ite_eq_right hrs] at h
      refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2, ?_⟩
      intro pre z post he hp ht
      apply (hcross z).mpr
      exact h.2.2.2.1 z (by simp [he])
    · rintro ⟨hh, ht, hn, hc, hi⟩
      simp only [TriangularStripSegment, ite_eq_right hrs]
      refine ⟨hh, ht, hn, ?_, hc⟩
      intro z hz
      obtain ⟨pre, post, he⟩ := List.mem_iff_append.mp hz
      by_cases hp : pre = []
      · have hzr : z = r := by simpa [he, hp] using hh
        subst z
        simpa [TriangularBoundaryStrip, TriangularSignedHeight] using hM
      by_cases ht' : post = []
      · have hzs : z = s := by simpa [he, ht'] using ht
        subst z
        simpa [TriangularBoundaryStrip, TriangularSignedHeight, mul_comm] using hM
      exact (hcross z).mp (hi pre z post he hp ht')

private theorem nonnegative :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let index := fun z : Int × Int => (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b
        let tileAt := fun z : Int × Int => TileTranslation base (index z)
        (∀ (x : Int × Int), ∀ (y : Int × Int), ∀ (z : Int × Int), ((TileCentroid (tileAt z)).2 -
            (TileCentroid (tileAt x)).2) * ((TileCentroid (tileAt y)).1 - (TileCentroid (tileAt
            x)).1) - ((TileCentroid (tileAt z)).1 - (TileCentroid (tileAt x)).1) * ((TileCentroid
            (tileAt y)).2 - (TileCentroid (tileAt x)).2) = ((a.re * b.im - a.im * b.re : Int) :
            Real) * TriangularSignedHeight x y z) → (∀ (r : ℤ × ℤ), ∀ (s : ℤ × ℤ),
        let physical := fun T : ProtoTile =>
          ((TileCentroid T).2 - (TileCentroid (tileAt r)).2) *
              ((TileCentroid (tileAt s)).1 - (TileCentroid (tileAt r)).1) -
            ((TileCentroid T).1 - (TileCentroid (tileAt r)).1) *
              ((TileCentroid (tileAt s)).2 - (TileCentroid (tileAt r)).2)
        ((0 : Real) < ((a.re * b.im - a.im * b.re : Int) : Real)) → (∀ (z : Int × Int), 0 ≤
            physical (tileAt z) ↔ 0 ≤ TriangularSignedHeight r s z)) ) := by
  classical
  intro base a b index tileAt height r s physical hdetReal z
  dsimp only [physical]
  rw [height, mul_nonneg_iff_of_pos_left hdetReal]
  norm_cast

private theorem negative :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let index := fun z : Int × Int => (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b
        let tileAt := fun z : Int × Int => TileTranslation base (index z)
        ∀ (r : ℤ × ℤ), ∀ (s : ℤ × ℤ),
        let physical := fun T : ProtoTile =>
          ((TileCentroid T).2 - (TileCentroid (tileAt r)).2) *
              ((TileCentroid (tileAt s)).1 - (TileCentroid (tileAt r)).1) -
            ((TileCentroid T).1 - (TileCentroid (tileAt r)).1) *
              ((TileCentroid (tileAt s)).2 - (TileCentroid (tileAt r)).2)
        (∀ (z : Int × Int), 0 ≤ physical (tileAt z) ↔ 0 ≤ TriangularSignedHeight r s z) → (∀ (z :
            Int × Int), physical (tileAt z) < 0 ↔ TriangularSignedHeight r s z < 0) ) := by
  classical
  intro base a b index tileAt r s physical nonnegative z
  rw [← not_le, ← not_le, nonnegative]

private theorem interior_point :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀
            (b : GaussianInt),
        let index := fun z : Int × Int => (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b
        let tileAt := fun z : Int × Int => TileTranslation base (index z)
        let adjacent := fun T U : ProtoTile =>
          if C.1.1.1 = 1 then
            ∃ v : GaussianInt, UnitTriangularStep orientation v ∧
              TileCentroid U - TileCentroid T = GaussianRealPoint v
          else TileTouching T U
        (∀ (U : ProtoTile), U ∈ RegularTileFamily base (TilingLattice C) ↔ ∃! z : Int × Int, U =
            tileAt z) → ((∀ (z : Int × Int), tileAt z ∈ RegularTileFamily base (TilingLattice C))
            → ((∀ (x : Int × Int), ∀ (y : Int × Int), adjacent (tileAt x) (tileAt y) ↔
            TriangularLatticeAdjacent x y) → (∀ (r : ℤ × ℤ), ∀ (s : ℤ × ℤ),
        let physical := fun T : ProtoTile =>
          ((TileCentroid T).2 - (TileCentroid (tileAt r)).2) *
              ((TileCentroid (tileAt s)).1 - (TileCentroid (tileAt r)).1) -
            ((TileCentroid T).1 - (TileCentroid (tileAt r)).1) *
              ((TileCentroid (tileAt s)).2 - (TileCentroid (tileAt r)).2)
        (∀ (z : Int × Int), 0 ≤ physical (tileAt z) ↔ 0 ≤ TriangularSignedHeight r s z) → ((∀ (z
            : Int × Int), physical (tileAt z) < 0 ↔ TriangularSignedHeight r s z < 0) → (∀ (z :
            Int × Int), (0 ≤ physical (tileAt z) ∧ ∃ U ∈ RegularTileFamily base (TilingLattice
            C), adjacent (tileAt z) U ∧ physical U < 0) ↔ (0 ≤ TriangularSignedHeight r s z ∧ ∃
            u, TriangularLatticeAdjacent z u ∧ TriangularSignedHeight r s u < 0)))))) ) := by
  classical
  intro C orientation base a b index tileAt adjacent family tile_mem adj r s physical nonnegative
      negative z
  rw [nonnegative]
  constructor
  · rintro ⟨hz, U, hU, hzu, hneg⟩
    obtain ⟨u, rfl, _⟩ := (family U).mp hU
    exact ⟨hz, u, (adj z u).mp hzu, (negative u).mp hneg⟩
  · rintro ⟨hz, u, hzu, hneg⟩
    exact ⟨hz, tileAt u, tile_mem u, (adj z u).mpr hzu, (negative u).mpr hneg⟩

private theorem head_iff :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let index := fun z : Int × Int => (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b
        let tileAt := fun z : Int × Int => TileTranslation base (index z)
        (Function.Injective tileAt) → (∀ (r : ℤ × ℤ), ∀ (xs : List (Int × Int)), (xs.map
            tileAt).head? = some (tileAt r) ↔ xs.head? = some r) ) := by
  classical
  intro base a b index tileAt tile_inj r xs
  rw [List.head?_map]
  simpa only [Option.map_some] using
    (Option.map_injective tile_inj).eq_iff (a := xs.head?) (b := some r)

private theorem last_iff :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let index := fun z : Int × Int => (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b
        let tileAt := fun z : Int × Int => TileTranslation base (index z)
        (Function.Injective tileAt) → (∀ (s : ℤ × ℤ), ∀ (xs : List (Int × Int)), (xs.map
            tileAt).getLast? = some (tileAt s) ↔ xs.getLast? = some s) ) := by
  classical
  intro base a b index tileAt tile_inj s xs
  rw [List.getLast?_map]
  simpa only [Option.map_some] using
    (Option.map_injective tile_inj).eq_iff (a := xs.getLast?) (b := some s)

private theorem distinct_iff :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let index := fun z : Int × Int => (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b
        let tileAt := fun z : Int × Int => TileTranslation base (index z)
        (Function.Injective tileAt) → (∀ (xs : List (Int × Int)), (xs.map tileAt).Pairwise (fun T
            U => T ≠ U) ↔ xs.Nodup) ) := by
  classical
  intro base a b index tileAt tile_inj xs
  simp only [List.pairwise_map, ne_eq, tile_inj.eq_iff, ← List.nodup_iff_pairwise_ne]

private theorem chain_iff :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀
            (b : GaussianInt),
        let index := fun z : Int × Int => (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b
        let tileAt := fun z : Int × Int => TileTranslation base (index z)
        let adjacent := fun T U : ProtoTile =>
          if C.1.1.1 = 1 then
            ∃ v : GaussianInt, UnitTriangularStep orientation v ∧
              TileCentroid U - TileCentroid T = GaussianRealPoint v
          else TileTouching T U
        (∀ (x : Int × Int), ∀ (y : Int × Int), adjacent (tileAt x) (tileAt y) ↔
            TriangularLatticeAdjacent x y) → (∀ (xs : List (Int × Int)), (xs.map tileAt).IsChain
            adjacent ↔ xs.IsChain TriangularLatticeAdjacent) ) := by
  classical
  intro C orientation base a b index tileAt adjacent adj xs
  simp only [List.isChain_map, adj]

private theorem map_family :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let index := fun z : Int × Int => (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b
        let tileAt := fun z : Int × Int => TileTranslation base (index z)
        (∀ (z : Int × Int), tileAt z ∈ RegularTileFamily base (TilingLattice C)) → (∀ (xs : List
            (Int × Int)), ∀ T ∈ xs.map tileAt, T ∈ RegularTileFamily base (TilingLattice C)) ) := by
  classical
  intro C base a b index tileAt tile_mem xs T hT
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hT
  exact tile_mem z

private theorem mapped_string :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), (BandPrototile C.1.1
            base) → (∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let index := fun z : Int × Int => (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b
        let tileAt := fun z : Int × Int => TileTranslation base (index z)
        let adjacent := fun T U : ProtoTile =>
          if C.1.1.1 = 1 then
            ∃ v : GaussianInt, UnitTriangularStep orientation v ∧
              TileCentroid U - TileCentroid T = GaussianRealPoint v
          else TileTouching T U
        ∀ (r : ℤ × ℤ), ∀ (s : ℤ × ℤ), (∀ (P : ProtoTile → Prop), ∀ (xs : List (Int × Int)), (∀
            pre, ∀ T, ∀ post, xs.map tileAt = pre ++ T :: post → pre ≠ [] → post ≠ [] → P T) ↔ (∀
            pre, ∀ z, ∀ post, xs = pre ++ z :: post → pre ≠ [] → post ≠ [] → P (tileAt z))) → ((∀
            (xs : List (Int × Int)), TriangularStripSegment r s xs ↔ xs.head? = some r ∧
            xs.getLast? = some s ∧ xs.Nodup ∧ xs.IsChain TriangularLatticeAdjacent ∧ (∀ pre, ∀ z,
            ∀ post, xs = pre ++ z :: post → pre ≠ [] → post ≠ [] → 0 ≤ TriangularSignedHeight r s
            z ∧ ∃ u, TriangularLatticeAdjacent z u ∧ TriangularSignedHeight r s u < 0)) → (
        let physical := fun T : ProtoTile =>
          ((TileCentroid T).2 - (TileCentroid (tileAt r)).2) *
              ((TileCentroid (tileAt s)).1 - (TileCentroid (tileAt r)).1) -
            ((TileCentroid T).1 - (TileCentroid (tileAt r)).1) *
              ((TileCentroid (tileAt s)).2 - (TileCentroid (tileAt r)).2)
        (∀ (z : Int × Int), (0 ≤ physical (tileAt z) ∧ ∃ U ∈ RegularTileFamily base
            (TilingLattice C), adjacent (tileAt z) U ∧ physical U < 0) ↔ (0 ≤
            TriangularSignedHeight r s z ∧ ∃ u, TriangularLatticeAdjacent z u ∧
            TriangularSignedHeight r s u < 0)) → ((∀ (xs : List (Int × Int)), (xs.map
            tileAt).head? = some (tileAt r) ↔ xs.head? = some r) → ((∀ (xs : List (Int × Int)),
            (xs.map tileAt).getLast? = some (tileAt s) ↔ xs.getLast? = some s) → ((∀ (xs : List
            (Int × Int)), (xs.map tileAt).Pairwise (fun T U => T ≠ U) ↔ xs.Nodup) → ((∀ (xs :
            List (Int × Int)), (xs.map tileAt).IsChain adjacent ↔ xs.IsChain
            TriangularLatticeAdjacent) → ((∀ (xs : List (Int × Int)), ∀ T ∈ xs.map tileAt, T ∈
            RegularTileFamily base (TilingLattice C)) → (∀ (xs : List (Int × Int)), TileString C
            orientation base (tileAt r) (tileAt s) (xs.map tileAt) ↔ TriangularStripSegment r s
            xs))))))))) ) := by
  classical
  intro C orientation base hbase a b index tileAt adjacent r s map_interior internal_strip
      physical interior_point head_iff last_iff distinct_iff chain_iff map_family xs
  rw [internal_strip]
  change (BandPrototile C.1.1 base ∧
    (xs.map tileAt).head? = some (tileAt r) ∧
    (xs.map tileAt).getLast? = some (tileAt s) ∧
    (xs.map tileAt).Pairwise (fun T U => T ≠ U) ∧
    (∀ T ∈ xs.map tileAt, T ∈ RegularTileFamily base (TilingLattice C)) ∧
    (xs.map tileAt).IsChain adjacent ∧
    ∀ pre T post, xs.map tileAt = pre ++ T :: post → pre ≠ [] → post ≠ [] →
      0 ≤ physical T ∧ ∃ U ∈ RegularTileFamily base (TilingLattice C),
        adjacent T U ∧ physical U < 0) ↔ _
  rw [head_iff, last_iff, distinct_iff, chain_iff, map_interior]
  simp only [hbase, true_and, interior_point]
  constructor
  · rintro ⟨hh, hl, hn, hf, hc, hi⟩
    exact ⟨hh, hl, hn, hc, hi⟩
  · rintro ⟨hh, hl, hn, hc, hi⟩
    exact ⟨hh, hl, hn, map_family xs, hc, hi⟩

private theorem decode :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let index := fun z : Int × Int => (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b
        let tileAt := fun z : Int × Int => TileTranslation base (index z)
        ∀ (ys : List ProtoTile), ∀ (zs : List (Int × Int)), List.Forall₂ (fun T z => T = tileAt
            z) ys zs ↔ ys = zs.map tileAt ) := by
  classical
  intro base a b index tileAt ys zs
  rw [← List.forall₂_map_right_iff, List.forall₂_eq_eq_eq]

private theorem map_decode :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let index := fun z : Int × Int => (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b
        let tileAt := fun z : Int × Int => TileTranslation base (index z)
        (∀ (U : ProtoTile), U ∈ RegularTileFamily base (TilingLattice C) ↔ ∃! z : Int × Int, U =
            tileAt z) → (∀ (ys : List ProtoTile), (∀ T ∈ ys, T ∈ RegularTileFamily base
            (TilingLattice C)) → (∃ xs : List (Int × Int), ys = xs.map tileAt)) ) := by
  classical
  intro C base a b index tileAt family ys hy
  induction ys with
  | nil => exact ⟨[], rfl⟩
  | cons T rest ih =>
      obtain ⟨z, hz, _⟩ := (family T).mp (hy T (by simp))
      obtain ⟨zs, hzs⟩ := ih (fun U hU => hy U (by simp [hU]))
      exact ⟨z :: zs, by simp [hz, hzs]⟩

end StringCoordinateGeometry

theorem TileStringCoordinateTransport (C : BandCircle) (orientation : Bool)
    (base : ProtoTile)
    (hbase : BandPrototile C.1.1 base) :
    ∃ a b : GaussianInt,
      0 < a.re * b.im - a.im * b.re ∧
      a ∈ TilingLattice C ∧ b ∈ TilingLattice C ∧
      (∀ w : TilingLattice C, ∃! z : Int × Int,
        (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b =
          (w : GaussianInt)) ∧
      ((C.1.1.1 = 1 ∧
          ((orientation = true ∧ a = 1 ∧ b = ⟨0, 1⟩) ∨
            (orientation = false ∧ a = ⟨0, 1⟩ ∧ b = -1))) ∨
        (1 < C.1.1.1 ∧
          ∃ q : Fin 4 → CircleCoordinates,
            ProperBandQuadruple q ∧ q 0 = C.1.1 ∧
              ((a = BandVectors.1 (q 1) (q 0) ∧
                  b = BandVectors.1 (q 2) (q 0)) ∨
                (a = BandVectors.1 (q 2) (q 0) ∧
                  b = BandVectors.1 (q 1) (q 0))))) ∧
      let tileAt := fun z : Int × Int =>
        TileTranslation base
          ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
      let tileAdjacent := fun T U : ProtoTile =>
        if C.1.1.1 = 1 then
          ∃ v : GaussianInt,
            UnitTriangularStep orientation v ∧
            TileCentroid U - TileCentroid T = GaussianRealPoint v
        else TileTouching T U
      (∀ U : ProtoTile,
        U ∈ RegularTileFamily base (TilingLattice C) ↔
          ∃! z : Int × Int, U = tileAt z) ∧
      (∀ x y : Int × Int,
        tileAdjacent (tileAt x) (tileAt y) ↔
          TriangularLatticeAdjacent x y) ∧
      (∀ x y z : Int × Int,
        ((TileCentroid (tileAt z)).2 - (TileCentroid (tileAt x)).2) *
              ((TileCentroid (tileAt y)).1 - (TileCentroid (tileAt x)).1) -
            ((TileCentroid (tileAt z)).1 - (TileCentroid (tileAt x)).1) *
              ((TileCentroid (tileAt y)).2 - (TileCentroid (tileAt x)).2) =
          ((a.re * b.im - a.im * b.re : Int) : Real) *
            TriangularSignedHeight x y z) ∧
      ∀ (R S : ProtoTile) (tiles : List ProtoTile) (r s : Int × Int),
        R = tileAt r → S = tileAt s →
        (TileString C orientation base R S tiles ↔
          ∃! coordinates : List (Int × Int),
            List.Forall₂ (fun T z => T = tileAt z) tiles coordinates ∧
              TriangularStripSegment r s coordinates) := by
-- BODY
  classical
  have chart : ∃ a b : GaussianInt,
      0 < a.re * b.im - a.im * b.re ∧
      a ∈ TilingLattice C ∧ b ∈ TilingLattice C ∧
      (∀ w : TilingLattice C, ∃! z : Int × Int,
        (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b = (w : GaussianInt)) ∧
      ((C.1.1.1 = 1 ∧
          ((orientation = true ∧ a = 1 ∧ b = ⟨0, 1⟩) ∨
            (orientation = false ∧ a = ⟨0, 1⟩ ∧ b = -1))) ∨
        (1 < C.1.1.1 ∧ ∃ q : Fin 4 → CircleCoordinates,
          ProperBandQuadruple q ∧ q 0 = C.1.1 ∧
            ((a = BandVectors.1 (q 1) (q 0) ∧ b = BandVectors.1 (q 2) (q 0)) ∨
              (a = BandVectors.1 (q 2) (q 0) ∧ b = BandVectors.1 (q 1) (q 0))))) :=
                  StringCoordinateGeometry.chart C orientation
  obtain ⟨a, b, hdet, ha, hb, hcoord, hsource⟩ := chart
  let index := fun z : Int × Int => (z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b
  let tileAt := fun z : Int × Int => TileTranslation base (index z)
  let adjacent := fun T U : ProtoTile =>
    if C.1.1.1 = 1 then
      ∃ v : GaussianInt, UnitTriangularStep orientation v ∧
        TileCentroid U - TileCentroid T = GaussianRealPoint v
    else TileTouching T U
  have index_mem (z : Int × Int) : index z ∈ TilingLattice C :=
      StringCoordinateGeometry.index_mem C a b ha hb z
  have index_inj : Function.Injective index := StringCoordinateGeometry.index_inj C a b hcoord
      index_mem
  have translation_inj : Function.Injective (TileTranslation base) :=
      StringCoordinateGeometry.translation_inj base
  have tile_inj : Function.Injective tileAt := translation_inj.comp index_inj
  have family (U : ProtoTile) : U ∈ RegularTileFamily base (TilingLattice C) ↔
      ∃! z : Int × Int, U = tileAt z := StringCoordinateGeometry.family C base a b hcoord
          index_mem translation_inj U
  have tile_mem (z : Int × Int) : tileAt z ∈ RegularTileFamily base (TilingLattice C) :=
    ⟨index z, index_mem z, rfl⟩
  have point_inj : Function.Injective GaussianRealPoint := GaussianRealPointProperties.injective
  have centroid (z : Int × Int) : TileCentroid (tileAt z) =
      ((TileCentroid base).1 + ((index z).re : Int),
        (TileCentroid base).2 + ((index z).im : Int)) :=
    (TileTranslationFormulas base (index z)).2.2.2.2.1
  have index_sub (x y : Int × Int) : index (y - x) = index y - index x :=
      StringCoordinateGeometry.index_sub a b x y
  have difference (x y : Int × Int) :
      TileCentroid (tileAt y) - TileCentroid (tileAt x) = GaussianRealPoint (index (y - x)) :=
          StringCoordinateGeometry.difference base a b centroid index_sub x y
  have adj (x y : Int × Int) : adjacent (tileAt x) (tileAt y) ↔
      TriangularLatticeAdjacent x y := StringCoordinateGeometry.adj C orientation base hbase a b
          hdet hcoord hsource index_inj family tile_mem point_inj index_sub difference x y
  have height (x y z : Int × Int) :
      ((TileCentroid (tileAt z)).2 - (TileCentroid (tileAt x)).2) *
            ((TileCentroid (tileAt y)).1 - (TileCentroid (tileAt x)).1) -
          ((TileCentroid (tileAt z)).1 - (TileCentroid (tileAt x)).1) *
            ((TileCentroid (tileAt y)).2 - (TileCentroid (tileAt x)).2) =
        ((a.re * b.im - a.im * b.re : Int) : Real) * TriangularSignedHeight x y z :=
            StringCoordinateGeometry.height base a b centroid x y z
  refine ⟨a, b, hdet, ha, hb, hcoord, hsource, family, adj, height, ?_⟩
  intro R S tiles r s hr hs
  subst R
  subst S
  have map_occurrence (xs : List (Int × Int)) (pre : List ProtoTile)
      (T : ProtoTile) (post : List ProtoTile)
      (h : xs.map tileAt = pre ++ T :: post) :
      ∃ left z right, xs = left ++ z :: right ∧ pre = left.map tileAt ∧
        T = tileAt z ∧ post = right.map tileAt := StringCoordinateGeometry.map_occurrence base a
            b xs pre T post h
  have map_interior (P : ProtoTile → Prop) (xs : List (Int × Int)) :
      (∀ pre T post, xs.map tileAt = pre ++ T :: post →
        pre ≠ [] → post ≠ [] → P T) ↔
      (∀ pre z post, xs = pre ++ z :: post →
        pre ≠ [] → post ≠ [] → P (tileAt z)) := StringCoordinateGeometry.map_interior base a b
            map_occurrence P xs
  have internal_strip (xs : List (Int × Int)) :
      TriangularStripSegment r s xs ↔
        xs.head? = some r ∧ xs.getLast? = some s ∧ xs.Nodup ∧
        xs.IsChain TriangularLatticeAdjacent ∧
        (∀ pre z post, xs = pre ++ z :: post → pre ≠ [] → post ≠ [] →
          0 ≤ TriangularSignedHeight r s z ∧
            ∃ u, TriangularLatticeAdjacent z u ∧ TriangularSignedHeight r s u < 0) :=
                StringCoordinateGeometry.internal_strip a r s xs
  let physical := fun T : ProtoTile =>
    ((TileCentroid T).2 - (TileCentroid (tileAt r)).2) *
        ((TileCentroid (tileAt s)).1 - (TileCentroid (tileAt r)).1) -
      ((TileCentroid T).1 - (TileCentroid (tileAt r)).1) *
        ((TileCentroid (tileAt s)).2 - (TileCentroid (tileAt r)).2)
  have hdetReal : (0 : Real) < ((a.re * b.im - a.im * b.re : Int) : Real) := by
    exact_mod_cast hdet
  have nonnegative (z : Int × Int) :
      0 ≤ physical (tileAt z) ↔ 0 ≤ TriangularSignedHeight r s z :=
          StringCoordinateGeometry.nonnegative base a b height r s hdetReal z
  have negative (z : Int × Int) :
      physical (tileAt z) < 0 ↔ TriangularSignedHeight r s z < 0 :=
          StringCoordinateGeometry.negative base a b r s nonnegative z
  have interior_point (z : Int × Int) :
      (0 ≤ physical (tileAt z) ∧
        ∃ U ∈ RegularTileFamily base (TilingLattice C),
          adjacent (tileAt z) U ∧ physical U < 0) ↔
      (0 ≤ TriangularSignedHeight r s z ∧
        ∃ u, TriangularLatticeAdjacent z u ∧ TriangularSignedHeight r s u < 0) :=
            StringCoordinateGeometry.interior_point C orientation base a b family tile_mem adj r
            s nonnegative negative z
  have head_iff (xs : List (Int × Int)) :
      (xs.map tileAt).head? = some (tileAt r) ↔ xs.head? = some r :=
          StringCoordinateGeometry.head_iff base a b tile_inj r xs
  have last_iff (xs : List (Int × Int)) :
      (xs.map tileAt).getLast? = some (tileAt s) ↔ xs.getLast? = some s :=
          StringCoordinateGeometry.last_iff base a b tile_inj s xs
  have distinct_iff (xs : List (Int × Int)) :
      (xs.map tileAt).Pairwise (fun T U => T ≠ U) ↔ xs.Nodup :=
          StringCoordinateGeometry.distinct_iff base a b tile_inj xs
  have chain_iff (xs : List (Int × Int)) :
      (xs.map tileAt).IsChain adjacent ↔ xs.IsChain TriangularLatticeAdjacent :=
          StringCoordinateGeometry.chain_iff C orientation base a b adj xs
  have map_family (xs : List (Int × Int)) :
      ∀ T ∈ xs.map tileAt, T ∈ RegularTileFamily base (TilingLattice C) :=
          StringCoordinateGeometry.map_family C base a b tile_mem xs
  have mapped_string (xs : List (Int × Int)) :
      TileString C orientation base (tileAt r) (tileAt s) (xs.map tileAt) ↔
        TriangularStripSegment r s xs := StringCoordinateGeometry.mapped_string C orientation
            base hbase a b r s map_interior internal_strip interior_point head_iff last_iff
            distinct_iff chain_iff map_family xs
  have decode (ys : List ProtoTile) (zs : List (Int × Int)) :
      List.Forall₂ (fun T z => T = tileAt z) ys zs ↔ ys = zs.map tileAt :=
          StringCoordinateGeometry.decode base a b ys zs
  have map_decode (ys : List ProtoTile)
      (hy : ∀ T ∈ ys, T ∈ RegularTileFamily base (TilingLattice C)) :
      ∃ xs : List (Int × Int), ys = xs.map tileAt := StringCoordinateGeometry.map_decode C base a
          b family ys hy
  constructor
  · intro ht
    obtain ⟨xs, hxs⟩ := map_decode tiles ht.2.2.2.2.1
    refine ⟨xs, ⟨(decode tiles xs).mpr hxs, ?_⟩, ?_⟩
    · exact (mapped_string xs).mp (by simpa [hxs] using ht)
    · intro ys hy
      exact List.map_injective_iff.mpr tile_inj
        (((decode tiles ys).mp hy.1).symm.trans hxs)
  · rintro ⟨xs, ⟨hd, hstrip⟩, _⟩
    rw [(decode tiles xs).mp hd]
    exact (mapped_string xs).mpr hstrip

end ApollonianSuperharmonic

end
