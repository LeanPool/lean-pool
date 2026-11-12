/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PeriodicTileMultiplicityOne
public import LeanPool.ApollonianSuperharmonic.BandRegularTranslatePeriodicComplex
public import LeanPool.ApollonianSuperharmonic.BandRegularTileTouchingClassification
public import LeanPool.ApollonianSuperharmonic.BandTileSimultaneousInduction
public import LeanPool.ApollonianSuperharmonic.IncomingSuperbasisRelation
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIntersectionClassification
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.TileBordering
public import LeanPool.ApollonianSuperharmonic.RegularTileFamily
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.TilingLatticeBasis

-- [TABLET NODE: BandTileTopologyApplication]

/-!
# BandTileTopologyApplication

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TileTopologyGeometry

private theorem family_eq :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), (∀
            (u : ↥(TilingLattice C)), P.tile u = TileTranslation T (↑u : GaussianInt)) →
            (RegularTileFamily T (TilingLattice C) = Set.range P.tile) ) := by
  classical
  intro C T P htile
  ext U
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, htile ⟨u, hu⟩⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u.1, u.2, htile u⟩

private theorem edge_in_footprint :
    (by
      classical
      exact
        ∀ (S : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges S) → (e ∈
            FootprintEdges S) ) := by
  classical
  intro S e he
  rcases he with ⟨z, ⟨rfl, hz⟩ | ⟨rfl, hz⟩⟩
  · rcases hz with ⟨hz, _⟩ | ⟨_, hz⟩
    · exact ⟨z, hz, Or.inl rfl⟩
    · exact ⟨z - ⟨0, 1⟩, hz, Or.inr (Or.inr (Or.inr (by
        ext; simp [Zsqrtd.ext_iff])))⟩
  · rcases hz with ⟨hz, _⟩ | ⟨_, hz⟩
    · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
    · exact ⟨z - 1, hz, Or.inr (Or.inr (Or.inl (by
        ext; simp [Zsqrtd.ext_iff])))⟩

private theorem centroid_difference :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), TileCentroid
            (TileTranslation T y) - TileCentroid (TileTranslation T x) = GaussianRealPoint (y -
            x) ) := by
  classical
  intro T x y
  rw [(TileTranslationFormulas T y).2.2.2.2.1,
    (TileTranslationFormulas T x).2.2.2.2.1]
  ext <;> simp [GaussianRealPoint]

private theorem translate_zero :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), (BandPrototile
            (q (0 : Fin (4 : ℕ))) T) → (∀ (P : PeriodicTileComplex ↥(TilingLattice C)), (∀ (u :
            ↥(TilingLattice C)), P.tile u = TileTranslation T (↑u : GaussianInt)) → (∀ [
            Nonempty (AffineTriangularComplexChart P fun (mn : ℤ × ℤ) => TileTranslation T
            ((↑mn.1 : GaussianInt) * BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) +
            (↑mn.2 : GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)))))],
            (RegularTileFamily T (TilingLattice C) = Set.range P.tile) → ((∀ (x : GaussianInt), ∀
            (y : GaussianInt), TileCentroid (TileTranslation T y) - TileCentroid (TileTranslation
            T x) = GaussianRealPoint (y - x)) → (TileTranslation T 0 = T)))) ) := by
  classical
  intro C q T hT P htile hchart family_eq centroid_difference
  cases T with
  | mk cells anchor =>
    apply congrArg₂ ProtoTile.mk
    · ext z
      simp [GaussianTranslation]
    · simp [GaussianTranslation]

private theorem realPoint_injective :
    (by
      classical
      exact
        Function.Injective GaussianRealPoint ) := by
  classical
  intro x y hxy
  apply Zsqrtd.ext
  · have h := congrArg Prod.fst hxy
    dsimp [GaussianRealPoint] at h
    exact_mod_cast h
  · have h := congrArg Prod.snd hxy
    dsimp [GaussianRealPoint] at h
    exact_mod_cast h

private theorem hnonempty :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile),
            (PeriodicTileComplex ↥(TilingLattice C)) → ((0 < (q 0).1) → ((TileArea T = (q (0 :
            Fin (4 : ℕ))).1.toNat) → (∀ (x : GaussianInt), (TileTranslation T
            x).cells.Nonempty))) ) := by
  classical
  intro C q T P hpositive harea x
  rw [Finset.nonempty_iff_ne_empty]
  intro he
  have hz : TileArea T = 0 := by
    have := (TileTranslationFormulas T x).2.2.1.mp he
    simp [TileArea, this]
  rw [harea] at hz
  have hp : 0 < Int.toNat (q 0).1 := by omega
  omega

private theorem border_touch :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), (BandPrototile
            (q (0 : Fin (4 : ℕ))) T) → (∀ (P : PeriodicTileComplex ↥(TilingLattice C)), (∀ (u :
            ↥(TilingLattice C)), P.tile u = TileTranslation T (↑u : GaussianInt)) → (∀ [
            Nonempty (AffineTriangularComplexChart P fun (mn : ℤ × ℤ) => TileTranslation T
            ((↑mn.1 : GaussianInt) * BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) +
            (↑mn.2 : GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)))))],
            (RegularTileFamily T (TilingLattice C) = Set.range P.tile) → ((∀ (x : GaussianInt), ∀
            (y : GaussianInt), TileCentroid (TileTranslation T y) - TileCentroid (TileTranslation
            T x) = GaussianRealPoint (y - x)) → ((TileTranslation T 0 = T) → ((TileArea T = (q (0
            : Fin (4 : ℕ))).1.toNat) → ((∀ (x : GaussianInt), (TileTranslation T
            x).cells.Nonempty) → (∀ (U : ProtoTile), (U ∈ RegularTileFamily T (TilingLattice C))
            → ((U ≠ T) → (TileTouching T U → TileBordering T U))))))))) ) := by
  classical
  intro C q T hT P htile hchart family_eq centroid_difference translate_zero harea hnonempty U hU
      hneq
  obtain ⟨a, ha, hua⟩ := RegularTileFamilyTranslationUnique T
    (TilingLattice C) U hU
  have hUform : U = TileTranslation T (a : GaussianInt) := ha
  have ha0 : a ≠ 0 := by
    intro hz
    apply hneq
    rw [hUform, hz]
    cases T with
    | mk cells anchor =>
      apply congrArg₂ ProtoTile.mk
      · ext z
        simp [GaussianTranslation]
      · simp [GaussianTranslation]
  rw [hUform]
  intro ht
  rcases ht with ht | ht | ht
  · exact ⟨ht.2.2.1, by
      rcases ht.2.2.2 with ⟨p, hp, hl, hvtx, hstep, hed⟩
      cases p with
      | nil => simp at hl
      | cons x p =>
        cases p with
        | nil => simp at hl
        | cons y p =>
          refine ⟨{x, y}, ?_⟩
          rw [hed]
          exact ⟨x, y, [], p, by simp⟩⟩
  · exact False.elim ((hnonempty 0).ne_empty (by simpa [translate_zero] using ht.1))
  · exact False.elim ((hnonempty (a : GaussianInt)).ne_empty ht.1)

private theorem border_iff_index :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → ((q (0 :
            Fin (4 : ℕ)) = C.1.1) → (∀ (T : ProtoTile), (BandPrototile (q (0 : Fin (4 : ℕ))) T) →
            (∀ (P : PeriodicTileComplex ↥(TilingLattice C)), (∀ (u : ↥(TilingLattice C)), P.tile
            u = TileTranslation T (↑u : GaussianInt)) → ((∀ (u : ↥(TilingLattice C)), ∀ (v :
            ↥(TilingLattice C)), P.plane.adjacent u v ↔ ∃ (j : Fin (3 : ℕ)), (↑v : GaussianInt) -
            (↑u : GaussianInt) = BandVectors.1 (q j.succ) (q (0 : Fin (4 : ℕ))) ∨ (↑v :
            GaussianInt) - (↑u : GaussianInt) = -BandVectors.1 (q j.succ) (q (0 : Fin (4 : ℕ))))
            → ((∀ (S : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges S) →
            (e ∈ FootprintEdges S)) → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), TileCentroid
            (TileTranslation T y) - TileCentroid (TileTranslation T x) = GaussianRealPoint (y -
            x)) → ((TileTranslation T 0 = T) → ((∀ (U : ProtoTile), (U ∈ RegularTileFamily T
            (TilingLattice C)) → ((U ≠ T) → (TileTouching T U → TileBordering T U))) → (∀ (a :
            TilingLattice C), (a ≠ 0) → (TileBordering T (P.tile a) ↔ ∃ j : Fin 3, (a :
            GaussianInt) = BandVectors.1 (q j.succ) (q 0) ∨ (a : GaussianInt) = -BandVectors.1 (q
            j.succ) (q 0))))))))))) ) := by
  classical
  intro C q hq hqC T hT P htile hadj edge_in_footprint centroid_difference translate_zero
      border_touch a ha0
  have hmem : P.tile a ∈ RegularTileFamily T (TilingLattice C) :=
    ⟨a.1, a.2, htile a⟩
  have hneq : P.tile a ≠ T := by
    intro heq
    have := congrArg TileCentroid heq
    rw [htile a, (TileTranslationFormulas T (a : GaussianInt)).2.2.2.2.1] at this
    have hr := congrArg Prod.fst this
    have hi := congrArg Prod.snd this
    dsimp at hr hi
    have hz : (a : GaussianInt) = 0 := by
      apply Zsqrtd.ext
      · have hh : (((a : GaussianInt).re : Int) : Real) = 0 := by linarith
        exact_mod_cast hh
      · have hh : (((a : GaussianInt).im : Int) : Real) = 0 := by linarith
        exact_mod_cast hh
    exact ha0 (Subtype.ext hz)
  constructor
  · intro hb
    have hcommon : (FootprintEdges (P.tile 0) ∩ FootprintEdges (P.tile a)).Nonempty := by
      rcases hb.2 with ⟨e, heT, heU⟩
      have he0 : e ∈ FootprintEdges (P.tile 0) := by
        simpa [htile 0, translate_zero] using edge_in_footprint T e heT
      exact ⟨e, he0,
        edge_in_footprint (P.tile a) e heU⟩
    have hadj0 := ((PeriodicTileIntersectionClassification P).1 0 a
      (by intro h; exact ha0 (Subtype.ext (by simpa using h.symm)))).1.mp hcommon
    rcases (hadj 0 a).mp hadj0 with ⟨j, hj | hj⟩
    · exact ⟨j, Or.inl (by simpa using hj)⟩
    · exact ⟨j, Or.inr (by simpa using hj)⟩
  · rintro ⟨j, hj | hj⟩
    · apply border_touch (P.tile a) hmem hneq
      apply (BandRegularTileTouchingClassification C q hq hqC T hT T
        (P.tile a) ⟨0, (TilingLattice C).zero_mem, translate_zero.symm⟩ hmem).2
      refine ⟨j, Or.inl ?_⟩
      have hc := centroid_difference 0 (a : GaussianInt)
      rw [sub_zero, hj] at hc
      simpa [htile a, translate_zero, hj] using hc
    · apply border_touch (P.tile a) hmem hneq
      apply (BandRegularTileTouchingClassification C q hq hqC T hT T
        (P.tile a) ⟨0, (TilingLattice C).zero_mem, translate_zero.symm⟩ hmem).2
      refine ⟨j, Or.inr ?_⟩
      have hc := centroid_difference 0 (a : GaussianInt)
      rw [sub_zero, hj] at hc
      simpa [htile a, translate_zero, hj, GaussianRealPoint] using hc

private theorem hcAt267 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (∑ j : Fin (3 : ℕ), BandVectors.1 (q j.succ) (q (0 :
            Fin (4 : ℕ))) = (0 : GaussianInt) ∧ ∑ j : Fin (3 : ℕ), BandVectors.2 (q j.succ) (q (0
            : Fin (4 : ℕ))) = (0 : GaussianInt)) → (BandVectors.1 (q 3) (q 0) = -BandVectors.1 (q
            1) (q 0) - BandVectors.1 (q 2) (q 0)) ) := by
  classical
  intro q hsum
  have hsum' := hsum.1
  simp? [Fin.sum_univ_succ] at hsum'
  have heq : BandVectors.1 (q 3) (q 0) =
      -(BandVectors.1 (q 1) (q 0) + BandVectors.1 (q 2) (q 0)) := by
    apply (eq_neg_iff_add_eq_zero).2
    convert hsum' using 1; abel
  convert heq using 1; abel

private theorem hcmem :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), (BandVectors.1 (q 1) (q 0) ∈
            TilingLattice C) → ((BandVectors.1 (q 2) (q 0) ∈ TilingLattice C) → ((BandVectors.1
            (q 3) (q 0) = -BandVectors.1 (q 1) (q 0) - BandVectors.1 (q 2) (q 0)) →
            (BandVectors.1 (q 3) (q 0) ∈ TilingLattice C))) ) := by
  classical
  intro C q ha hb hc
  rw [hc]
  exact (TilingLattice C).add_mem ((TilingLattice C).neg_mem ha)
    ((TilingLattice C).neg_mem hb)

private theorem coordinate_unique :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), (
        let a := BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)));
        let b := BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)));
        let u := BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ)));
        let v := BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)));
        let L := AddSubgroup.closure {u, v}; a ∈ TilingLattice C ∧ b ∈ TilingLattice C ∧ (∀ (w :
            ↥(TilingLattice C)), ∃! mn : ℤ × ℤ, (↑mn.1 : GaussianInt) * a + (↑mn.2 : GaussianInt)
            * b = (↑w : GaussianInt)) ∧ u ∈ L ∧ v ∈ L ∧ (∀ (z : GaussianInt), z ∈ L ↔ ∃ w ∈
            TilingLattice C, z = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * w) ∧ (∀ (w : ↥L), ∃! mn : ℤ
            × ℤ, (↑mn.1 : GaussianInt) * u + (↑mn.2 : GaussianInt) * v = (↑w : GaussianInt)) ∧ ∃
            (R : Finset GaussianInt), LatticeFundamentalSet L R ∧ R.card = C.1.1.1.natAbs) →
            ((BandVectors.1 (q 1) (q 0) ∈ TilingLattice C) → ((BandVectors.1 (q 2) (q 0) ∈
            TilingLattice C) → (∀ (m : Int × Int), ∀ (n : Int × Int), ((m.1 : GaussianInt) *
            BandVectors.1 (q 1) (q 0) +
            (m.2 : GaussianInt) * BandVectors.1 (q 2) (q 0) =
            (n.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
            (n.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)) → (m = n)))) ) := by
  classical
  intro C q hbasis ha hb m n hm
  have hu := (hbasis.2.2.1
    ⟨_, (TilingLattice C).add_mem
      ((TilingLattice C).zsmul_mem ha m.1)
      ((TilingLattice C).zsmul_mem hb m.2)⟩)
  apply hu.unique
  · simp [zsmul_eq_mul]
  · calc
      _ = (m.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
          (m.2 : GaussianInt) * BandVectors.1 (q 2) (q 0) := hm.symm
      _ = _ := by simp [zsmul_eq_mul]

private theorem vector_repr :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandVectors.1 (q 3) (q 0) = -BandVectors.1 (q 1) (q
            0) - BandVectors.1 (q 2) (q 0)) → (
        let vectors : Fin 6 → GaussianInt :=
          ![BandVectors.1 (q 1) (q 0), BandVectors.1 (q 2) (q 0),
            BandVectors.1 (q 3) (q 0), -BandVectors.1 (q 1) (q 0),
            -BandVectors.1 (q 2) (q 0), -BandVectors.1 (q 3) (q 0)]
        let coordinates : Fin 6 → Int × Int :=
          ![(1, 0), (0, 1), (-1, -1), (-1, 0), (0, -1), (1, 1)]
        ∀ (i : Fin 6), vectors i = (coordinates i).1 * BandVectors.1 (q 1) (q 0) + (coordinates
            i).2 * BandVectors.1 (q 2) (q 0)) ) := by
  classical
  intro q hc vectors coordinates i
  fin_cases i <;> simp [vectors, coordinates, hc] <;> ring

private theorem vector_injective :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let vectors : Fin 6 → GaussianInt :=
          ![BandVectors.1 (q 1) (q 0), BandVectors.1 (q 2) (q 0),
            BandVectors.1 (q 3) (q 0), -BandVectors.1 (q 1) (q 0),
            -BandVectors.1 (q 2) (q 0), -BandVectors.1 (q 3) (q 0)]
        let coordinates : Fin 6 → Int × Int :=
          ![(1, 0), (0, 1), (-1, -1), (-1, 0), (0, -1), (1, 1)]
        (∀ (m : Int × Int), ∀ (n : Int × Int), ((m.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
            (m.2 : GaussianInt) * BandVectors.1 (q 2) (q 0) = (n.1 : GaussianInt) * BandVectors.1
            (q 1) (q 0) + (n.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)) → (m = n)) → ((∀ (i :
            Fin 6), vectors i = (coordinates i).1 * BandVectors.1 (q 1) (q 0) + (coordinates i).2
            * BandVectors.1 (q 2) (q 0)) → (Function.Injective vectors)) ) := by
  classical
  intro q vectors coordinates coordinate_unique vector_repr i j hij
  have hcoord : coordinates i = coordinates j := by
    apply coordinate_unique
    rw [← vector_repr i, hij, vector_repr j]
  fin_cases i <;> fin_cases j <;> simp [coordinates] at hcoord ⊢

private theorem vector_mem :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), (BandVectors.1 (q 1) (q 0) ∈
            TilingLattice C) → ((BandVectors.1 (q 2) (q 0) ∈ TilingLattice C) → ((BandVectors.1
            (q 3) (q 0) ∈ TilingLattice C) → (
        let vectors : Fin 6 → GaussianInt :=
          ![BandVectors.1 (q 1) (q 0), BandVectors.1 (q 2) (q 0),
            BandVectors.1 (q 3) (q 0), -BandVectors.1 (q 1) (q 0),
            -BandVectors.1 (q 2) (q 0), -BandVectors.1 (q 3) (q 0)]
        ∀ (i : Fin 6), vectors i ∈ TilingLattice C))) ) := by
  classical
  intro C q ha hb hcmem vectors i
  fin_cases i
  · exact ha
  · exact hb
  · exact hcmem
  · exact (TilingLattice C).neg_mem ha
  · exact (TilingLattice C).neg_mem hb
  · exact (TilingLattice C).neg_mem hcmem

private theorem hzAt326 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (P :
            PeriodicTileComplex ↥(TilingLattice C)), (∀ (u : ↥(TilingLattice C)), P.tile u =
            TileTranslation T (↑u : GaussianInt)) → (
        let vectors : Fin 6 → GaussianInt :=
          ![BandVectors.1 (q 1) (q 0), BandVectors.1 (q 2) (q 0),
            BandVectors.1 (q 3) (q 0), -BandVectors.1 (q 1) (q 0),
            -BandVectors.1 (q 2) (q 0), -BandVectors.1 (q 3) (q 0)]
        ∀ (vector_mem : ∀ (i : Fin 6), vectors i ∈ TilingLattice C), ∀ (i : Fin (6 : ℕ)), (P.tile
            ⟨vectors i, vector_mem i⟩ = T) → (vectors i = 0)) ) := by
  classical
  intro C q T P htile vectors vector_mem i heqTile
  have hcq := congrArg TileCentroid heqTile
  rw [htile, (TileTranslationFormulas T (vectors i)).2.2.2.2.1] at hcq
  apply Zsqrtd.ext
  · have hh := congrArg Prod.fst hcq
    dsimp at hh
    exact_mod_cast (by linarith : (((vectors i).re : Int) : Real) = 0)
  · have hh := congrArg Prod.snd hcq
    dsimp at hh
    exact_mod_cast (by linarith : (((vectors i).im : Int) : Real) = 0)

private theorem hcoordAt336 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let vectors : Fin 6 → GaussianInt :=
          ![BandVectors.1 (q 1) (q 0), BandVectors.1 (q 2) (q 0),
            BandVectors.1 (q 3) (q 0), -BandVectors.1 (q 1) (q 0),
            -BandVectors.1 (q 2) (q 0), -BandVectors.1 (q 3) (q 0)]
        let coordinates : Fin 6 → Int × Int :=
          ![(1, 0), (0, 1), (-1, -1), (-1, 0), (0, -1), (1, 1)]
        (∀ (m : Int × Int), ∀ (n : Int × Int), ((m.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
            (m.2 : GaussianInt) * BandVectors.1 (q 2) (q 0) = (n.1 : GaussianInt) * BandVectors.1
            (q 1) (q 0) + (n.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)) → (m = n)) → ((∀ (i :
            Fin 6), vectors i = (coordinates i).1 * BandVectors.1 (q 1) (q 0) + (coordinates i).2
            * BandVectors.1 (q 2) (q 0)) → (∀ (i : Fin (6 : ℕ)), (vectors i = 0) → (coordinates i
            = (0, 0)))) ) := by
  classical
  intro q vectors coordinates coordinate_unique vector_repr i hz
  apply coordinate_unique
  rw [← vector_repr i, hz]
  simp

private theorem hnonzero :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates),
        let vectors : Fin 6 → GaussianInt :=
          ![BandVectors.1 (q 1) (q 0), BandVectors.1 (q 2) (q 0),
            BandVectors.1 (q 3) (q 0), -BandVectors.1 (q 1) (q 0),
            -BandVectors.1 (q 2) (q 0), -BandVectors.1 (q 3) (q 0)]
        let coordinates : Fin 6 → Int × Int :=
          ![(1, 0), (0, 1), (-1, -1), (-1, 0), (0, -1), (1, 1)]
        (∀ (m : Int × Int), ∀ (n : Int × Int), ((m.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
            (m.2 : GaussianInt) * BandVectors.1 (q 2) (q 0) = (n.1 : GaussianInt) * BandVectors.1
            (q 1) (q 0) + (n.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)) → (m = n)) → ((∀ (i :
            Fin 6), vectors i = (coordinates i).1 * BandVectors.1 (q 1) (q 0) + (coordinates i).2
            * BandVectors.1 (q 2) (q 0)) → (∀ (vector_mem : ∀ (i : Fin 6), vectors i ∈
            TilingLattice C), ∀ (i : Fin (6 : ℕ)), (⟨vectors i, vector_mem i⟩ : TilingLattice C)
            ≠ 0)) ) := by
  classical
  intro C q vectors coordinates coordinate_unique vector_repr vector_mem i hz
  have hz' := congrArg Subtype.val hz
  have hz'' : vectors i = 0 := by simpa using hz'
  have hcoord : coordinates i = (0, 0) := by
    apply coordinate_unique
    calc
      (coordinates i).1 * BandVectors.1 (q 1) (q 0) +
          (coordinates i).2 * BandVectors.1 (q 2) (q 0) = vectors i :=
        (vector_repr i).symm
      _ = 0 := hz''
      _ = (0 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
          (0 : GaussianInt) * BandVectors.1 (q 2) (q 0) := by simp
  fin_cases i <;> simp [coordinates] at hcoord

private theorem map_injective :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (P :
            PeriodicTileComplex ↥(TilingLattice C)), ∀ (htile : ∀ (u : ↥(TilingLattice C)),
            P.tile u = TileTranslation T (↑u : GaussianInt)), ∀ (border_iff_index : ∀ (a :
            TilingLattice C), (a ≠ 0) → (TileBordering T (P.tile a) ↔ ∃ j : Fin 3, (a :
            GaussianInt) = BandVectors.1 (q j.succ) (q 0) ∨ (a : GaussianInt) = -BandVectors.1 (q
            j.succ) (q 0))),
        let vectors : Fin 6 → GaussianInt :=
          ![BandVectors.1 (q 1) (q 0), BandVectors.1 (q 2) (q 0),
            BandVectors.1 (q 3) (q 0), -BandVectors.1 (q 1) (q 0),
            -BandVectors.1 (q 2) (q 0), -BandVectors.1 (q 3) (q 0)]
        let coordinates : Fin 6 → Int × Int :=
          ![(1, 0), (0, 1), (-1, -1), (-1, 0), (0, -1), (1, 1)]
        ∀ (coordinate_unique : ∀ (m : Int × Int), ∀ (n : Int × Int), ((m.1 : GaussianInt) *
            BandVectors.1 (q 1) (q 0) + (m.2 : GaussianInt) * BandVectors.1 (q 2) (q 0) = (n.1 :
            GaussianInt) * BandVectors.1 (q 1) (q 0) + (n.2 : GaussianInt) * BandVectors.1 (q 2)
            (q 0)) → (m = n)), ∀ (vector_repr : ∀ (i : Fin 6), vectors i = (coordinates i).1 *
            BandVectors.1 (q 1) (q 0) + (coordinates i).2 * BandVectors.1 (q 2) (q 0)),
                (Function.Injective vectors) → (∀ (vector_mem : ∀ (i : Fin 6), vectors i ∈
                TilingLattice C),
        let target : Type := {U : ProtoTile //
          U ∈ RegularTileFamily T (TilingLattice C) ∧ U ≠ T ∧ TileBordering T U}
        let map : Fin 6 → target := fun i =>
          ⟨P.tile ⟨vectors i, vector_mem i⟩, by
            refine ⟨⟨vectors i, vector_mem i, htile _⟩, ?_, ?_⟩
            · intro heq
              have heqTile : P.tile ⟨vectors i, vector_mem i⟩ = T := heq
              have hz : vectors i = 0 := by
                have hcq := congrArg TileCentroid heqTile
                rw [htile, (TileTranslationFormulas T (vectors i)).2.2.2.2.1] at hcq
                apply Zsqrtd.ext
                · have hh := congrArg Prod.fst hcq
                  dsimp at hh
                  exact_mod_cast (by linarith : (((vectors i).re : Int) : Real) = 0)
                · have hh := congrArg Prod.snd hcq
                  dsimp at hh
                  exact_mod_cast (by linarith : (((vectors i).im : Int) : Real) = 0)
              have hcoord : coordinates i = (0, 0) := by
                apply coordinate_unique
                rw [← vector_repr i, hz]
                simp
              fin_cases i <;> simp [coordinates] at hcoord
            · have hnonzero : (⟨vectors i, vector_mem i⟩ : TilingLattice C) ≠ 0 := by
                intro hz
                have hz' := congrArg Subtype.val hz
                have hz'' : vectors i = 0 := by simpa using hz'
                have hcoord : coordinates i = (0, 0) := by
                  apply coordinate_unique
                  calc
                    (coordinates i).1 * BandVectors.1 (q 1) (q 0) +
                        (coordinates i).2 * BandVectors.1 (q 2) (q 0) = vectors i :=
                      (vector_repr i).symm
                    _ = 0 := hz''
                    _ = (0 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
                        (0 : GaussianInt) * BandVectors.1 (q 2) (q 0) := by simp
                fin_cases i <;> simp [coordinates] at hcoord
              apply (border_iff_index ⟨vectors i, vector_mem i⟩ hnonzero).2
              fin_cases i
              · exact ⟨0, Or.inl rfl⟩
              · exact ⟨1, Or.inl rfl⟩
              · exact ⟨2, Or.inl rfl⟩
              · exact ⟨0, Or.inr rfl⟩
              · exact ⟨1, Or.inr rfl⟩
              · exact ⟨2, Or.inr rfl⟩
          ⟩
        Function.Injective map)) := by
  classical
  intro C q T P htile border_iff_index vectors coordinates coordinate_unique vector_repr
      vector_injective vector_mem target map i j hij
  have ht : P.tile ⟨vectors i, vector_mem i⟩ =
      P.tile ⟨vectors j, vector_mem j⟩ := congrArg Subtype.val hij
  have hu := RegularTileFamilyTranslationUnique T (TilingLattice C)
    (P.tile ⟨vectors j, vector_mem j⟩) (by
      exact (map j).property.1)
  have heq : (⟨vectors i, vector_mem i⟩ : TilingLattice C) =
      ⟨vectors j, vector_mem j⟩ := hu.unique
        (by simpa [htile] using ht.symm) (htile _)
  exact vector_injective (Subtype.ext_iff.mp heq)

private theorem map_surjective :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (P :
            PeriodicTileComplex ↥(TilingLattice C)), ∀ (htile : ∀ (u : ↥(TilingLattice C)),
            P.tile u = TileTranslation T (↑u : GaussianInt)), ∀ (translate_zero : TileTranslation
            T 0 = T), ∀ (border_iff_index : ∀ (a : TilingLattice C), (a ≠ 0) → (TileBordering T
            (P.tile a) ↔ ∃ j : Fin 3, (a : GaussianInt) = BandVectors.1 (q j.succ) (q 0) ∨ (a :
            GaussianInt) = -BandVectors.1 (q j.succ) (q 0))),
        let vectors : Fin 6 → GaussianInt :=
          ![BandVectors.1 (q 1) (q 0), BandVectors.1 (q 2) (q 0),
            BandVectors.1 (q 3) (q 0), -BandVectors.1 (q 1) (q 0),
            -BandVectors.1 (q 2) (q 0), -BandVectors.1 (q 3) (q 0)]
        let coordinates : Fin 6 → Int × Int :=
          ![(1, 0), (0, 1), (-1, -1), (-1, 0), (0, -1), (1, 1)]
        ∀ (coordinate_unique : ∀ (m : Int × Int), ∀ (n : Int × Int), ((m.1 : GaussianInt) *
            BandVectors.1 (q 1) (q 0) + (m.2 : GaussianInt) * BandVectors.1 (q 2) (q 0) = (n.1 :
            GaussianInt) * BandVectors.1 (q 1) (q 0) + (n.2 : GaussianInt) * BandVectors.1 (q 2)
            (q 0)) → (m = n)), ∀ (vector_repr : ∀ (i : Fin 6), vectors i = (coordinates i).1 *
            BandVectors.1 (q 1) (q 0) + (coordinates i).2 * BandVectors.1 (q 2) (q 0)), ∀
            (vector_mem : ∀ (i : Fin 6), vectors i ∈ TilingLattice C),
        let target : Type := {U : ProtoTile //
          U ∈ RegularTileFamily T (TilingLattice C) ∧ U ≠ T ∧ TileBordering T U}
        let map : Fin 6 → target := fun i =>
          ⟨P.tile ⟨vectors i, vector_mem i⟩, by
            refine ⟨⟨vectors i, vector_mem i, htile _⟩, ?_, ?_⟩
            · intro heq
              have heqTile : P.tile ⟨vectors i, vector_mem i⟩ = T := heq
              have hz : vectors i = 0 := by
                have hcq := congrArg TileCentroid heqTile
                rw [htile, (TileTranslationFormulas T (vectors i)).2.2.2.2.1] at hcq
                apply Zsqrtd.ext
                · have hh := congrArg Prod.fst hcq
                  dsimp at hh
                  exact_mod_cast (by linarith : (((vectors i).re : Int) : Real) = 0)
                · have hh := congrArg Prod.snd hcq
                  dsimp at hh
                  exact_mod_cast (by linarith : (((vectors i).im : Int) : Real) = 0)
              have hcoord : coordinates i = (0, 0) := by
                apply coordinate_unique
                rw [← vector_repr i, hz]
                simp
              fin_cases i <;> simp [coordinates] at hcoord
            · have hnonzero : (⟨vectors i, vector_mem i⟩ : TilingLattice C) ≠ 0 := by
                intro hz
                have hz' := congrArg Subtype.val hz
                have hz'' : vectors i = 0 := by simpa using hz'
                have hcoord : coordinates i = (0, 0) := by
                  apply coordinate_unique
                  calc
                    (coordinates i).1 * BandVectors.1 (q 1) (q 0) +
                        (coordinates i).2 * BandVectors.1 (q 2) (q 0) = vectors i :=
                      (vector_repr i).symm
                    _ = 0 := hz''
                    _ = (0 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
                        (0 : GaussianInt) * BandVectors.1 (q 2) (q 0) := by simp
                fin_cases i <;> simp [coordinates] at hcoord
              apply (border_iff_index ⟨vectors i, vector_mem i⟩ hnonzero).2
              fin_cases i
              · exact ⟨0, Or.inl rfl⟩
              · exact ⟨1, Or.inl rfl⟩
              · exact ⟨2, Or.inl rfl⟩
              · exact ⟨0, Or.inr rfl⟩
              · exact ⟨1, Or.inr rfl⟩
              · exact ⟨2, Or.inr rfl⟩
          ⟩
        Function.Surjective map ) := by
  classical
  intro C q T P htile translate_zero border_iff_index vectors coordinates coordinate_unique
      vector_repr vector_mem target map U
  obtain ⟨a, haU, hUa⟩ := RegularTileFamilyTranslationUnique T
    (TilingLattice C) U.1 U.property.1
  have translate_eq (i : Fin 6) (hi : vectors i = (a : GaussianInt)) :
      map i = U := by
    apply Subtype.ext
    dsimp [map]
    have hidx : (↑(⟨vectors i, vector_mem i⟩ : TilingLattice C) : GaussianInt) =
        (a : GaussianInt) := hi
    rw [htile, hidx, ← haU]
  have hUtile : P.tile a = U.1 := (htile a).trans haU.symm
  obtain ⟨j, hj | hj⟩ := (border_iff_index a (by
    intro hz
    apply U.property.2.1
    calc
      U.1 = TileTranslation T (a : GaussianInt) := haU
      _ = TileTranslation T 0 := by
        have hz' := congrArg Subtype.val hz
        rw [hz']
        rfl
      _ = T := translate_zero)).1 (by
        rw [hUtile]
        exact U.property.2.2)
  · fin_cases j
    · exact ⟨0, translate_eq 0 (by simpa [vectors] using hj.symm)⟩
    · exact ⟨1, translate_eq 1 (by simpa [vectors] using hj.symm)⟩
    · exact ⟨2, translate_eq 2 (by simpa [vectors] using hj.symm)⟩
  · fin_cases j
    · exact ⟨3, translate_eq 3 (by simpa [vectors] using hj.symm)⟩
    · exact ⟨4, translate_eq 4 (by simpa [vectors] using hj.symm)⟩
    · exact ⟨5, translate_eq 5 (by simpa [vectors] using hj.symm)⟩

end TileTopologyGeometry

theorem BandTileTopologyApplication (C : BandCircle)
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hqC : q 0 = C.1.1) (T : ProtoTile) (hT : BandPrototile (q 0) T) :
    ExactTileTiling (RegularTileFamily T (TilingLattice C)) ∧
      Nat.card {U : ProtoTile //
        U ∈ RegularTileFamily T (TilingLattice C) ∧ U ≠ T ∧
          TileBordering T U} = 6 := by
-- BODY
  classical
  obtain ⟨P, hPlattice, htile, hadj, hpos, hv, he, hf, hchart⟩ :=
    BandRegularTranslatePeriodicComplex C q hq hqC T hT
  have family_eq : RegularTileFamily T (TilingLattice C) = Set.range P.tile :=
      TileTopologyGeometry.family_eq C T P htile
  refine ⟨?_, ?_⟩
  · rw [family_eq]
    exact PeriodicTileMultiplicityOne P
  · have edge_in_footprint (S : ProtoTile) (e : Finset GaussianInt)
        (he : e ∈ BoundaryFootprintEdges S) : e ∈ FootprintEdges S :=
            TileTopologyGeometry.edge_in_footprint S e he
    have centroid_difference (x y : GaussianInt) :
        TileCentroid (TileTranslation T y) - TileCentroid (TileTranslation T x) =
          GaussianRealPoint (y - x) := TileTopologyGeometry.centroid_difference T x y
    have translate_zero : TileTranslation T 0 = T := @TileTopologyGeometry.translate_zero C q T hT
        P htile hchart family_eq centroid_difference
    have realPoint_injective : Function.Injective GaussianRealPoint :=
        TileTopologyGeometry.realPoint_injective
    have hpositive : 0 < (q 0).1 := (ProperBandCurvatureStructure q hq).1
    have harea := (BandTileSimultaneousInduction q hq T hT).2.1
    have hnonempty (x : GaussianInt) :
        (TileTranslation T x).cells.Nonempty := TileTopologyGeometry.hnonempty C q T P hpositive
            harea x
    have border_touch (U : ProtoTile) (hU : U ∈ RegularTileFamily T (TilingLattice C))
        (hneq : U ≠ T) : TileTouching T U → TileBordering T U :=
            @TileTopologyGeometry.border_touch C q T hT P htile hchart family_eq
            centroid_difference translate_zero harea hnonempty U hU hneq
    have border_iff_index (a : TilingLattice C) (ha0 : a ≠ 0) :
        TileBordering T (P.tile a) ↔
          ∃ j : Fin 3, (a : GaussianInt) = BandVectors.1 (q j.succ) (q 0) ∨
            (a : GaussianInt) = -BandVectors.1 (q j.succ) (q 0) :=
                TileTopologyGeometry.border_iff_index C q hq hqC T hT P htile hadj
                edge_in_footprint centroid_difference translate_zero border_touch a ha0
    have hbasis := TilingLatticeBasis C q hq hqC
    have ha : BandVectors.1 (q 1) (q 0) ∈ TilingLattice C := hbasis.1
    have hb : BandVectors.1 (q 2) (q 0) ∈ TilingLattice C := hbasis.2.1
    have hsum := IncomingSuperbasisRelation q hq
    have hc : BandVectors.1 (q 3) (q 0) =
        -BandVectors.1 (q 1) (q 0) - BandVectors.1 (q 2) (q 0) := TileTopologyGeometry.hcAt267 q
            hsum
    have hcmem : BandVectors.1 (q 3) (q 0) ∈ TilingLattice C := TileTopologyGeometry.hcmem C q ha
        hb hc
    let vectors : Fin 6 → GaussianInt :=
      ![BandVectors.1 (q 1) (q 0), BandVectors.1 (q 2) (q 0),
        BandVectors.1 (q 3) (q 0), -BandVectors.1 (q 1) (q 0),
        -BandVectors.1 (q 2) (q 0), -BandVectors.1 (q 3) (q 0)]
    let coordinates : Fin 6 → Int × Int :=
      ![(1, 0), (0, 1), (-1, -1), (-1, 0), (0, -1), (1, 1)]
    have coordinate_unique (m n : Int × Int)
        (hm : (m.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
          (m.2 : GaussianInt) * BandVectors.1 (q 2) (q 0) =
          (n.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
          (n.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)) : m = n :=
              TileTopologyGeometry.coordinate_unique C q hbasis ha hb m n hm
    have vector_repr (i : Fin 6) :
        vectors i = (coordinates i).1 * BandVectors.1 (q 1) (q 0) +
          (coordinates i).2 * BandVectors.1 (q 2) (q 0) := TileTopologyGeometry.vector_repr q hc i
    have vector_injective : Function.Injective vectors := TileTopologyGeometry.vector_injective q
        coordinate_unique vector_repr
    have vector_mem (i : Fin 6) : vectors i ∈ TilingLattice C := TileTopologyGeometry.vector_mem
        C q ha hb hcmem i
    let target : Type := {U : ProtoTile //
      U ∈ RegularTileFamily T (TilingLattice C) ∧ U ≠ T ∧ TileBordering T U}
    let map : Fin 6 → target := fun i =>
      ⟨P.tile ⟨vectors i, vector_mem i⟩, by
        refine ⟨⟨vectors i, vector_mem i, htile _⟩, ?_, ?_⟩
        · intro heq
          have heqTile : P.tile ⟨vectors i, vector_mem i⟩ = T := heq
          have hz : vectors i = 0 := TileTopologyGeometry.hzAt326 C q T P htile vector_mem i heqTile
          have hcoord : coordinates i = (0, 0) := TileTopologyGeometry.hcoordAt336 q
              coordinate_unique vector_repr i hz
          fin_cases i <;> simp [coordinates] at hcoord
        · have hnonzero : (⟨vectors i, vector_mem i⟩ : TilingLattice C) ≠ 0 :=
            TileTopologyGeometry.hnonzero C q coordinate_unique vector_repr vector_mem i
          apply (border_iff_index ⟨vectors i, vector_mem i⟩ hnonzero).2
          fin_cases i
          · exact ⟨0, Or.inl rfl⟩
          · exact ⟨1, Or.inl rfl⟩
          · exact ⟨2, Or.inl rfl⟩
          · exact ⟨0, Or.inr rfl⟩
          · exact ⟨1, Or.inr rfl⟩
          · exact ⟨2, Or.inr rfl⟩
      ⟩
    have map_injective : Function.Injective map := TileTopologyGeometry.map_injective C q T P
        htile border_iff_index coordinate_unique vector_repr vector_injective vector_mem
    have map_surjective : Function.Surjective map := TileTopologyGeometry.map_surjective C q T P
        htile translate_zero border_iff_index coordinate_unique vector_repr vector_mem
    change Nat.card target = 6
    rw [← Fintype.card_fin 6]
    simpa [Nat.card_eq_fintype_card] using
      (Nat.card_congr (Equiv.ofBijective map ⟨map_injective, map_surjective⟩)).symm

end ApollonianSuperharmonic

end
