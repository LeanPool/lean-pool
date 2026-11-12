/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandRegularTranslatePeriodicComplex
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIntersectionClassification
public import LeanPool.ApollonianSuperharmonic.RegularTileFamilyTranslationUnique
public import LeanPool.ApollonianSuperharmonic.TileBordering
public import LeanPool.ApollonianSuperharmonic.TileTouchingCovariance

-- [TABLET NODE: BandRegularTileTouchingClassification]

/-!
# BandRegularTileTouchingClassification

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandRegularTileTouchingClassification (C : BandCircle)
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hqC : q 0 = C.1.1) (T : ProtoTile) (hT : BandPrototile (q 0) T)
    (U V : ProtoTile) (hU : U ∈ RegularTileFamily T (TilingLattice C))
    (hV : V ∈ RegularTileFamily T (TilingLattice C)) :
    TileTouching U V ↔
      ∃ j : Fin 3,
        TileCentroid V - TileCentroid U =
            GaussianRealPoint (BandVectors.1 (q j.succ) (q 0)) ∨
          TileCentroid V - TileCentroid U =
            -GaussianRealPoint (BandVectors.1 (q j.succ) (q 0)) := by
-- BODY
  have boundaryEdge_mem_footprintEdges (S : ProtoTile)
      (e : Finset GaussianInt) (he : e ∈ BoundaryFootprintEdges S) :
      e ∈ FootprintEdges S := by
    rcases he with ⟨z, ⟨rfl, hz⟩ | ⟨rfl, hz⟩⟩
    · rcases hz with ⟨hz, _⟩ | ⟨_, hz⟩
      · exact ⟨z, hz, Or.inl rfl⟩
      · exact ⟨z - ⟨0, 1⟩, hz, Or.inr (Or.inr (Or.inr (by
          ext; simp [Zsqrtd.ext_iff])))⟩
    · rcases hz with ⟨hz, _⟩ | ⟨_, hz⟩
      · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
      · exact ⟨z - 1, hz, Or.inr (Or.inr (Or.inl (by
          ext; simp [Zsqrtd.ext_iff])))⟩
  have centroid_difference (x y : GaussianInt) :
      TileCentroid (TileTranslation T y) -
          TileCentroid (TileTranslation T x) =
        GaussianRealPoint (y - x) := by
    rw [(TileTranslationFormulas T y).2.2.2.2.1,
      (TileTranslationFormulas T x).2.2.2.2.1]
    ext <;> simp [GaussianRealPoint]
  have realPoint_injective : Function.Injective GaussianRealPoint := by
    intro x y hxy
    apply Zsqrtd.ext
    · have h := congrArg Prod.fst hxy
      dsimp [GaussianRealPoint] at h
      exact_mod_cast h
    · have h := congrArg Prod.snd hxy
      dsimp [GaussianRealPoint] at h
      exact_mod_cast h
  have translate_add (x y : GaussianInt) :
      TileTranslation (TileTranslation T x) y = TileTranslation T (x + y) := by
    cases T with
    | mk cells anchor =>
      apply congrArg₂ ProtoTile.mk
      · ext z
        simp [TileTranslation, GaussianTranslation, add_comm,
          add_left_comm]
      · simp [TileTranslation, GaussianTranslation, add_comm,
          add_left_comm]
  have translate_zero : TileTranslation T 0 = T := by
    cases T with
    | mk cells anchor =>
      apply congrArg₂ ProtoTile.mk
      · ext z
        simp [GaussianTranslation]
      · simp [GaussianTranslation]
  have touching_symm (A B : ProtoTile) : TileTouching A B → TileTouching B A := by
    rintro (h | h | h)
    · exact Or.inl ⟨h.2.1, h.1, h.2.2.1.symm, by
        simpa [Set.inter_comm] using h.2.2.2⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  have hpositive : 0 < (q 0).1 := (ProperBandCurvatureStructure q hq).1
  have harea := (BandTileSimultaneousInduction q hq T hT).2.1
  have hTnonempty : T.cells.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have : TileArea T = 0 := by simp [TileArea, hempty]
    rw [harea] at this
    have : 0 < Int.toNat (q 0).1 := by omega
    omega
  have translate_nonempty (x : GaussianInt) :
      (TileTranslation T x).cells.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    exact hTnonempty.ne_empty ((TileTranslationFormulas T x).2.2.1.mp hempty)
  obtain ⟨a, ha, _⟩ := RegularTileFamilyTranslationUnique T
    (TilingLattice C) U hU
  obtain ⟨b, hb, _⟩ := RegularTileFamilyTranslationUnique T
    (TilingLattice C) V hV
  rw [ha, hb]
  constructor
  · intro htouch
    have hborder : TileBordering (TileTranslation T a) (TileTranslation T b) := by
      rcases htouch with h | h | h
      · refine ⟨h.2.2.1, ?_⟩
        rcases h.2.2.2 with ⟨p, hp_nodup, hp_length, hp_vertices, hp_steps,
          hp_edges⟩
        cases p with
        | nil => simp at hp_length
        | cons x p =>
          cases p with
          | nil => simp at hp_length
          | cons y p =>
            refine ⟨{x, y}, ?_⟩
            rw [hp_edges]
            exact ⟨x, y, [], p, by simp⟩
      · exact False.elim ((translate_nonempty a).ne_empty h.1)
      · exact False.elim ((translate_nonempty b).ne_empty h.1)
    have hab : a ≠ b := by
      intro hab
      subst b
      have hempty : (TileTranslation T (a : GaussianInt)).cells = ∅ :=
        (Finset.disjoint_self_iff_empty _).mp hborder.1
      exact (translate_nonempty a).ne_empty hempty
    obtain ⟨P, _, htile, hadj, _, _, _, _, _⟩ :=
      BandRegularTranslatePeriodicComplex C q hq hqC T hT
    have hpAdjacent : P.plane.adjacent a b := by
      apply ((PeriodicTileIntersectionClassification P).1 a b hab).1.mp
      rcases hborder.2 with ⟨e, hea, heb⟩
      rw [htile a, htile b]
      exact ⟨e, boundaryEdge_mem_footprintEdges _ _ hea,
        boundaryEdge_mem_footprintEdges _ _ heb⟩
    rcases (hadj a b).mp hpAdjacent with ⟨j, hj | hj⟩
    · exact ⟨j, Or.inl (centroid_difference a b |>.trans (by rw [hj]))⟩
    · exact ⟨j, Or.inr (centroid_difference a b |>.trans (by
        rw [hj]
        ext <;> simp [GaussianRealPoint]))⟩
  · rintro ⟨j, hcentroid | hcentroid⟩
    · have hreal : GaussianRealPoint ((b : GaussianInt) - a) =
          GaussianRealPoint (BandVectors.1 (q j.succ) (q 0)) := by
        rw [← centroid_difference a b]
        exact hcentroid
      have hdiff : (b : GaussianInt) - a =
          BandVectors.1 (q j.succ) (q 0) := realPoint_injective hreal
      have hcurvature : 1 < (q 0).1 := by
        have hs := ProperBandCurvatureStructure q hq
        by_contra hn
        have hzero : ∀ k : Fin 3, (q k.succ).1 = 0 := by
          intro k
          have hnonnegative := hs.2.1 k
          have hsmaller := hq.2 k
          omega
        have heq := hs.2.2 (0 : Fin 3) (1 : Fin 3) (hzero 0) (hzero 1)
        norm_num at heq
      have hbase : TileTouching T
          (TileTranslation T (BandVectors.1 (q j.succ) (q 0))) :=
        ((BandTileSimultaneousInduction q hq T hT).2.2.2.2.1
          hcurvature j).1
      have htranslated :=
        ((TileTouchingCovariance T
          (TileTranslation T (BandVectors.1 (q j.succ) (q 0))) a).1).mp hbase
      have hb : BandVectors.1 (q j.succ) (q 0) + (a : GaussianInt) = b := by
        rw [← hdiff]
        abel
      simpa [translate_add, hb] using htranslated
    · have hnegative :
          -GaussianRealPoint (BandVectors.1 (q j.succ) (q 0)) =
            GaussianRealPoint (-BandVectors.1 (q j.succ) (q 0)) := by
        ext <;> simp [GaussianRealPoint]
      have hreal : GaussianRealPoint ((b : GaussianInt) - a) =
          GaussianRealPoint (-BandVectors.1 (q j.succ) (q 0)) := by
        rw [← centroid_difference a b, ← hnegative]
        exact hcentroid
      have hdiff : (b : GaussianInt) - a =
          -BandVectors.1 (q j.succ) (q 0) := realPoint_injective hreal
      have hcurvature : 1 < (q 0).1 := by
        have hs := ProperBandCurvatureStructure q hq
        by_contra hn
        have hzero : ∀ k : Fin 3, (q k.succ).1 = 0 := by
          intro k
          have hnonnegative := hs.2.1 k
          have hsmaller := hq.2 k
          omega
        have heq := hs.2.2 (0 : Fin 3) (1 : Fin 3) (hzero 0) (hzero 1)
        norm_num at heq
      have hbase : TileTouching T
          (TileTranslation T (BandVectors.1 (q j.succ) (q 0))) :=
        ((BandTileSimultaneousInduction q hq T hT).2.2.2.2.1
          hcurvature j).1
      have hback :=
        ((TileTouchingCovariance T
          (TileTranslation T (BandVectors.1 (q j.succ) (q 0)))
          (-BandVectors.1 (q j.succ) (q 0))).1).mp hbase
      have hnegativeBase : TileTouching T
          (TileTranslation T (-BandVectors.1 (q j.succ) (q 0))) := by
        apply touching_symm
        simpa [translate_add, translate_zero] using hback
      have htranslated :=
        ((TileTouchingCovariance T
          (TileTranslation T (-BandVectors.1 (q j.succ) (q 0))) a).1).mp
          hnegativeBase
      have hb : -BandVectors.1 (q j.succ) (q 0) + (a : GaussianInt) = b := by
        rw [← hdiff]
        abel
      simpa [translate_add, hb] using htranslated

end ApollonianSuperharmonic

end
