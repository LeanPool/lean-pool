/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.P4339T1PrecursorSupportGeometry

-- [TABLET NODE: P4616T1OriginalMixedPaths]

/-!
# P4616T1OriginalMixedPaths

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4616T1OriginalMixedPaths
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T) :
    let U : Fin 6 → ProtoTile := ![cert.P 0 true, cert.P 0 true,
      cert.P 0 false, cert.P 0 false, cert.P 1 true, cert.P 1 false]
    let W : Fin 6 → ProtoTile := ![cert.P 1 false, cert.P 2 false,
      cert.P 1 true, cert.P 2 true, cert.P 2 false, cert.P 2 true]
    let K : Fin 6 → ProtoTile := ![cert.P 0 false, cert.P 1 true,
      cert.P 0 true, cert.P 1 false, cert.P 0 true, cert.P 0 false]
    let H : Fin 6 → ProtoTile := ![
      TileTranslation (cert.P 0 false) (cert.u + cert.v),
      TileTranslation (cert.P 0 false) cert.v,
      TileTranslation (cert.P 0 true) (-cert.u - cert.v),
      TileTranslation (cert.P 0 true) (-cert.v),
      TileTranslation (cert.P 1 false) (-cert.u),
      TileTranslation (cert.P 1 true) cert.u]
    let rho := fun f : PeriodicSubtileFaceIndex =>
      cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm f)
    let p : Fin 6 → GaussianInt := ![rho ⟨.I2, 0, 0⟩, rho ⟨.I3, 0, 0⟩,
      rho ⟨.I1, 0, 0⟩, rho ⟨.I4, 0, 0⟩, rho ⟨.I3, 0, 0⟩, rho ⟨.I4, 0, 0⟩]
    let l : Fin 6 → GaussianInt := ![rho ⟨.J4, 0, 0⟩, rho ⟨.J2, 0, 0⟩,
      rho ⟨.J3, -1, -1⟩, rho ⟨.J1, 0, -1⟩, rho ⟨.J8, 0, 0⟩,
      rho ⟨.J7, 1, 0⟩]
    ∀ k, SimpleGridPathBetween
        (FootprintVertices (U k) ∩ FootprintVertices (W k))
        (FootprintEdges (U k) ∩ FootprintEdges (W k)) (p k) (l k) ∧
      p k ∈ FootprintVertices (K k) ∧ l k ∈ FootprintVertices (H k) := by
-- BODY
  classical
  let U : Fin 6 → ProtoTile := ![cert.P 0 true, cert.P 0 true,
    cert.P 0 false, cert.P 0 false, cert.P 1 true, cert.P 1 false]
  let W : Fin 6 → ProtoTile := ![cert.P 1 false, cert.P 2 false,
    cert.P 1 true, cert.P 2 true, cert.P 2 false, cert.P 2 true]
  let K : Fin 6 → ProtoTile := ![cert.P 0 false, cert.P 1 true,
    cert.P 0 true, cert.P 1 false, cert.P 0 true, cert.P 0 false]
  let H : Fin 6 → ProtoTile := ![
    TileTranslation (cert.P 0 false) (cert.u + cert.v),
    TileTranslation (cert.P 0 false) cert.v,
    TileTranslation (cert.P 0 true) (-cert.u - cert.v),
    TileTranslation (cert.P 0 true) (-cert.v),
    TileTranslation (cert.P 1 false) (-cert.u),
    TileTranslation (cert.P 1 true) cert.u]
  let rho := fun f : PeriodicSubtileFaceIndex =>
    cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm f)
  let f : Fin 6 → PeriodicSubtileFaceIndex := ![⟨.I2, 0, 0⟩, ⟨.I3, 0, 0⟩,
    ⟨.I1, 0, 0⟩, ⟨.I4, 0, 0⟩, ⟨.I3, 0, 0⟩, ⟨.I4, 0, 0⟩]
  let g : Fin 6 → PeriodicSubtileFaceIndex := ![⟨.J4, 0, 0⟩, ⟨.J2, 0, 0⟩,
    ⟨.J3, -1, -1⟩, ⟨.J1, 0, -1⟩, ⟨.J8, 0, 0⟩, ⟨.J7, 1, 0⟩]
  let a : Fin 6 → PeriodicSubtileIndex := ![⟨.A, 0, 0⟩, ⟨.A, 0, 0⟩,
    ⟨.B, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.C, 0, 0⟩, ⟨.D, 0, 0⟩]
  let b : Fin 6 → PeriodicSubtileIndex := ![⟨.D, 0, 0⟩, ⟨.F, 0, 0⟩,
    ⟨.C, 0, 0⟩, ⟨.E, 0, 0⟩, ⟨.F, 0, 0⟩, ⟨.E, 0, 0⟩]
  let p : Fin 6 → GaussianInt := ![rho ⟨.I2, 0, 0⟩, rho ⟨.I3, 0, 0⟩,
    rho ⟨.I1, 0, 0⟩, rho ⟨.I4, 0, 0⟩, rho ⟨.I3, 0, 0⟩, rho ⟨.I4, 0, 0⟩]
  let l : Fin 6 → GaussianInt := ![rho ⟨.J4, 0, 0⟩, rho ⟨.J2, 0, 0⟩,
    rho ⟨.J3, -1, -1⟩, rho ⟨.J1, 0, -1⟩, rho ⟨.J8, 0, 0⟩,
    rho ⟨.J7, 1, 0⟩]
  change ∀ k, SimpleGridPathBetween
      (FootprintVertices (U k) ∩ FootprintVertices (W k))
      (FootprintEdges (U k) ∩ FootprintEdges (W k)) (p k) (l k) ∧
    p k ∈ FootprintVertices (K k) ∧ l k ∈ FootprintVertices (H k)
  have reversePath {V : Set GaussianInt} {E : Set (Finset GaussianInt)}
      {x y : GaussianInt} (hp : SimpleGridPathBetween V E x y) :
      SimpleGridPathBetween V E y x := by
    obtain ⟨p, hn, hl, hh, ht, hv, hs, he⟩ := hp
    have reverseRaw (r : List GaussianInt) (e : Finset GaussianInt) :
        (∃ u v l₁ l₂, r = l₁ ++ u :: v :: l₂ ∧ e = {u, v}) →
          ∃ u v l₁ l₂, r.reverse = l₁ ++ u :: v :: l₂ ∧ e = {u, v} := by
      rintro ⟨u, v, l₁, l₂, hr, he⟩
      exact ⟨v, u, l₂.reverse, l₁.reverse, by
        simp [hr, List.reverse_append, List.append_assoc], by
        simpa only [Finset.pair_comm] using he⟩
    refine ⟨p.reverse, List.nodup_reverse.mpr hn, by simpa using hl,
      by simpa using ht, by simpa using hh, by simpa using hv, ?_, ?_⟩
    · intro u v l₁ l₂ hr
      have hpform : p = l₂.reverse ++ v :: u :: l₁.reverse := by
        have hr' := congrArg List.reverse hr
        simpa [List.reverse_append, List.append_assoc] using hr'
      rcases hs v u l₂.reverse l₁.reverse hpform with h | h | h | h
      · exact Or.inr (Or.inl (by rw [h]; simp))
      · exact Or.inl (by rw [h]; simp)
      · exact Or.inr (Or.inr (Or.inr (by rw [h]; simp)))
      · exact Or.inr (Or.inr (Or.inl (by rw [h]; simp)))
    · intro e
      constructor
      · exact fun h => reverseRaw p e ((he e).mp h)
      · intro h
        apply (he e).mpr
        simpa using reverseRaw p.reverse e h
  have regular := (PeriodicTileIntersectionClassification cert.modified).2
  have pathFor (a b : PeriodicSubtileIndex) (hab : a ≠ b)
      (hadj : AllowedSubtileIncidence a b) (f g : PeriodicSubtileFaceIndex)
      (hfg : f ≠ g)
      (hf : (∃ i, SixSubtileFaceVertices f i = a) ∧
        ∃ i, SixSubtileFaceVertices f i = b)
      (hg : (∃ i, SixSubtileFaceVertices g i = a) ∧
        ∃ i, SixSubtileFaceVertices g i = b) :
      SimpleGridPathBetween
        (FootprintVertices (cert.modified.tile a) ∩ FootprintVertices (cert.modified.tile b))
        (FootprintEdges (cert.modified.tile a) ∩ FootprintEdges (cert.modified.tile b))
        (rho f) (rho g) := by
    have hadj' := (cert.modified_adjacency a b).mpr hadj
    obtain ⟨_, f', g', _, _, _, allFaces, hp⟩ :=
      (PeriodicTileIntersectionPaths cert.modified regular a b hab).1.mpr
        (cert.modified.adjacent_has_common_edge a b hadj')
    have liftFace (F : PeriodicSubtileFaceIndex)
        (hF : (∃ i, SixSubtileFaceVertices F i = a) ∧
          ∃ i, SixSubtileFaceVertices F i = b) :
        (∃ i, cert.modified.plane.faceVertex (cert.modifiedFaceEquivalence.symm F) i = a) ∧
        ∃ i, cert.modified.plane.faceVertex (cert.modifiedFaceEquivalence.symm F) i = b := by
      constructor
      · obtain ⟨i, hi⟩ := hF.1
        exact ⟨i, by rw [cert.modified_face_vertices]; simpa using hi⟩
      · obtain ⟨i, hi⟩ := hF.2
        exact ⟨i, by rw [cert.modified_face_vertices]; simpa using hi⟩
    have hfc := allFaces _ (liftFace f hf)
    have hgc := allFaces _ (liftFace g hg)
    have hne : cert.modifiedFaceEquivalence.symm f ≠ cert.modifiedFaceEquivalence.symm g :=
      fun h => hfg (cert.modifiedFaceEquivalence.symm.injective h)
    rw [regular.adjacent_raw_eq_edge_vertices a b hadj']
    have hpath : SimpleGridPathBetween
        (CommonFootprintEdgeVertices (cert.modified.tile a) (cert.modified.tile b))
        (FootprintEdges (cert.modified.tile a) ∩ FootprintEdges (cert.modified.tile b))
        (cert.modified.rho (cert.modifiedFaceEquivalence.symm f))
        (cert.modified.rho (cert.modifiedFaceEquivalence.symm g)) := by
      rcases hfc with hfc | hfc <;> rcases hgc with hgc | hgc
      · exact (hne (hfc.trans hgc.symm)).elim
      · simpa only [hfc, hgc] using hp
      · simpa only [hfc, hgc] using reversePath hp
      · exact (hne (hfc.trans hgc.symm)).elim
    simpa only [cert.modified_face_points, rho] using hpath
  have modifiedPath (k : Fin 6) : SimpleGridPathBetween
      (FootprintVertices (cert.modified.tile (a k)) ∩
        FootprintVertices (cert.modified.tile (b k)))
      (FootprintEdges (cert.modified.tile (a k)) ∩
        FootprintEdges (cert.modified.tile (b k))) (rho (f k)) (rho (g k)) := by
    apply pathFor (a k) (b k) (by fin_cases k <;> decide)
    · fin_cases k
      · exact AllowedSubtileIncidence.AD 0 0
      · exact AllowedSubtileIncidence.AF 0 0
      · exact AllowedSubtileIncidence.BC 0 0
      · exact AllowedSubtileIncidence.BE 0 0
      · exact AllowedSubtileIncidence.CF 0 0
      · exact AllowedSubtileIncidence.DE 0 0
    · fin_cases k <;> decide
    · let j : Fin 6 → Fin 3 := ![0, 0, 1, 0, 1, 1]
      refine ⟨⟨j k, ?_⟩, ⟨2, ?_⟩⟩ <;>
        fin_cases k <;> simp [SixSubtileFaceVertices, a, b, f, j]
    · let j : Fin 6 → Fin 3 := ![0, 0, 1, 1, 0, 1]
      refine ⟨⟨j k, ?_⟩, ⟨2, ?_⟩⟩ <;>
        fin_cases k <;> simp [SixSubtileFaceVertices, a, b, g, j]
  have hzero : GaussianTranslation (0 : GaussianInt) = id := funext add_zero
  have hAtile : cert.modified.tile ⟨.A, 0, 0⟩ =
      TileCellComplement (cert.P 0 true) cert.O := by
    rw [cert.modified_tile]
    simp [ModifiedSubtileOccurrenceInterpretation, TileTranslation, hzero]
  have hAO : (TileCellComplement (cert.P 0 true) cert.O).cells.Nonempty := by
    rw [← hAtile]
    exact (LatticeTileGridStructure _ (cert.modified.tiles_are_disks _)).1.1
  have hOA : cert.O.cells ⊆ (cert.P 0 true).cells := by
    intro z hz
    exact (cert.plus_union z).mpr ⟨0, false, by simpa only [← cert.precursor_eq] using hz⟩
  obtain ⟨_, _, _, _, _, _, _, separate⟩ :=
    P4339T1PrecursorSupportGeometry C q cfg T cert
  have isolated : ∀ z ∈ CellSupportedFootprintVertices cert.O, ∀ c : GaussianInt,
      z ∈ FootprintVertices (⟨{c}, c⟩ : ProtoTile) →
      c ∈ (cert.P 0 true).cells ∨ c ∈ (cert.P 0 false).cells := by
    intro z hz c hc
    have hzO : z ∈ FootprintVertices cert.O := by
      have hne : cert.O.cells.Nonempty := by obtain ⟨w, hw, _⟩ := hz; exact ⟨w, hw⟩
      simpa [FootprintVertices, CellSupportedFootprintVertices, hne] using hz
    have hh := cert.precursor_isolated 0 0 z
      (by simpa [TileTranslation, hzero, Finset.image_id] using hzO) c hc
    simpa [SubtileOccurrenceInterpretation, TileTranslation, hzero, Finset.image_id] using hh
  have restore (i : Fin 3) (hi : i ≠ 0) :
      FootprintVertices (TileCellComplement (cert.P 0 true) cert.O) ∩
          FootprintVertices (cert.P i false) =
        FootprintVertices (cert.P 0 true) ∩ FootprintVertices (cert.P i false) ∧
      FootprintEdges (TileCellComplement (cert.P 0 true) cert.O) ∩
          FootprintEdges (cert.P i false) =
        FootprintEdges (cert.P 0 true) ∩ FootprintEdges (cert.P i false) := by
    have hYA := separate i false 0 true (by simp [hi]) (by simp [hi])
    have hYB := separate i false 0 false (by simp [hi]) (by simp [hi])
    have hr := FootprintDeletionRetention _ _ _ _ hOA isolated hYA hYB
    exact ⟨hr.2.2 (Or.inr ⟨hAO,
      (LatticeTileGridStructure _ (cert.parent_lattice i false)).1.1⟩), hr.2.1⟩
  have restoreD := restore 1 (by decide)
  have restoreF := restore 2 (by decide)
  have faceOwner (F : PeriodicSubtileFaceIndex) (i : Fin 3) :
      rho F ∈ FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v
        (SixSubtileFaceVertices F i)) := by
    have hh := cert.unmodified.core.rho_common (cert.unmodified.faceEquiv.symm F) i
    rw [cert.unmodified.face_vertices] at hh
    simpa only [Equiv.apply_symm_apply, cert.unmodified.tile_eq, rho] using hh
  intro k
  have hp : p k = rho (f k) := by fin_cases k <;> rfl
  have hl : l k = rho (g k) := by fin_cases k <;> rfl
  rw [hp, hl]
  refine ⟨?_, ?_, ?_⟩
  · have hp := modifiedPath k
    fin_cases k <;>
      simpa [a, b, U, W, cert.modified_tile, ModifiedSubtileOccurrenceInterpretation,
        TileTranslation, hzero, restoreD.1, restoreD.2, restoreF.1, restoreF.2] using hp
  · let j : Fin 6 → Fin 3 := ![1, 1, 0, 1, 0, 0]
    have hh := faceOwner (f k) (j k)
    fin_cases k <;> simpa [f, j, K, SixSubtileFaceVertices,
      SubtileOccurrenceInterpretation, TileTranslation, hzero] using hh
  · let j : Fin 6 → Fin 3 := ![1, 1, 0, 0, 1, 0]
    have hh := faceOwner (g k) (j k)
    fin_cases k <;> simpa [g, j, H, SixSubtileFaceVertices,
      SubtileOccurrenceInterpretation, sub_eq_add_neg] using hh

end ApollonianSuperharmonic

end
