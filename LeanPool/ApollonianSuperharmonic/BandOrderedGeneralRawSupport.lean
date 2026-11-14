/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.LatticeFootprintIncidence
public import LeanPool.ApollonianSuperharmonic.PairAssignmentFacts
public import LeanPool.ApollonianSuperharmonic.BandLayoutFaceSupport
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintInclusion
public import LeanPool.ApollonianSuperharmonic.TileTranslationProperties

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.BandOriginalPairSeparation
public import LeanPool.ApollonianSuperharmonic.FootprintDeletionRetention
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIntersectionPaths
public import LeanPool.ApollonianSuperharmonic.P3161T2PathExhaustion
public import LeanPool.ApollonianSuperharmonic.P3161T2PathSubwalk

-- [TABLET NODE: BandOrderedGeneralRawSupport]

/-!
# BandOrderedGeneralRawSupport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RawSupportGeometry

private theorem htileAAt155 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        (∀ (U : ProtoTile), TileTranslation U 0 = U) → (cert.modified.tile a = TileCellComplement
            (cert.P 0 true) cert.O) ) := by
  classical
  intro q cfg C₀ T cert a translation_zero
  rw [cert.modified_tile]
  simp [a, ModifiedSubtileOccurrenceInterpretation, translation_zero]

private theorem htileC :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        (∀ (U : ProtoTile), TileTranslation U 0 = U) → (cert.modified.tile c = cert.P 1 true) )
            := by
  classical
  intro q cfg C₀ T cert c translation_zero
  rw [cert.modified_tile]
  simp [c, ModifiedSubtileOccurrenceInterpretation, translation_zero]

private abbrev hf1At170 :=
  BandLayoutFaceSupport.firstFace

private abbrev hf3 :=
  BandLayoutFaceSupport.thirdFace

private theorem hf13 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
        let f3 := cert.modifiedFaceEquivalence.symm ⟨.I3, 0, 0⟩
        f1 ≠ f3 ) := by
  classical
  intro q cfg C₀ T cert f1 f3 h
  have := congrArg cert.modifiedFaceEquivalence h
  simp [f1, f3] at this

private theorem hend :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        ∀ (f : cert.modified.plane.Face), ∀ (g : cert.modified.plane.Face),
            (SimpleGridPathBetween (CommonFootprintEdgeVertices (cert.modified.tile a)
            (cert.modified.tile c)) (FootprintEdges (cert.modified.tile a) ∩ FootprintEdges
            (cert.modified.tile c)) (cert.modified.rho f) (cert.modified.rho g)) →
            (cert.modified.rho f ≠ cert.modified.rho g) ) := by
  classical
  intro q cfg C₀ T cert a c f g hpath h
  rcases hpath with ⟨p, hnd, hlen, hh, ht, _⟩
  have hpne : p ≠ [] := by
    intro hp
    simp [hp] at hlen
  have hh' : p.head hpne = cert.modified.rho f := by
    simpa [List.head?_eq_some_head hpne] using hh
  have ht' : p.getLast hpne = cert.modified.rho g := by
    simpa [List.getLast?_eq_some_getLast hpne] using ht
  obtain ⟨z, hz⟩ := (List.Nodup.head_eq_getLast_iff hpne hnd).mp
    (hh'.trans (h.trans ht'.symm))
  simp [hz] at hlen

private theorem hz13 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
        let f3 := cert.modifiedFaceEquivalence.symm ⟨.I3, 0, 0⟩
        let z1 := cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
        let z3 := cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)
        ∀ (f : cert.modified.plane.Face), ∀ (g : cert.modified.plane.Face), ((f1 = f ∧ f3 = g) ∨
            (f1 = g ∧ f3 = f)) → ((cert.modified.rho f1 = z1) → ((cert.modified.rho f3 = z3) →
            ((cert.modified.rho f ≠ cert.modified.rho g) → (z1 ≠ z3)))) ) := by
  classical
  intro q cfg C₀ T cert f1 f3 z1 z3 f g hpair hrho1 hrho3 hend
  rw [← hrho1, ← hrho3]
  rcases hpair with ⟨h1, h3⟩ | ⟨h1, h3⟩
  · simpa [h1, h3] using hend
  · simpa [h1, h3] using hend.symm

private theorem hcomplete :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
        let f3 := cert.modifiedFaceEquivalence.symm ⟨.I3, 0, 0⟩
        let z1 := cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
        let z3 := cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)
        (cert.modified.tile a = TileCellComplement (cert.P 0 true) cert.O) → ((cert.modified.tile
            c = cert.P 1 true) → ((FootprintVertices (cert.modified.tile a) ∩ FootprintVertices
            (cert.modified.tile c) = CommonFootprintEdgeVertices (cert.modified.tile a)
            (cert.modified.tile c)) → (∀ (f : cert.modified.plane.Face), ∀ (g :
            cert.modified.plane.Face), (SimpleGridPathBetween (CommonFootprintEdgeVertices
            (cert.modified.tile a) (cert.modified.tile c)) (FootprintEdges (cert.modified.tile a)
            ∩ FootprintEdges (cert.modified.tile c)) (cert.modified.rho f) (cert.modified.rho g))
            → (((f1 = f ∧ f3 = g) ∨ (f1 = g ∧ f3 = f)) → ((cert.modified.rho f1 = z1) →
            ((cert.modified.rho f3 = z3) → (SimpleGridPathBetween (FootprintVertices
            (TileCellComplement (cert.P 0 true) cert.O) ∩ FootprintVertices (cert.P 1 true))
            (FootprintEdges (TileCellComplement (cert.P 0 true) cert.O) ∩ FootprintEdges (cert.P
            1 true)) z1 z3 ∨ SimpleGridPathBetween (FootprintVertices (TileCellComplement (cert.P
            0 true) cert.O) ∩ FootprintVertices (cert.P 1 true)) (FootprintEdges
            (TileCellComplement (cert.P 0 true) cert.O) ∩ FootprintEdges (cert.P 1 true)) z3
            z1))))))) ) := by
  classical
  intro q cfg C₀ T cert a c f1 f3 z1 z3 htileA htileC hraw f g hpath hpair hrho1 hrho3
  rw [← hraw, htileA, htileC] at hpath
  rcases hpair with ⟨h1, h3⟩ | ⟨h1, h3⟩
  · left
    simpa [← h1, ← h3, hrho1, hrho3] using hpath
  · right
    simpa [← h3, ← h1, hrho1, hrho3] using hpath

private theorem hz1C :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
        let z1 := cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
        (cert.modified.tile c = cert.P 1 true) → ((cert.modified.rho f1 = z1) → (z1 ∈
            FootprintVertices (cert.P 1 true))) ) := by
  classical
  intro q cfg C₀ T cert c f1 z1 htileC hrho1
  have hface : cert.modified.plane.faceVertex f1 2 = c := by
    simp [f1, c, cert.modified_face_vertices, SixSubtileFaceVertices]
  have h := cert.modified.rho_common f1 2
  simpa [hface, htileC, hrho1] using h

private theorem hQne :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let z1 := cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
        let z3 := cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)
        (z1 ≠ z3) → ((z1 ∈ FootprintVertices (cert.Q 1 true)) → ((z3 ∈ FootprintVertices (cert.Q
            1 true)) → ((cert.Q 1 true).cells.Nonempty))) ) := by
  classical
  intro q cfg C₀ T cert z1 z3 hz13 hz1Q hz3Q
  by_contra hQempty
  have h1 : z1 = (cert.Q 1 true).anchor := by
    simpa [FootprintVertices, hQempty] using hz1Q
  have h3 : z3 = (cert.Q 1 true).anchor := by
    simpa [FootprintVertices, hQempty] using hz3Q
  exact hz13 (h1.trans h3.symm)

private theorem hQC :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ((cert.Q 1 true).cells.Nonempty) → (((cert.P 1 true).cells.Nonempty) →
            (Disjoint (cert.Q 1 true).cells (cert.P 1 true).cells ∧ SimpleGridPath
            (BoundaryFootprintVertices (cert.Q 1 true) ∩ BoundaryFootprintVertices (cert.P 1
            true)) (BoundaryFootprintEdges (cert.Q 1 true) ∩ BoundaryFootprintEdges (cert.P 1
            true)))) ) := by
  classical
  intro q cfg C₀ T cert hQne hCne
  rcases cert.double_third.1 with h | h | h
  · exact ⟨h.2.2.1, h.2.2.2⟩
  · rw [h.1] at hQne
    simp at hQne
  · rw [h.1] at hCne
    simp at hCne

private abbrev raw_incident := ApollonianSuperharmonic.LatticeFootprintIncidence.incidentCell

private theorem raw_boundary :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ((cert.Q 1 true).cells.Nonempty) → (((cert.P 1 true).cells.Nonempty) →
            ((Disjoint (cert.Q 1 true).cells (cert.P 1 true).cells ∧ SimpleGridPath
            (BoundaryFootprintVertices (cert.Q 1 true) ∩ BoundaryFootprintVertices (cert.P 1
            true)) (BoundaryFootprintEdges (cert.Q 1 true) ∩ BoundaryFootprintEdges (cert.P 1
            true))) → ((∀ (U : ProtoTile), ∀ (z : GaussianInt), (U.cells.Nonempty) → ((z ∈
            FootprintVertices U) → (∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ U.cells))) → (∀
            (z : GaussianInt), (z ∈ FootprintVertices (cert.Q 1 true)) → ((z ∈ FootprintVertices
            (cert.P 1 true)) → (z ∈ BoundaryFootprintVertices (cert.Q 1 true) ∩
            BoundaryFootprintVertices (cert.P 1 true))))))) ) := by
  classical
  intro q cfg C₀ T cert hQne hCne hQC raw_incident z hQ hC
  obtain ⟨jQ, hjQ⟩ := raw_incident _ z hQne hQ
  obtain ⟨jC, hjC⟩ := raw_incident _ z hCne hC
  constructor
  · exact P3161T2IncidentBoundary _ z ⟨jQ, hjQ⟩
      ⟨jC, fun h => Finset.disjoint_left.mp hQC.1 h hjC⟩
  · exact P3161T2IncidentBoundary _ z ⟨jC, hjC⟩
      ⟨jQ, fun h => Finset.disjoint_left.mp hQC.1 hjQ h⟩


private theorem hQO :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ((cert.Q 1 true).cells.Nonempty) → (Disjoint (cert.Q 1 true).cells
            cert.O.cells) ) := by
  classical
  intro q cfg C₀ T cert hQne
  rcases cert.precursor_first.2.2.1 with h | h | h
  · exact h.2.2.1.symm
  · simp [h.1]
  · rw [h.1] at hQne
    simp at hQne

private theorem hsupportEdges :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (w : List GaussianInt), (∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l :
            List GaussianInt), ∀ (r : List GaussianInt), w = l ++ a :: b :: r → {a, b} ∈
            BoundaryFootprintEdges (cert.Q (1 : Fin (3 : ℕ)) true) ∩ BoundaryFootprintEdges
            (cert.P (1 : Fin (3 : ℕ)) true)) → ((∀ (U : ProtoTile), ∀ (e : Finset GaussianInt),
            (e ∈ BoundaryFootprintEdges U) → (e ∈ FootprintEdges U)) → ((Disjoint (cert.Q 1
            true).cells cert.O.cells) → (∀ x y : GaussianInt, ∀ l r : List GaussianInt, w = l ++
            x :: y :: r → {x, y} ∈ FootprintEdges (TileCellComplement (cert.P 0 true) cert.O) ∩
            FootprintEdges (cert.P 1 true)))) ) := by
  classical
  intro q cfg C₀ T cert w hwedges boundary_edge_footprint hQO x y l r h
  have he := hwedges x y l r h
  rcases boundary_edge_footprint _ _ he.1 with ⟨cell, hc, hshape⟩
  refine ⟨⟨cell, ?_, hshape⟩, boundary_edge_footprint _ _ he.2⟩
  exact Finset.mem_sdiff.mpr
    ⟨(cert.plus_union cell).mpr ⟨1, true, hc⟩,
      fun ho => Finset.disjoint_left.mp hQO hc ho⟩

private theorem hexhaustAt317 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let z1 := cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
        let z3 := cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)
        (SimpleGridPathBetween (FootprintVertices (TileCellComplement (cert.P 0 true) cert.O) ∩
            FootprintVertices (cert.P 1 true)) (FootprintEdges (TileCellComplement (cert.P 0
            true) cert.O) ∩ FootprintEdges (cert.P 1 true)) z1 z3 ∨ SimpleGridPathBetween
            (FootprintVertices (TileCellComplement (cert.P 0 true) cert.O) ∩ FootprintVertices
            (cert.P 1 true)) (FootprintEdges (TileCellComplement (cert.P 0 true) cert.O) ∩
            FootprintEdges (cert.P 1 true)) z3 z1) → (∀ (w : List GaussianInt), (w.head? = some
            z1) → ((w.getLast? = some z3) → ((∀ x y : GaussianInt, ∀ l r : List GaussianInt, w =
            l ++ x :: y :: r → {x, y} ∈ FootprintEdges (TileCellComplement (cert.P 0 true)
            cert.O) ∩ FootprintEdges (cert.P 1 true)) → (∀ z ∈ FootprintVertices
            (TileCellComplement (cert.P 0 true) cert.O) ∩ FootprintVertices (cert.P 1 true), z ∈
            w)))) ) := by
  classical
  intro q cfg C₀ T cert z1 z3 hcomplete w hwhead hwlast hsupportEdges
  rcases hcomplete with hcomplete | hcomplete
  · exact P3161T2PathExhaustion hcomplete w hwhead hwlast hsupportEdges
  · have hrevEdges : ∀ x y : GaussianInt, ∀ l r : List GaussianInt,
        w.reverse = l ++ x :: y :: r →
        {x, y} ∈ FootprintEdges (TileCellComplement (cert.P 0 true) cert.O) ∩
          FootprintEdges (cert.P 1 true) := by
      intro x y l r h
      have h' := congrArg List.reverse h
      simp only [List.reverse_reverse, List.reverse_append, List.reverse_cons,
        List.append_assoc] at h'
      have he := hsupportEdges y x r.reverse l.reverse (by simpa using h')
      simpa [Finset.pair_comm] using he
    have hex := P3161T2PathExhaustion hcomplete w.reverse
      (by simpa using hwlast) (by simpa using hwhead) hrevEdges
    intro z hz
    exact List.mem_reverse.mp (hex z hz)

private theorem hOA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), cert.O.cells ⊆ (cert.P 0 true).cells ) := by
  classical
  intro q cfg C₀ T cert cell hc
  apply (cert.plus_union cell).mpr
  rw [cert.precursor_eq] at hc
  exact ⟨0, false, hc⟩

private theorem hOB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), cert.O.cells ⊆ (cert.P 0 false).cells ) := by
  classical
  intro q cfg C₀ T cert cell hc
  apply (cert.minus_union cell).mpr
  rw [cert.precursor_cells] at hc
  exact ⟨0, true, hc⟩

private theorem hCA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        (∀ (U : ProtoTile), TileTranslation U 0 = U) → ((∀ (a : PeriodicSubtileIndex), ∀ (b :
            PeriodicSubtileIndex), a ≠ b → ¬((a.label = SixSubtileLabel.A ∧ b.label =
            SixSubtileLabel.B ∨ a.label = SixSubtileLabel.B ∧ b.label = SixSubtileLabel.A) ∧
            a.first = b.first ∧ a.second = b.second) → Disjoint (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v a).cells (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            b).cells) → (Disjoint (cert.P 1 true).cells (cert.P 0 true).cells)) ) := by
  classical
  intro q cfg C₀ T cert translation_zero hsep
  let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
  let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
  simpa [c, a, SubtileOccurrenceInterpretation, translation_zero] using
    hsep c a (by decide) (by simp [c, a])

private theorem hCB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        (∀ (U : ProtoTile), TileTranslation U 0 = U) → ((∀ (a : PeriodicSubtileIndex), ∀ (b :
            PeriodicSubtileIndex), a ≠ b → ¬((a.label = SixSubtileLabel.A ∧ b.label =
            SixSubtileLabel.B ∨ a.label = SixSubtileLabel.B ∧ b.label = SixSubtileLabel.A) ∧
            a.first = b.first ∧ a.second = b.second) → Disjoint (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v a).cells (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            b).cells) → (Disjoint (cert.P 1 true).cells (cert.P 0 false).cells)) ) := by
  classical
  intro q cfg C₀ T cert translation_zero hsep
  let b : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
  let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
  simpa [c, b, SubtileOccurrenceInterpretation, translation_zero] using
    hsep c b (by decide) (by simp [c, b])

private theorem hisolated :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (∀ (U : ProtoTile), TileTranslation U 0 = U) → (∀ z ∈
            CellSupportedFootprintVertices cert.O, ∀ cell : GaussianInt, z ∈ FootprintVertices
            (⟨{cell}, cell⟩ : ProtoTile) → cell ∈ (cert.P 0 true).cells ∨ cell ∈ (cert.P 0
            false).cells) ) := by
  classical
  intro q cfg C₀ T cert translation_zero z hz cell hc
  have hzraw : z ∈ FootprintVertices cert.O := by
    rcases hz with ⟨cell, hc, hcorner⟩
    simpa only [FootprintVertices, ite_eq_left (show cert.O.cells.Nonempty from ⟨cell, hc⟩),
      Set.mem_ofPred_eq] using
      (show ∃ cell ∈ cert.O.cells,
        z = cell ∨ z = cell + 1 ∨ z = cell + ⟨0, 1⟩ ∨
          z = cell + 1 + ⟨0, 1⟩ from ⟨cell, hc, hcorner⟩)
  simpa [SubtileOccurrenceInterpretation, translation_zero] using
    cert.precursor_isolated 0 0 z (by simpa [translation_zero] using hzraw) cell hc

private theorem hzmodified :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (FootprintVertices (TileCellComplement (cert.P (0 : Fin (3 : ℕ)) true) cert.O)
            ∩ FootprintVertices (cert.P (1 : Fin (3 : ℕ)) true) = FootprintVertices (cert.P (0 :
            Fin (3 : ℕ)) true) ∩ FootprintVertices (cert.P (1 : Fin (3 : ℕ)) true)) → (∀ (z :
            GaussianInt), (z ∈ FootprintVertices (cert.P (0 : Fin (3 : ℕ)) true) ∩
            FootprintVertices (cert.P (1 : Fin (3 : ℕ)) true)) → (z ∈ FootprintVertices
            (TileCellComplement (cert.P 0 true) cert.O) ∩ FootprintVertices (cert.P 1 true))) )
            := by
  classical
  intro q cfg C₀ T cert hretain z hz
  rw [hretain]
  exact hz

private theorem htileB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let b : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        (∀ (U : ProtoTile), TileTranslation U 0 = U) → (cert.modified.tile b = cert.P 0 false) )
            := by
  classical
  intro q cfg C₀ T cert b translation_zero
  rw [cert.modified_tile]
  simp [b, ModifiedSubtileOccurrenceInterpretation, translation_zero]

private theorem hf1At418 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let b : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
        ∀ (f : cert.modified.plane.Face), ∀ (g : cert.modified.plane.Face), (∀ (h :
            cert.modified.plane.Face), ((∃ (i : Fin (3 : ℕ)), cert.modified.plane.faceVertex h i
            = a) ∧ ∃ (i : Fin (3 : ℕ)), cert.modified.plane.faceVertex h i = b) → h = f ∨ h = g)
            → (f1 = f ∨ f1 = g) ) := by
  classical
  intro q cfg C₀ T cert a b f1 f g hfaces
  apply hfaces
  constructor
  · exact ⟨0, by simp [f1, a, cert.modified_face_vertices, SixSubtileFaceVertices]⟩
  · exact ⟨1, by simp [f1, b, cert.modified_face_vertices, SixSubtileFaceVertices]⟩

private theorem hf2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let b : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        let f2 := cert.modifiedFaceEquivalence.symm ⟨.I2, 0, 0⟩
        ∀ (f : cert.modified.plane.Face), ∀ (g : cert.modified.plane.Face), (∀ (h :
            cert.modified.plane.Face), ((∃ (i : Fin (3 : ℕ)), cert.modified.plane.faceVertex h i
            = a) ∧ ∃ (i : Fin (3 : ℕ)), cert.modified.plane.faceVertex h i = b) → h = f ∨ h = g)
            → (f2 = f ∨ f2 = g) ) := by
  classical
  intro q cfg C₀ T cert a b f2 f g hfaces
  apply hfaces
  constructor
  · exact ⟨0, by simp [f2, a, cert.modified_face_vertices, SixSubtileFaceVertices]⟩
  · exact ⟨1, by simp [f2, b, cert.modified_face_vertices, SixSubtileFaceVertices]⟩

private theorem hf12 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
        let f2 := cert.modifiedFaceEquivalence.symm ⟨.I2, 0, 0⟩
        f1 ≠ f2 ) := by
  classical
  intro q cfg C₀ T cert f1 f2 h
  have := congrArg cert.modifiedFaceEquivalence h
  simp [f1, f2] at this

private theorem hexhaustAt438 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let b : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
        let f2 := cert.modifiedFaceEquivalence.symm ⟨.I2, 0, 0⟩
        (cert.modified.tile a = TileCellComplement (cert.P 0 true) cert.O) → ((cert.modified.tile
            b = cert.P 0 false) → (∀ (f : cert.modified.plane.Face), ∀ (g :
            cert.modified.plane.Face), (SimpleGridPathBetween (CommonFootprintEdgeVertices
            (cert.modified.tile a) (cert.modified.tile b)) (FootprintEdges (cert.modified.tile a)
            ∩ FootprintEdges (cert.modified.tile b)) (cert.modified.rho f) (cert.modified.rho g))
            → ((f1 = f ∨ f1 = g) → ((f2 = f ∨ f2 = g) → ((f1 ≠ f2) → ((cert.modified.rho f1 =
            cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)) →
            ((cert.modified.rho f2 = cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm
            ⟨.I2, 0, 0⟩)) → (∀ z ∈ CommonFootprintEdgeVertices (cert.modified.tile a)
            (cert.modified.tile b), z ∈ cert.connector)))))))) ) := by
  classical
  intro q cfg C₀ T cert a b f1 f2 htileA htileB f g hpath hf1 hf2 hf12 hrho1 hrho2
  rcases hf1 with hf1 | hf1 <;> rcases hf2 with hf2 | hf2
  · exact False.elim (hf12 (hf1.trans hf2.symm))
  · rw [← hf1, ← hf2, hrho1, hrho2, htileA, htileB] at hpath
    simpa [htileA, htileB] using P3161T2PathExhaustion hpath cert.connector
      cert.connector_head cert.connector_last cert.connector_edges
  · rw [← hf2, ← hf1, hrho2, hrho1, htileA, htileB] at hpath
    have hrevEdges : ∀ x y : GaussianInt, ∀ l r : List GaussianInt,
        cert.connector.reverse = l ++ x :: y :: r →
        {x, y} ∈ FootprintEdges (TileCellComplement (cert.P 0 true) cert.O) ∩
          FootprintEdges (cert.P 0 false) := by
      intro x y l r h
      have h' := congrArg List.reverse h
      simp only [List.reverse_reverse, List.reverse_append, List.reverse_cons,
        List.append_assoc] at h'
      have he := cert.connector_edges y x r.reverse l.reverse (by simpa using h')
      simpa [Finset.pair_comm] using he
    have hex := P3161T2PathExhaustion hpath cert.connector.reverse
      (by simpa using cert.connector_last)
      (by simpa using cert.connector_head) hrevEdges
    intro z hz
    apply List.mem_reverse.mp
    apply hex
    simpa [htileA, htileB] using hz
  · exact False.elim (hf12 (hf1.trans hf2.symm))

private theorem hmodifiedSupport :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let b : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        (cert.modified.tile a = TileCellComplement (cert.P 0 true) cert.O) → ((cert.modified.tile
            b = cert.P 0 false) → ((FootprintVertices (cert.modified.tile a) ∩ FootprintVertices
            (cert.modified.tile b) = CommonFootprintEdgeVertices (cert.modified.tile a)
            (cert.modified.tile b)) → ((∀ z ∈ CommonFootprintEdgeVertices (cert.modified.tile a)
            (cert.modified.tile b), z ∈ cert.connector) → (FootprintVertices (TileCellComplement
            (cert.P 0 true) cert.O) ∩ FootprintVertices (cert.P 0 false) ⊆ (FootprintVertices
            (cert.Q 1 true) ∩ FootprintVertices (cert.S 2 false)) ∪ FootprintVertices cert.O ∪
            (FootprintVertices (cert.Q 2 true) ∩ FootprintVertices (cert.S 1 false)))))) ) := by
  classical
  intro q cfg C₀ T cert a b htileA htileB hraw hexhaust z hz
  apply cert.connector_support z
  apply hexhaust z
  rw [← hraw, htileA, htileB]
  exact hz

private theorem hAne :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (cert.P 0 true).cells.Nonempty ) := by
  classical
  intro q cfg C₀ T cert
  have hgrid := LatticeTileGridStructure _ (cert.parent_lattice 0 true)
  exact hgrid.1.1

private theorem hdeletedNeAt478 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (TileCellComplement (cert.P 0 true) cert.O).cells.Nonempty ) := by
  classical
  intro q cfg C₀ T cert
  have hgrid := LatticeTileGridStructure _ (cert.precursor_complement_lattice.1)
  exact hgrid.1.1

private theorem hxO :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (z : GaussianInt), (z ∉ FootprintVertices cert.O) → (∀ (x : LatticeCell), (z
            = x ∨ z = x + (1 : GaussianInt) ∨ z = x + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨ z = x
            + (1 : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) → (x ∉ cert.O.cells)) ) := by
  classical
  intro q cfg C₀ T cert z hzO x hcorner hxO
  have hOne : cert.O.cells.Nonempty := ⟨x, hxO⟩
  apply hzO
  simpa only [FootprintVertices, ite_eq_left hOne, Set.mem_ofPred_eq] using
    (show ∃ x ∈ cert.O.cells,
      z = x ∨ z = x + 1 ∨ z = x + ⟨0, 1⟩ ∨
        z = x + 1 + ⟨0, 1⟩ from ⟨x, hxO, hcorner⟩)

end RawSupportGeometry

theorem BandOrderedGeneralRawSupport
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T) :
    FootprintVertices (cert.P 0 true) ∩
        FootprintVertices (cert.P 1 true) ⊆
      FootprintVertices (cert.Q 1 true) ∩
        FootprintVertices (cert.P 1 true) ∧
    FootprintVertices (cert.P 0 true) ∩
        FootprintVertices (cert.P 0 false) ⊆
      (FootprintVertices (cert.Q 1 true) ∩
         FootprintVertices (cert.S 2 false)) ∪
       FootprintVertices (cert.Q 0 false) ∪
       (FootprintVertices (cert.Q 2 true) ∩
         FootprintVertices (cert.S 1 false)) := by
-- BODY
  classical
  constructor
  · let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
    let b : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
    let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
    let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
    let f3 := cert.modifiedFaceEquivalence.symm ⟨.I3, 0, 0⟩
    let z1 := cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
    let z3 := cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)
    have translation_zero (U : ProtoTile) : TileTranslation U 0 = U :=
        TileTranslationProperties.zero U
    have htileA : cert.modified.tile a =
        TileCellComplement (cert.P 0 true) cert.O := RawSupportGeometry.htileAAt155 q cfg C₀ T
            cert translation_zero
    have htileC : cert.modified.tile c = cert.P 1 true := RawSupportGeometry.htileC q cfg C₀ T
        cert translation_zero
    have hac : a ≠ c := by decide
    have hadj : cert.modified.plane.adjacent a c :=
      (cert.modified_adjacency a c).mpr (.AC 0 0)
    have hcommon := cert.modified.adjacent_has_common_edge a c hadj
    obtain ⟨hclass, hregular⟩ := PeriodicTileIntersectionClassification cert.modified
    have hraw := ((hclass a c hac).2.1 hcommon).2
    obtain ⟨_, f, g, hfg, hf, hg, hfaces, hpath⟩ :=
      (PeriodicTileIntersectionPaths cert.modified hregular a c hac).1.mpr hcommon
    have hf1 : f1 = f ∨ f1 = g := RawSupportGeometry.hf1At170 q cfg C₀ T cert f g hfaces
    have hf3 : f3 = f ∨ f3 = g := RawSupportGeometry.hf3 q cfg C₀ T cert f g hfaces
    have hf13 : f1 ≠ f3 := RawSupportGeometry.hf13 q cfg C₀ T cert
    have hpair : (f1 = f ∧ f3 = g) ∨ (f1 = g ∧ f3 = f) := PairAssignmentFacts.assignment
        (cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩) (cert.modifiedFaceEquivalence.symm ⟨.I3,
        0, 0⟩) f g hf1 hf3 hf13
    have hrho1 : cert.modified.rho f1 = z1 := cert.modified_face_points _
    have hrho3 : cert.modified.rho f3 = z3 := cert.modified_face_points _
    have hend : cert.modified.rho f ≠ cert.modified.rho g := RawSupportGeometry.hend q cfg C₀ T
        cert f g hpath
    have hz13 : z1 ≠ z3 := RawSupportGeometry.hz13 q cfg C₀ T cert f g hpair hrho1 hrho3 hend
    have hcomplete :
        SimpleGridPathBetween
          (FootprintVertices (TileCellComplement (cert.P 0 true) cert.O) ∩
            FootprintVertices (cert.P 1 true))
          (FootprintEdges (TileCellComplement (cert.P 0 true) cert.O) ∩
            FootprintEdges (cert.P 1 true)) z1 z3 ∨
        SimpleGridPathBetween
          (FootprintVertices (TileCellComplement (cert.P 0 true) cert.O) ∩
            FootprintVertices (cert.P 1 true))
          (FootprintEdges (TileCellComplement (cert.P 0 true) cert.O) ∩
            FootprintEdges (cert.P 1 true)) z3 z1 := RawSupportGeometry.hcomplete q cfg C₀ T cert
                htileA htileC hraw f g hpath hpair hrho1 hrho3
    have hz1Q : z1 ∈ FootprintVertices (cert.Q 1 true) := cert.inner_first.1
    have hz3Q : z3 ∈ FootprintVertices (cert.Q 1 true) := cert.inner_third.1
    have hz3C : z3 ∈ FootprintVertices (cert.P 1 true) := cert.inner_third.2
    have hz1C : z1 ∈ FootprintVertices (cert.P 1 true) := RawSupportGeometry.hz1C q cfg C₀ T cert
        htileC hrho1
    have hQne : (cert.Q 1 true).cells.Nonempty := RawSupportGeometry.hQne q cfg C₀ T cert hz13
        hz1Q hz3Q
    have hCne : (cert.P 1 true).cells.Nonempty :=
      (LatticeTileGridStructure _ (cert.parent_lattice 1 true)).1.1
    have hQC : Disjoint (cert.Q 1 true).cells (cert.P 1 true).cells ∧
        SimpleGridPath
          (BoundaryFootprintVertices (cert.Q 1 true) ∩
            BoundaryFootprintVertices (cert.P 1 true))
          (BoundaryFootprintEdges (cert.Q 1 true) ∩
            BoundaryFootprintEdges (cert.P 1 true)) := RawSupportGeometry.hQC q cfg C₀ T cert
                hQne hCne
    have raw_incident (U : ProtoTile) (z : GaussianInt)
        (hne : U.cells.Nonempty) (hz : z ∈ FootprintVertices U) :
        ∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ U.cells := RawSupportGeometry.raw_incident U
            z hne hz
    have raw_boundary (z : GaussianInt)
        (hQ : z ∈ FootprintVertices (cert.Q 1 true))
        (hC : z ∈ FootprintVertices (cert.P 1 true)) :
        z ∈ BoundaryFootprintVertices (cert.Q 1 true) ∩
          BoundaryFootprintVertices (cert.P 1 true) := RawSupportGeometry.raw_boundary q cfg C₀ T
              cert hQne hCne hQC raw_incident z hQ hC
    obtain ⟨w, hwhead, hwlast, hwvertices, hwedges⟩ :=
      P3161T2PathSubwalk hQC.2 z1 z3
        (raw_boundary z1 hz1Q hz1C) (raw_boundary z3 hz3Q hz3C)
    have boundary_edge_footprint (U : ProtoTile) (e : Finset GaussianInt)
        (he : e ∈ BoundaryFootprintEdges U) : e ∈ FootprintEdges U :=
            BoundaryFootprintInclusion.boundaryEdge U e he
    have hQO : Disjoint (cert.Q 1 true).cells cert.O.cells := RawSupportGeometry.hQO q cfg C₀ T
        cert hQne
    have hsupportEdges : ∀ x y : GaussianInt, ∀ l r : List GaussianInt,
        w = l ++ x :: y :: r →
        {x, y} ∈ FootprintEdges (TileCellComplement (cert.P 0 true) cert.O) ∩
          FootprintEdges (cert.P 1 true) := RawSupportGeometry.hsupportEdges q cfg C₀ T cert w
              hwedges boundary_edge_footprint hQO
    have hexhaust : ∀ z ∈ FootprintVertices
        (TileCellComplement (cert.P 0 true) cert.O) ∩
          FootprintVertices (cert.P 1 true), z ∈ w := RawSupportGeometry.hexhaustAt317 q cfg C₀ T
              cert hcomplete w hwhead hwlast hsupportEdges
    have hOA : cert.O.cells ⊆ (cert.P 0 true).cells := RawSupportGeometry.hOA q cfg C₀ T cert
    have hOB : cert.O.cells ⊆ (cert.P 0 false).cells := RawSupportGeometry.hOB q cfg C₀ T cert
    have hsep := (BandOriginalPairSeparation cert.P cert.O cert.u cert.v
      hOA hOB cert.partition).2
    have hCA : Disjoint (cert.P 1 true).cells (cert.P 0 true).cells := RawSupportGeometry.hCA q
        cfg C₀ T cert translation_zero hsep
    have hCB : Disjoint (cert.P 1 true).cells (cert.P 0 false).cells := RawSupportGeometry.hCB q
        cfg C₀ T cert translation_zero hsep
    have hisolated : ∀ z ∈ CellSupportedFootprintVertices cert.O,
        ∀ cell : GaussianInt, z ∈ FootprintVertices (⟨{cell}, cell⟩ : ProtoTile) →
          cell ∈ (cert.P 0 true).cells ∨ cell ∈ (cert.P 0 false).cells :=
              RawSupportGeometry.hisolated q cfg C₀ T cert translation_zero
    have hdeletedNe : (TileCellComplement (cert.P 0 true) cert.O).cells.Nonempty :=
      (LatticeTileGridStructure _ cert.precursor_complement_lattice.1).1.1
    have hretain := (FootprintDeletionRetention (cert.P 0 true) (cert.P 0 false)
      cert.O (cert.P 1 true) hOA hisolated hCA hCB).2.2
        (Or.inr ⟨hdeletedNe, hCne⟩)
    intro z hz
    have hzmodified : z ∈ FootprintVertices
        (TileCellComplement (cert.P 0 true) cert.O) ∩
          FootprintVertices (cert.P 1 true) := RawSupportGeometry.hzmodified q cfg C₀ T cert
              hretain z hz
    refine ⟨?_, hz.2⟩
    have hzboundary := (hwvertices z (hexhaust z hzmodified)).1
    simp only [BoundaryFootprintVertices, ite_eq_left hQne, Set.mem_ofPred_eq] at hzboundary
    rcases hzboundary with ⟨e, he, hze⟩
    rcases boundary_edge_footprint _ _ he with ⟨cell, hc, hshape⟩
    simp only [FootprintVertices, ite_eq_left hQne, Set.mem_ofPred_eq]
    refine ⟨cell, hc, ?_⟩
    rcases hshape with rfl | rfl | rfl | rfl <;>
      simp only [Finset.mem_insert, Finset.mem_singleton] at hze
    · exact hze.elim Or.inl (fun h => Or.inr (Or.inl h))
    · exact hze.elim Or.inl (fun h => Or.inr (Or.inr (Or.inl h)))
    · exact hze.elim (fun h => Or.inr (Or.inl h))
        (fun h => Or.inr (Or.inr (Or.inr h)))
    · exact hze.elim (fun h => Or.inr (Or.inr (Or.inl h)))
        (fun h => Or.inr (Or.inr (Or.inr h)))
  · let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
    let b : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
    let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
    let f2 := cert.modifiedFaceEquivalence.symm ⟨.I2, 0, 0⟩
    have translation_zero (U : ProtoTile) : TileTranslation U 0 = U :=
        TileTranslationProperties.zero U
    have htileA : cert.modified.tile a =
        TileCellComplement (cert.P 0 true) cert.O := RawSupportGeometry.htileAAt155 q cfg C₀ T
            cert translation_zero
    have htileB : cert.modified.tile b = cert.P 0 false := RawSupportGeometry.htileB q cfg C₀ T
        cert translation_zero
    have hab : a ≠ b := by decide
    have hadj : cert.modified.plane.adjacent a b :=
      (cert.modified_adjacency a b).mpr (.AB 0 0)
    have hcommon := cert.modified.adjacent_has_common_edge a b hadj
    obtain ⟨hclass, hregular⟩ := PeriodicTileIntersectionClassification cert.modified
    have hraw := ((hclass a b hab).2.1 hcommon).2
    obtain ⟨_, f, g, hfg, hf, hg, hfaces, hpath⟩ :=
      (PeriodicTileIntersectionPaths cert.modified hregular a b hab).1.mpr hcommon
    have hf1 : f1 = f ∨ f1 = g := RawSupportGeometry.hf1At418 q cfg C₀ T cert f g hfaces
    have hf2 : f2 = f ∨ f2 = g := RawSupportGeometry.hf2 q cfg C₀ T cert f g hfaces
    have hf12 : f1 ≠ f2 := RawSupportGeometry.hf12 q cfg C₀ T cert
    have hrho1 : cert.modified.rho f1 =
        cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩) :=
      cert.modified_face_points _
    have hrho2 : cert.modified.rho f2 =
        cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I2, 0, 0⟩) :=
      cert.modified_face_points _
    have hexhaust : ∀ z ∈ CommonFootprintEdgeVertices
        (cert.modified.tile a) (cert.modified.tile b), z ∈ cert.connector :=
            RawSupportGeometry.hexhaustAt438 q cfg C₀ T cert htileA htileB f g hpath hf1 hf2 hf12
            hrho1 hrho2
    have hmodifiedSupport :
        FootprintVertices (TileCellComplement (cert.P 0 true) cert.O) ∩
            FootprintVertices (cert.P 0 false) ⊆
          (FootprintVertices (cert.Q 1 true) ∩ FootprintVertices (cert.S 2 false)) ∪
            FootprintVertices cert.O ∪
            (FootprintVertices (cert.Q 2 true) ∩ FootprintVertices (cert.S 1 false)) :=
                RawSupportGeometry.hmodifiedSupport q cfg C₀ T cert htileA htileB hraw hexhaust
    have hAne : (cert.P 0 true).cells.Nonempty := RawSupportGeometry.hAne q cfg C₀ T cert
    have hdeletedNe : (TileCellComplement (cert.P 0 true) cert.O).cells.Nonempty :=
        RawSupportGeometry.hdeletedNeAt478 q cfg C₀ T cert
    intro z hz
    rw [← cert.precursor_eq]
    by_cases hzO : z ∈ FootprintVertices cert.O
    · exact Or.inl (Or.inr hzO)
    · apply hmodifiedSupport
      refine ⟨?_, hz.2⟩
      rcases (show ∃ x ∈ (cert.P 0 true).cells,
          z = x ∨ z = x + 1 ∨ z = x + ⟨0, 1⟩ ∨
            z = x + 1 + ⟨0, 1⟩ from by
          simpa only [FootprintVertices, ite_eq_left hAne, Set.mem_ofPred_eq] using hz.1)
        with ⟨x, hx, hcorner⟩
      have hxO : x ∉ cert.O.cells := RawSupportGeometry.hxO q cfg C₀ T cert z hzO x hcorner
      simpa only [FootprintVertices, ite_eq_left hdeletedNe, Set.mem_ofPred_eq] using
        (show ∃ x ∈ (TileCellComplement (cert.P 0 true) cert.O).cells,
          z = x ∨ z = x + 1 ∨ z = x + ⟨0, 1⟩ ∨
            z = x + 1 + ⟨0, 1⟩ from
          ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxO⟩, hcorner⟩)

end ApollonianSuperharmonic

end
