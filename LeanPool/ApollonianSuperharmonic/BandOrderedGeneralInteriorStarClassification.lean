/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralInteriorWebRow
public import LeanPool.ApollonianSuperharmonic.P4590T1OriginalNonedges
public import LeanPool.ApollonianSuperharmonic.P4590T1ReflectedCenterBoundary
public import LeanPool.ApollonianSuperharmonic.P4590T1SixLabelBoundaryCount
public import LeanPool.ApollonianSuperharmonic.P4590T1MixedInteriorGeometry
public import LeanPool.ApollonianSuperharmonic.P4590T1RightInteriorGeometry
public import LeanPool.ApollonianSuperharmonic.P4590T1RestoredBoundaryGeometry
public import LeanPool.ApollonianSuperharmonic.P4590T1JunctionRouting
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralPositiveCutGeometry

-- [TABLET NODE: BandOrderedGeneralInteriorStarClassification]

/-!
# BandOrderedGeneralInteriorStarClassification

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOrderedGeneralInteriorStarClassification
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T)
    (hT : LatticeTile T)
    (x : GaussianInt) (hx : x ∈ FootprintVertices T)
    (hxb : x ∉ BoundaryFootprintVertices T) :
    let k := Nat.card {is : Fin 3 × Bool //
      x ∈ BoundaryFootprintVertices (cert.P is.1 is.2)}
    (k = 2 → GaussianRealPoint x ≠ TileCentroid T →
      BandOrderedGeneralInteriorWebRow cert x false) ∧
    (k = 3 →
      BandOrderedGeneralInteriorWebRow cert x true ∧
      GaussianRealPoint x ≠ TileCentroid T) ∧
    k ≠ 4 ∧
    (k = 2 → GaussianRealPoint x = TileCentroid T →
      (cfg.firstPredecessor 1).1 = 0) := by
-- BODY
  classical
  have hne (i : Fin 3) (s : Bool) : (cert.P i s).cells.Nonempty :=
    (LatticeTileGridStructure _ (cert.parent_lattice i s)).1.1
  have boundary_raw (i : Fin 3) (s : Bool)
      (hb : x ∈ BoundaryFootprintVertices (cert.P i s)) :
      x ∈ FootprintVertices (cert.P i s) := by
    simp only [BoundaryFootprintVertices, hne i s, ite_true, Set.mem_ofPred_eq] at hb
    obtain ⟨e, he, hz⟩ := hb
    simp only [FootprintVertices, hne i s, ite_true, Set.mem_ofPred_eq]
    obtain ⟨a, ⟨rfl, ha⟩ | ⟨rfl, ha⟩⟩ := he
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases ha with ⟨ha, _⟩ | ⟨_, ha⟩
      · refine ⟨a, ha, ?_⟩
        rcases hz with rfl | rfl <;> simp
      · refine ⟨_, ha, ?_⟩
        rcases hz with rfl | rfl <;>
          simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have nonedges := P4590T1OriginalNonedges q cfg C₀ T cert
  have exclude (i j : Fin 3) (s t : Bool)
      (hempty : FootprintVertices (cert.P i s) ∩
          FootprintVertices (cert.P j t) = ∅) :
      ¬ (x ∈ BoundaryFootprintVertices (cert.P i s) ∧
        x ∈ BoundaryFootprintVertices (cert.P j t)) := by
    rintro ⟨hi, hj⟩
    have hf : x ∈ (∅ : Set GaussianInt) :=
      hempty ▸ ⟨boundary_raw i s hi, boundary_raw j t hj⟩
    exact hf
  have count := P4590T1SixLabelBoundaryCount
    (fun i s => x ∈ BoundaryFootprintVertices (cert.P i s))
    (exclude 0 2 true true nonedges.1)
    (exclude 0 2 false false nonedges.2.1)
    (exclude 1 1 true false nonedges.2.2.1)
    (exclude 1 2 true true nonedges.2.2.2.1)
    (exclude 1 2 false false nonedges.2.2.2.2.1)
    (exclude 2 2 true false nonedges.2.2.2.2.2)
  have central_pairing (hc : GaussianRealPoint x = TileCentroid T) :
      ∀ i, x ∈ BoundaryFootprintVertices (cert.P i true) ↔
        x ∈ BoundaryFootprintVertices (cert.P i false) := by
    have signed := BandSignedOccurrenceHalfTurn q (TileCentroid T) cert.P
      (fun i s => (cert.outer_occurrence i s).1)
      (fun i s => (cert.outer_occurrence i s).2.2)
    intro i
    apply P4590T1ReflectedCenterBoundary _ _ x (hne i true) (hne i false)
    simpa only [hc] using (signed i).2.2.2.2.2
  dsimp only at count ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hk hnoncentral
    rcases count.2.1 hk with hAB | hAC | hBD | ⟨i, j, hij, hi, hj⟩
    · rcases P4590T1RestoredBoundaryGeometry q cfg C₀ T cert hT x hx hxb
        hk hnoncentral hAB.1 hAB.2 with h | h | ⟨ha, hO⟩ | ⟨hb, hO⟩
      · exact .largestPositive h.1 h.2.1 h.2.2.1 (by simp [h.2.2.2])
      · exact .largestReflected h.1 h.2.1 h.2.2.1 (by simp [h.2.2.2])
      · subst x
        exact .leftPositiveCut rfl rfl
          (Classical.choice (BandOrderedGeneralPositiveCutGeometry q cfg C₀ T cert hO).1)
      · subst x
        exact .rightPositiveCut rfl rfl
          (Classical.choice (BandOrderedGeneralPositiveCutGeometry q cfg C₀ T cert hO).2)
    · have h := (P4590T1RightInteriorGeometry q cfg C₀ T cert hT x hx hxb hk).1
        (boundary_raw 0 true hAC.1) (boundary_raw 1 true hAC.2)
      exact .rightPositive h.1 (boundary_raw 1 true hAC.2) h.2.1 (by simp [h.2.2])
    · have h := (P4590T1RightInteriorGeometry q cfg C₀ T cert hT x hx hxb hk).2
        (boundary_raw 0 false hBD.1) (boundary_raw 1 false hBD.2)
      exact .rightReflected h.1 (boundary_raw 1 false hBD.2) h.2.1 (by simp [h.2.2])
    · have hi' := boundary_raw i true hi
      have hj' := boundary_raw j false hj
      obtain ⟨g12, g13, g21, g31, g23, g32⟩ :=
        P4590T1MixedInteriorGeometry q cfg C₀ T cert hT x hx hxb hk
      obtain ⟨m12, m13, m21, m31, m23, m32⟩ :=
        P4590T1MixedCompanionMarks q cfg C₀ T cert hT x hx hxb
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · obtain ⟨hs, hn⟩ := g12 hi' hj'
        exact .outer12 hi' hj' hs (by simp [hn])
          ((m12 hi' hj').trans (by simp [hn]))
      · obtain ⟨hs, hn⟩ := g13 hi' hj'
        exact .outer13 hi' hj' hs (by simp [hn])
          ((m13 hi' hj').trans (by simp [hn]))
      · obtain ⟨hs, hn⟩ := g21 hi' hj'
        exact .outer21 hi' hj' hs (by simp [hn])
          ((m21 hi' hj').trans (by simp [hn]))
      · exact (hij rfl).elim
      · obtain ⟨hs, hn⟩ := g23 hi' hj'
        exact .outer23 hi' hj' hs (by simp [hn])
          ((m23 hi' hj').trans (by simp [hn]))
      · obtain ⟨hs, hn⟩ := g31 hi' hj'
        exact .outer31 hi' hj' hs (by simp [hn])
          ((m31 hi' hj').trans (by simp [hn]))
      · obtain ⟨hs, hn⟩ := g32 hi' hj'
        exact .outer32 hi' hj' hs (by simp [hn])
          ((m32 hi' hj').trans (by simp [hn]))
      · exact (hij rfl).elim
  · intro hk
    refine ⟨?_, ?_⟩
    · have refineJunction := P4590T1JunctionRefinement q cfg C₀ T cert hT x hx hxb
      apply P4590T1JunctionRouting q cfg C₀ T cert hT x hx hxb
      rcases count.2.2.1 hk with h | h | h | h
      · exact Or.inl (refineJunction.1
          ⟨boundary_raw 0 true h.1, boundary_raw 0 false h.2.1,
            boundary_raw 1 true h.2.2⟩)
      · exact Or.inr (Or.inl (refineJunction.2.1
          ⟨boundary_raw 0 true h.1, boundary_raw 0 false h.2.1,
            boundary_raw 1 false h.2.2⟩))
      · exact Or.inr (Or.inr (Or.inl (refineJunction.2.2.1
          ⟨boundary_raw 0 true h.1, boundary_raw 1 true h.2.1,
            boundary_raw 2 false h.2.2⟩)))
      · exact Or.inr (Or.inr (Or.inr (refineJunction.2.2.2
          ⟨boundary_raw 0 false h.1, boundary_raw 1 false h.2.1,
            boundary_raw 2 true h.2.2⟩)))
    · intro hc
      exact (count.2.2.2 (central_pairing hc)).1 hk
  · omega
  · intro hk hc
    have hAB := (count.2.2.2 (central_pairing hc)).2 hk
    have precursor := P4339T1PrecursorSupportGeometry C₀ q cfg T cert
    by_contra hcurvature
    have hO : cert.O.cells.Nonempty := Finset.nonempty_iff_ne_empty.mpr
      (fun hempty => hcurvature (precursor.2.1.mp hempty))
    have hOlattice : LatticeTile cert.O := precursor.2.2.2.1 hO
    have hOquarter : QuarterTurnSymmetric cert.O :=
      P4055T1BandQuarterTurn _ _ precursor.2.2.1
    have all_precursor := P4590T1CentralDiskSectors cert.O hOlattice hOquarter
      x (precursor.1.trans hc.symm)
    have hmissing : ∃ j : Fin 4,
        LatticeVertexIncidentCell x j ∉ (cert.P 0 true).cells := by
      by_contra! hall
      exact ((P4456T2VertexInterior _ (hne 0 true) x
        (boundary_raw 0 true hAB.1)).2.mpr hall) hAB.1
    obtain ⟨j, hj⟩ := hmissing
    exact hj (cert.exceptionalSegments.precursor_in_left (all_precursor j))

end ApollonianSuperharmonic

end
