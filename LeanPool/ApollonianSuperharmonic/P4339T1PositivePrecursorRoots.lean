/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.LatticeFootprintIncidence

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralInteriorStarClassification

-- [TABLET NODE: P4339T1PositivePrecursorRoots]

/-!
# P4339T1PositivePrecursorRoots

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PositivePrecursorGeometry

private abbrev raw_incident := ApollonianSuperharmonic.LatticeFootprintIncidence.incidentCell

private theorem boundary_incident :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (x : GaussianInt), (U.cells.Nonempty) → ((x ∈
            BoundaryFootprintVertices U) → (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈
            U.cells)) ) := by
  classical
  intro U x hn hx
  rw [BoundaryFootprintVertices, ite_eq_left hn] at hx
  obtain ⟨e, ⟨z, ⟨rfl, hz⟩ | ⟨rfl, hz⟩⟩, hxe⟩ := hx
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
    rcases hxe with rfl | rfl <;> rcases hz with hz | hz
    · exact ⟨0, hz.1⟩
    · exact ⟨3, hz.2⟩
    · exact ⟨1, by simpa [LatticeVertexIncidentCell] using hz.1⟩
    · exact ⟨2, by simpa [LatticeVertexIncidentCell] using hz.2⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
    rcases hxe with rfl | rfl <;> rcases hz with hz | hz
    · exact ⟨0, hz.1⟩
    · exact ⟨1, hz.2⟩
    · exact ⟨3, by simpa [LatticeVertexIncidentCell] using hz.1⟩
    · refine ⟨2, ?_⟩
      convert hz.2 using 1; simp [LatticeVertexIncidentCell, sub_sub]

private theorem full_nonboundary :
    (by
      classical
      exact
        ∀ (C : BandCircle),
          ∀ (q : Fin 4 → CircleCoordinates),
            ∀ (cfg : BandOrderedGeneralConfiguration q),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C T),
                  (cert.O.cells = ∅ ↔
                      (cfg.firstPredecessor (1 : Fin (4 : ℕ))).1 = (0 : ℤ)) →
                    ∀ (U : ProtoTile),
                      ∀ (x : GaussianInt),
                        (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells) →
                          x ∉ BoundaryFootprintVertices U
    ) := by
  classical
  intro C q cfg T cert hzero U x hall
  have hn : U.cells.Nonempty := ⟨x, hall 0⟩
  intro hx
  rw [BoundaryFootprintVertices, ite_eq_left hn] at hx
  obtain ⟨e, ⟨z, ⟨rfl, hz⟩ | ⟨rfl, hz⟩⟩, hxe⟩ := hx
  all_goals
    have h0 := hall 0
    have h1 := hall 1
    have h2 := hall 2
    have h3 := hall 3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
    rcases hxe with rfl | rfl
    all_goals
      simp [LatticeVertexIncidentCell, sub_eq_add_neg, add_comm,
        add_left_comm, add_assoc] at h0 h1 h2 h3 hz
      tauto

private theorem htrans0 :
    (by
      classical
      exact
        GaussianTranslation 0 = id ) := by
  classical
  funext z
  exact add_zero z

private theorem trans_zero :
    (by
      classical
      exact
        (GaussianTranslation 0 = id) → (∀ (U : ProtoTile), TileTranslation U 0 = U) ) := by
  classical
  intro htrans0 U
  cases U
  simp [TileTranslation, htrans0]

private theorem hallAB :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (∀ (U : ProtoTile), TileTranslation U
            0 = U) → (∀ (x : GaussianInt), (x ∈ FootprintVertices cert.O) → (∀ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ∨ LatticeVertexIncidentCell x j
            ∈ (cert.P 0 false).cells)) ) := by
  classical
  intro C q cfg T cert trans_zero x hx j
  have hcorner : x ∈ FootprintVertices
      (⟨{LatticeVertexIncidentCell x j}, LatticeVertexIncidentCell x j⟩ : ProtoTile) := by
    rw [FootprintVertices, ite_eq_left (Finset.singleton_nonempty _)]
    refine ⟨LatticeVertexIncidentCell x j, by simp, ?_⟩
    fin_cases j <;> simp [LatticeVertexIncidentCell, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc]
  have hisolated := cert.precursor_isolated 0 0 x
    (by simpa only [Int.cast_zero, zero_mul, zero_add, trans_zero] using hx)
    (LatticeVertexIncidentCell x j) hcorner
  simpa only [SubtileOccurrenceInterpretation, Int.cast_zero, zero_mul,
    zero_add, trans_zero] using hisolated

private theorem hallT :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (∀ (x : GaussianInt), (x ∈
            FootprintVertices cert.O) → (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ (cert.P 0
            true).cells ∨ LatticeVertexIncidentCell x j ∈ (cert.P 0 false).cells)) → (∀ (x :
            GaussianInt), (x ∈ FootprintVertices cert.O) → (∀ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ T.cells)) ) := by
  classical
  intro C q cfg T cert hallAB x hx j
  rcases hallAB x hx j with hA | hB
  · exact (cert.outer_union _).mpr ⟨0, true, hA⟩
  · exact (cert.outer_union _).mpr ⟨0, false, hB⟩

private theorem inD :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (D : Finset GaussianInt), (∀ (x :
            GaussianInt), x ∈ D ↔ x ∈ FootprintVertices T ∧ x ∉ BoundaryFootprintVertices T) →
            ((∀ (U : ProtoTile), ∀ (x : GaussianInt), (∀ j : Fin 4, LatticeVertexIncidentCell x j
            ∈ U.cells) → (x ∉ BoundaryFootprintVertices U)) → ((∀ (x : GaussianInt), (x ∈
            FootprintVertices cert.O) → (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells)) →
            (∀ (x : GaussianInt), (x ∈ FootprintVertices cert.O) → (x ∈ D)))) ) := by
  classical
  intro C q cfg T cert D hD full_nonboundary hallT x hx
  apply (hD x).mpr
  refine ⟨?_, full_nonboundary T x (hallT x hx)⟩
  rw [FootprintVertices, ite_eq_left ⟨x, hallT x hx 0⟩]
  exact ⟨x, hallT x hx 0, Or.inl rfl⟩

private theorem hOA :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), cert.O.cells ⊆ (cert.P 0 true).cells
            ) := by
  classical
  intro C q cfg T cert z hz
  apply (cert.plus_union z).mpr
  exact ⟨0, false, by simpa only [← cert.precursor_eq] using hz⟩

private theorem hOB :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), cert.O.cells ⊆ (cert.P 0 false).cells
            ) := by
  classical
  intro C q cfg T cert z hz
  exact (cert.minus_union z).mpr ⟨0, true, by rw [← cert.precursor_cells]; exact hz⟩

private theorem incident_footprint :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (x : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈
            U.cells) → (x ∈ FootprintVertices U) ) := by
  classical
  intro U x j hj
  have hn : U.cells.Nonempty := ⟨_, hj⟩
  rw [FootprintVertices, ite_eq_left hn]
  refine ⟨LatticeVertexIncidentCell x j, hj, ?_⟩
  fin_cases j <;> simp [LatticeVertexIncidentCell, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc]

private theorem boundary_footprint :
    (by
      classical
      exact
        (∀ (U : ProtoTile), ∀ (x : GaussianInt), (U.cells.Nonempty) → ((x ∈
            BoundaryFootprintVertices U) → (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈
            U.cells))) → ((∀ (U : ProtoTile), ∀ (x : GaussianInt), ∀ (j : Fin 4),
            (LatticeVertexIncidentCell x j ∈ U.cells) → (x ∈ FootprintVertices U)) → (∀ (U :
            ProtoTile), ∀ (x : GaussianInt), (U.cells.Nonempty) → ((x ∈ BoundaryFootprintVertices
            U) → (x ∈ FootprintVertices U)))) ) := by
  classical
  intro boundary_incident incident_footprint U x hn hb
  obtain ⟨j, hj⟩ := boundary_incident U x hn hb
  exact incident_footprint U x j hj

private theorem haPlus :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (plusArc : List GaussianInt),
            (plusArc.head? = some cert.precursorBoundary.a) → (cert.precursorBoundary.a ∈
            (plusArc.toFinset : Set GaussianInt)) ) := by
  classical
  intro C q cfg T cert plusArc hplusHead
  have hn : plusArc ≠ [] := by intro h; simp [h] at hplusHead
  have heq : plusArc.head hn = cert.precursorBoundary.a := by
    have hh := hplusHead
    rw [List.head?_eq_some_head hn] at hh
    exact Option.some.inj hh
  exact List.mem_toFinset.mpr (by simpa [heq] using List.head_mem hn)

private theorem hbPlus :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (plusArc : List GaussianInt),
            (plusArc.getLast? = some cert.precursorBoundary.b) → (cert.precursorBoundary.b ∈
            (plusArc.toFinset : Set GaussianInt)) ) := by
  classical
  intro C q cfg T cert plusArc hplusLast
  have hn : plusArc ≠ [] := by intro h; simp [h] at hplusLast
  have heq : plusArc.getLast hn = cert.precursorBoundary.b := by
    have hh := hplusLast
    rw [List.getLast?_eq_getLast_of_ne_nil hn] at hh
    exact Option.some.inj hh
  exact List.mem_toFinset.mpr (by simpa [heq] using List.getLast_mem hn)

private theorem hbMinus :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (minusArc : List GaussianInt),
            (minusArc.head? = some cert.precursorBoundary.b) → (cert.precursorBoundary.b ∈
            (minusArc.toFinset : Set GaussianInt)) ) := by
  classical
  intro C q cfg T cert minusArc hminusHead
  have hn : minusArc ≠ [] := by intro h; simp [h] at hminusHead
  have heq : minusArc.head hn = cert.precursorBoundary.b := by
    have hh := hminusHead
    rw [List.head?_eq_some_head hn] at hh
    exact Option.some.inj hh
  exact List.mem_toFinset.mpr (by simpa [heq] using List.head_mem hn)

private theorem haMinus :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (minusArc : List GaussianInt),
            (minusArc.getLast? = some cert.precursorBoundary.a) → (cert.precursorBoundary.a ∈
            (minusArc.toFinset : Set GaussianInt)) ) := by
  classical
  intro C q cfg T cert minusArc hminusLast
  have hn : minusArc ≠ [] := by intro h; simp [h] at hminusLast
  have heq : minusArc.getLast hn = cert.precursorBoundary.a := by
    have hh := hminusLast
    rw [List.getLast?_eq_getLast_of_ne_nil hn] at hh
    exact Option.some.inj hh
  exact List.mem_toFinset.mpr (by simpa [heq] using List.getLast_mem hn)

private theorem arcPlus :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (plusArc : List GaussianInt),
            ((↑plusArc.toFinset : Set GaussianInt) = BoundaryFootprintVertices
            (TileCellComplement (cert.P (0 : Fin (3 : ℕ)) true) cert.O) ∩
            BoundaryFootprintVertices cert.O) → (∀ (x : GaussianInt), (x ∈ (plusArc.toFinset :
            Set GaussianInt)) → (x ∈ BoundaryFootprintVertices (TileCellComplement (cert.P 0
            true) cert.O) ∧ x ∈ BoundaryFootprintVertices cert.O)) ) := by
  classical
  intro C q cfg T cert plusArc hplusSet x hx
  rw [hplusSet] at hx
  exact hx

private theorem arcMinus :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (minusArc : List GaussianInt),
            ((↑minusArc.toFinset : Set GaussianInt) = BoundaryFootprintVertices
            (TileCellComplement (cert.P (0 : Fin (3 : ℕ)) false) cert.O) ∩
            BoundaryFootprintVertices cert.O) → (∀ (x : GaussianInt), (x ∈ (minusArc.toFinset :
            Set GaussianInt)) → (x ∈ BoundaryFootprintVertices (TileCellComplement (cert.P 0
            false) cert.O) ∧ x ∈ BoundaryFootprintVertices cert.O)) ) := by
  classical
  intro C q cfg T cert minusArc hminusSet x hx
  rw [hminusSet] at hx
  exact hx

private theorem hR :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (x : GaussianInt), x ∈
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt) ↔ x =
            cert.precursorBoundary.a ∨ x = cert.precursorBoundary.b ) := by
  classical
  intro C q cfg T cert x
  simp

private theorem endpoint_boundaries :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (plusArc : List GaussianInt), ∀
            (minusArc : List GaussianInt), (cert.precursorBoundary.a ∈ (plusArc.toFinset : Set
            GaussianInt)) → ((cert.precursorBoundary.b ∈ (plusArc.toFinset : Set GaussianInt)) →
            ((cert.precursorBoundary.b ∈ (minusArc.toFinset : Set GaussianInt)) →
            ((cert.precursorBoundary.a ∈ (minusArc.toFinset : Set GaussianInt)) → ((∀ (x :
            GaussianInt), (x ∈ (plusArc.toFinset : Set GaussianInt)) → (x ∈
            BoundaryFootprintVertices (TileCellComplement (cert.P 0 true) cert.O) ∧ x ∈
            BoundaryFootprintVertices cert.O)) → ((∀ (x : GaussianInt), (x ∈ (minusArc.toFinset :
            Set GaussianInt)) → (x ∈ BoundaryFootprintVertices (TileCellComplement (cert.P 0
            false) cert.O) ∧ x ∈ BoundaryFootprintVertices cert.O)) → ((∀ (x : GaussianInt), x ∈
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt) ↔ x =
            cert.precursorBoundary.a ∨ x = cert.precursorBoundary.b) → (∀ (x : GaussianInt), (x
            ∈ ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) → (x
            ∈ BoundaryFootprintVertices (TileCellComplement (cert.P 0 true) cert.O) ∧ x ∈
            BoundaryFootprintVertices (TileCellComplement (cert.P 0 false) cert.O) ∧ x ∈
            BoundaryFootprintVertices cert.O)))))))) ) := by
  classical
  intro C q cfg T cert plusArc minusArc haPlus hbPlus hbMinus haMinus arcPlus arcMinus hR x hxR
  rcases (hR x).mp hxR with rfl | rfl
  · exact ⟨(arcPlus _ haPlus).1, (arcMinus _ haMinus).1,
      (arcPlus _ haPlus).2⟩
  · exact ⟨(arcPlus _ hbPlus).1, (arcMinus _ hbMinus).1,
      (arcPlus _ hbPlus).2⟩

private theorem hboundaryA :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (Finset.Nonempty cert.O.cells) →
            (((cert.P (0 : Fin (3 : ℕ)) true).cells ∩ (cert.P (0 : Fin (3 : ℕ)) false).cells =
            cert.O.cells) → ((∀ (U : ProtoTile), ∀ (x : GaussianInt), (U.cells.Nonempty) → ((x ∈
            FootprintVertices U) → (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells))) → ((∀
            (U : ProtoTile), ∀ (x : GaussianInt), (U.cells.Nonempty) → ((x ∈
            BoundaryFootprintVertices U) → (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈
            U.cells))) → ((∀ (U : ProtoTile), ∀ (x : GaussianInt), (U.cells.Nonempty) → ((x ∈
            BoundaryFootprintVertices U) → (x ∈ FootprintVertices U))) → ((∀ (x : GaussianInt),
            (x ∈ ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) →
            (x ∈ BoundaryFootprintVertices (TileCellComplement (cert.P 0 true) cert.O) ∧ x ∈
            BoundaryFootprintVertices (TileCellComplement (cert.P 0 false) cert.O) ∧ x ∈
            BoundaryFootprintVertices cert.O)) → (((TileCellComplement (cert.P 0 true)
            cert.O).cells.Nonempty) → (((TileCellComplement (cert.P 0 false)
            cert.O).cells.Nonempty) → (∀ (x : GaussianInt), (x ∈ ({cert.precursorBoundary.a,
            cert.precursorBoundary.b} : Finset GaussianInt)) → (x ∈ BoundaryFootprintVertices
            (cert.P 0 true)))))))))) ) := by
  classical
  intro C q cfg T cert hO hpair raw_incident boundary_incident boundary_footprint
      endpoint_boundaries hcompA_nonempty hcompB_nonempty x hxR
  obtain ⟨hca, hcb, hco⟩ := endpoint_boundaries x hxR
  obtain ⟨jA, hjA⟩ := boundary_incident _ x hcompA_nonempty hca
  obtain ⟨jB, hjB⟩ := boundary_incident _ x hcompB_nonempty hcb
  obtain ⟨jO, hjO⟩ := raw_incident cert.O x hO
    (boundary_footprint cert.O x hO hco)
  have hAcell : LatticeVertexIncidentCell x jA ∈ (cert.P 0 true).cells := by
    exact (Finset.mem_sdiff.mp hjA).1
  have hBcell : LatticeVertexIncidentCell x jB ∈ (cert.P 0 false).cells := by
    exact (Finset.mem_sdiff.mp hjB).1
  have hA_missing : LatticeVertexIncidentCell x jB ∉ (cert.P 0 true).cells := by
    intro hc
    have hi := Finset.mem_inter.mpr ⟨hc, hBcell⟩
    rw [hpair] at hi
    exact (Finset.mem_sdiff.mp hjB).2 hi
  exact P3161T2IncidentBoundary _ x ⟨jA, hAcell⟩ ⟨jB, hA_missing⟩

private theorem hboundaryB :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ((cert.P (0 : Fin (3 : ℕ))
            true).cells ∩ (cert.P (0 : Fin (3 : ℕ)) false).cells = cert.O.cells) → ((∀ (U :
            ProtoTile), ∀ (x : GaussianInt), (U.cells.Nonempty) → ((x ∈ BoundaryFootprintVertices
            U) → (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells))) → ((∀ (x :
            GaussianInt), (x ∈ ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset
            GaussianInt)) → (x ∈ BoundaryFootprintVertices (TileCellComplement (cert.P 0 true)
            cert.O) ∧ x ∈ BoundaryFootprintVertices (TileCellComplement (cert.P 0 false) cert.O)
            ∧ x ∈ BoundaryFootprintVertices cert.O)) → (((TileCellComplement (cert.P 0 true)
            cert.O).cells.Nonempty) → (((TileCellComplement (cert.P 0 false)
            cert.O).cells.Nonempty) → (∀ (x : GaussianInt), (x ∈ ({cert.precursorBoundary.a,
            cert.precursorBoundary.b} : Finset GaussianInt)) → (x ∈ BoundaryFootprintVertices
            (cert.P 0 false))))))) ) := by
  classical
  intro C q cfg T cert hpair boundary_incident endpoint_boundaries hcompA_nonempty
      hcompB_nonempty x hxR
  obtain ⟨hca, hcb, hco⟩ := endpoint_boundaries x hxR
  obtain ⟨jA, hjA⟩ := boundary_incident _ x hcompA_nonempty hca
  obtain ⟨jB, hjB⟩ := boundary_incident _ x hcompB_nonempty hcb
  have hAcell : LatticeVertexIncidentCell x jA ∈ (cert.P 0 true).cells :=
    (Finset.mem_sdiff.mp hjA).1
  have hBcell : LatticeVertexIncidentCell x jB ∈ (cert.P 0 false).cells :=
    (Finset.mem_sdiff.mp hjB).1
  have hB_missing : LatticeVertexIncidentCell x jA ∉ (cert.P 0 false).cells := by
    intro hc
    have hi := Finset.mem_inter.mpr ⟨hAcell, hc⟩
    rw [hpair] at hi
    exact (Finset.mem_sdiff.mp hjA).2 hi
  exact P3161T2IncidentBoundary _ x ⟨jB, hBcell⟩ ⟨jA, hB_missing⟩

private theorem other_absent :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (Finset.Nonempty cert.O.cells) → ((∀
            (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (j : Fin (3 : ℕ)), ∀ (t : Bool), (i, s) ≠ (j, t) →
            ¬(i = (0 : Fin (3 : ℕ)) ∧ j = (0 : Fin (3 : ℕ))) → Disjoint (cert.P i s).cells
            (cert.P j t).cells) → ((∀ (x : GaussianInt), (x ∈ FootprintVertices cert.O) → (∀ j :
            Fin 4, LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ∨
            LatticeVertexIncidentCell x j ∈ (cert.P 0 false).cells)) → ((∀ (U : ProtoTile), ∀ (x
            : GaussianInt), (U.cells.Nonempty) → ((x ∈ BoundaryFootprintVertices U) → (x ∈
            FootprintVertices U))) → ((∀ (x : GaussianInt), (x ∈ ({cert.precursorBoundary.a,
            cert.precursorBoundary.b} : Finset GaussianInt)) → (x ∈ BoundaryFootprintVertices
            (TileCellComplement (cert.P 0 true) cert.O) ∧ x ∈ BoundaryFootprintVertices
            (TileCellComplement (cert.P 0 false) cert.O) ∧ x ∈ BoundaryFootprintVertices cert.O))
            → (∀ (x : GaussianInt), (x ∈ ({cert.precursorBoundary.a, cert.precursorBoundary.b}
            : Finset GaussianInt)) → (∀ (i : Fin 3), ∀ (s : Bool), (i ≠ 0) → (∀ (j : Fin 4),
            LatticeVertexIncidentCell x j ∉ (cert.P i s).cells))))))) ) := by
  classical
  intro C q cfg T cert hO hdisjoint hallAB boundary_footprint endpoint_boundaries x hxR i s hi j hc
  obtain ⟨_, _, hco⟩ := endpoint_boundaries x hxR
  rcases hallAB x (boundary_footprint cert.O x hO hco) j with hA | hB
  · exact Finset.disjoint_left.mp
      (hdisjoint i s 0 true (fun he => hi (congrArg Prod.fst he))
        (fun he => hi he.1)) hc hA
  · exact Finset.disjoint_left.mp
      (hdisjoint i s 0 false (fun he => hi (congrArg Prod.fst he))
        (fun he => hi he.1)) hc hB

private theorem hboundary :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (∀ (U : ProtoTile), ∀ (x :
            GaussianInt), (U.cells.Nonempty) → ((x ∈ BoundaryFootprintVertices U) → (∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ U.cells))) → ((∀ (x : GaussianInt), (x ∈
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) → (x ∈
            BoundaryFootprintVertices (cert.P 0 true))) → ((∀ (x : GaussianInt), (x ∈
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) → (x ∈
            BoundaryFootprintVertices (cert.P 0 false))) → ((∀ (x : GaussianInt), (x ∈
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) → (∀
            (i : Fin 3), ∀ (s : Bool), (i ≠ 0) → (∀ (j : Fin 4), LatticeVertexIncidentCell x j ∉
            (cert.P i s).cells))) → (∀ (x : GaussianInt), (x ∈ ({cert.precursorBoundary.a,
            cert.precursorBoundary.b} : Finset GaussianInt)) → (∀ (i : Fin 3), ∀ (s : Bool), x ∈
            BoundaryFootprintVertices (cert.P i s) ↔ i = 0))))) ) := by
  classical
  intro C q cfg T cert boundary_incident hboundaryA hboundaryB other_absent x hxR i s
  by_cases hi : i = 0
  · subst i
    cases s
    · exact ⟨fun _ => rfl, fun _ => hboundaryB x hxR⟩
    · exact ⟨fun _ => rfl, fun _ => hboundaryA x hxR⟩
  · refine ⟨fun hb => ?_, fun he => (hi he).elim⟩
    obtain ⟨j, hj⟩ := boundary_incident _ x
      (LatticeTileGridStructure _ (cert.parent_lattice i s)).1.1 hb
    exact (other_absent x hxR i s hi j hj).elim

private theorem endpoint_inD :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (D : Finset GaussianInt),
            (Finset.Nonempty cert.O.cells) → ((∀ (x : GaussianInt), (x ∈ FootprintVertices
            cert.O) → (x ∈ D)) → ((∀ (U : ProtoTile), ∀ (x : GaussianInt), (U.cells.Nonempty) →
            ((x ∈ BoundaryFootprintVertices U) → (x ∈ FootprintVertices U))) → ((∀ (x :
            GaussianInt), (x ∈ ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset
            GaussianInt)) → (x ∈ BoundaryFootprintVertices (TileCellComplement (cert.P 0 true)
            cert.O) ∧ x ∈ BoundaryFootprintVertices (TileCellComplement (cert.P 0 false) cert.O)
            ∧ x ∈ BoundaryFootprintVertices cert.O)) → (∀ (x : GaussianInt), (x ∈
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) → (x ∈
            D))))) ) := by
  classical
  intro C q cfg T cert D hO inD boundary_footprint endpoint_boundaries x hxR
  exact inD x (boundary_footprint cert.O x hO (endpoint_boundaries x hxR).2.2)

private theorem endpoint_notP :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (D : Finset GaussianInt), ∀ (P :
            Finset GaussianInt), (∀ (x : GaussianInt), x ∈ P ↔ x ∈ D ∧ ∃ (i : Fin (3 : ℕ)) (s :
            Bool), x ∈ FootprintVertices (cert.P i s) ∧ x ∉ BoundaryFootprintVertices (cert.P i
            s)) → ((∀ (U : ProtoTile), ∀ (x : GaussianInt), (U.cells.Nonempty) → ((x ∈
            FootprintVertices U) → (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells))) → ((∀
            (x : GaussianInt), (x ∈ ({cert.precursorBoundary.a, cert.precursorBoundary.b} :
            Finset GaussianInt)) → (∀ (i : Fin 3), ∀ (s : Bool), (i ≠ 0) → (∀ (j : Fin 4),
            LatticeVertexIncidentCell x j ∉ (cert.P i s).cells))) → ((∀ (x : GaussianInt), (x ∈
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) → (∀
            (i : Fin 3), ∀ (s : Bool), x ∈ BoundaryFootprintVertices (cert.P i s) ↔ i = 0)) → (∀
            (x : GaussianInt), (x ∈ ({cert.precursorBoundary.a, cert.precursorBoundary.b} :
            Finset GaussianInt)) → (x ∉ P))))) ) := by
  classical
  intro C q cfg T cert D P hP raw_incident other_absent hboundary x hxR hp
  obtain ⟨_, i, s, hfoot, hnotb⟩ := (hP x).mp hp
  by_cases hi : i = 0
  · exact hnotb ((hboundary x hxR i s).mpr hi)
  · obtain ⟨j, hj⟩ := raw_incident _ x
      (LatticeTileGridStructure _ (cert.parent_lattice i s)).1.1 hfoot
    exact (other_absent x hxR i s hi j hj).elim

private theorem hRsubset :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (D : Finset GaussianInt), ∀ (P :
            Finset GaussianInt), (∀ (x : GaussianInt), (x ∈ ({cert.precursorBoundary.a,
            cert.precursorBoundary.b} : Finset GaussianInt)) → (x ∈ D)) → ((∀ (x : GaussianInt),
            (x ∈ ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) →
            (x ∉ P)) → (({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset
            GaussianInt) ⊆ D \ P)) ) := by
  classical
  intro C q cfg T cert D P endpoint_inD endpoint_notP x hx
  exact Finset.mem_sdiff.mpr ⟨endpoint_inD x hx, endpoint_notP x hx⟩

private theorem hWfoot :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (D : Finset GaussianInt), ∀ (P :
            Finset GaussianInt), (∀ (x : GaussianInt), x ∈ P ↔ x ∈ D ∧ ∃ (i : Fin (3 : ℕ)) (s :
            Bool), x ∈ FootprintVertices (cert.P i s) ∧ x ∉ BoundaryFootprintVertices (cert.P i
            s)) → ((Finset.Nonempty cert.O.cells) → ((∀ (U : ProtoTile), ∀ (x : GaussianInt),
            (U.cells.Nonempty) → ((x ∈ FootprintVertices U) → (∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ U.cells))) → ((∀ (U : ProtoTile), ∀ (x :
            GaussianInt), (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells) → (x ∉
            BoundaryFootprintVertices U)) → ((∀ (x : GaussianInt), (x ∈ FootprintVertices cert.O)
            → (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ∨
            LatticeVertexIncidentCell x j ∈ (cert.P 0 false).cells)) → ((cert.O.cells ⊆ (cert.P 0
            true).cells) → ((cert.O.cells ⊆ (cert.P 0 false).cells) → ((∀ (U : ProtoTile), ∀ (x :
            GaussianInt), (U.cells.Nonempty) → ((x ∈ BoundaryFootprintVertices U) → (x ∈
            FootprintVertices U))) → (∀ (plusArc : List GaussianInt), ∀ (minusArc : List
            GaussianInt), ((↑plusArc.toFinset : Set GaussianInt) = BoundaryFootprintVertices
            (TileCellComplement (cert.P (0 : Fin (3 : ℕ)) true) cert.O) ∩
            BoundaryFootprintVertices cert.O) → (((↑minusArc.toFinset : Set GaussianInt) =
            BoundaryFootprintVertices (TileCellComplement (cert.P (0 : Fin (3 : ℕ)) false)
            cert.O) ∩ BoundaryFootprintVertices cert.O) → ((BoundaryFootprintVertices cert.O =
            (↑plusArc.toFinset : Set GaussianInt) ∪ (↑minusArc.toFinset : Set GaussianInt)) →
            (((↑plusArc.toFinset : Set GaussianInt) ∩ (↑minusArc.toFinset : Set GaussianInt) =
            {cert.precursorBoundary.a, cert.precursorBoundary.b}) → ((∀ (x : GaussianInt), x ∈
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt) ↔ x =
            cert.precursorBoundary.a ∨ x = cert.precursorBoundary.b) → ((∀ (x : GaussianInt),
            (x ∈ ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) →
            (x ∈ BoundaryFootprintVertices (TileCellComplement (cert.P 0 true) cert.O) ∧ x ∈
            BoundaryFootprintVertices (TileCellComplement (cert.P 0 false) cert.O) ∧ x ∈
            BoundaryFootprintVertices cert.O)) → (∀ x ∈ D \ P, x ∈ FootprintVertices cert.O ↔ x ∈
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset
            GaussianInt))))))))))))))) ) := by
  classical
  intro C q cfg T cert D P hP hO raw_incident full_nonboundary hallAB hOA hOB boundary_footprint
      plusArc minusArc hplusSet hminusSet hunion hinter hR endpoint_boundaries x hxW
  have hxD : x ∈ D := (Finset.mem_sdiff.mp hxW).1
  have hxnotP : x ∉ P := (Finset.mem_sdiff.mp hxW).2
  constructor
  · intro hxO
    have hxOB : x ∈ BoundaryFootprintVertices cert.O := by
      by_contra hnotb
      obtain ⟨j0, hj0⟩ := raw_incident cert.O x hO hxO
      have hallO : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ cert.O.cells := by
        intro j
        by_contra hj
        have hb := P3161T2IncidentBoundary cert.O x ⟨j0, hj0⟩ ⟨j, hj⟩
        exact hnotb hb
      have hAinterior : x ∉ BoundaryFootprintVertices (cert.P 0 true) :=
        full_nonboundary (cert.P 0 true) x (fun j => hOA (hallO j))
      have hAfoot : x ∈ FootprintVertices (cert.P 0 true) := by
        rw [FootprintVertices, ite_eq_left ⟨x, hOA (hallO 0)⟩]
        exact ⟨x, hOA (hallO 0), Or.inl rfl⟩
      exact hxnotP ((hP x).mpr ⟨hxD, 0, true, hAfoot, hAinterior⟩)
    have hxArcs : x ∈ (plusArc.toFinset : Set GaussianInt) ∨
        x ∈ (minusArc.toFinset : Set GaussianInt) := by
      have hh := hunion
      rw [hh] at hxOB
      exact hxOB
    rcases hxArcs with hxplus | hxminus
    · by_cases hxR : x ∈
          ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)
      · exact hxR
      · have hxnotA : x ≠ cert.precursorBoundary.a ∧
            x ≠ cert.precursorBoundary.b := by
          simpa [hR] using hxR
        have noBcomp (j : Fin 4) :
            LatticeVertexIncidentCell x j ∉
              (TileCellComplement (cert.P 0 false) cert.O).cells := by
          intro hj
          obtain ⟨k, hk⟩ := raw_incident cert.O x hO hxO
          have hmiss : LatticeVertexIncidentCell x k ∉
              (TileCellComplement (cert.P 0 false) cert.O).cells := by
            change LatticeVertexIncidentCell x k ∉
              (cert.P 0 false).cells \ cert.O.cells
            simp [hk]
          have hbcomp := P3161T2IncidentBoundary _ x ⟨j, hj⟩ ⟨k, hmiss⟩
          have hxminus : x ∈ (minusArc.toFinset : Set GaussianInt) := by
            rw [hminusSet]
            exact ⟨hbcomp, hxOB⟩
          have hboth : x ∈
              (plusArc.toFinset : Set GaussianInt) ∩
                (minusArc.toFinset : Set GaussianInt) :=
            ⟨hxplus, hxminus⟩
          rw [hinter] at hboth
          rcases hboth with he | he
          · exact hxnotA.1 he
          · exact hxnotA.2 he
        have hallA : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            (cert.P 0 true).cells := by
          intro j
          rcases hallAB x hxO j with hA | hB
          · exact hA
          · by_cases hOcell : LatticeVertexIncidentCell x j ∈ cert.O.cells
            · exact hOA hOcell
            · have : LatticeVertexIncidentCell x j ∈
                (TileCellComplement (cert.P 0 false) cert.O).cells := by
                change LatticeVertexIncidentCell x j ∈
                  (cert.P 0 false).cells \ cert.O.cells
                exact Finset.mem_sdiff.mpr ⟨hB, hOcell⟩
              exact (noBcomp j this).elim
        have hAfoot : x ∈ FootprintVertices (cert.P 0 true) := by
          rw [FootprintVertices, ite_eq_left ⟨x, hallA 0⟩]
          exact ⟨x, hallA 0, Or.inl rfl⟩
        have hAnotb := full_nonboundary (cert.P 0 true) x hallA
        exact (hxnotP ((hP x).mpr ⟨hxD, 0, true, hAfoot, hAnotb⟩)).elim
    · by_cases hxR : x ∈
          ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)
      · exact hxR
      · have hxnotA : x ≠ cert.precursorBoundary.a ∧
            x ≠ cert.precursorBoundary.b := by
          simpa [hR] using hxR
        have noAcomp (j : Fin 4) :
            LatticeVertexIncidentCell x j ∉
              (TileCellComplement (cert.P 0 true) cert.O).cells := by
          intro hj
          obtain ⟨k, hk⟩ := raw_incident cert.O x hO hxO
          have hmiss : LatticeVertexIncidentCell x k ∉
              (TileCellComplement (cert.P 0 true) cert.O).cells := by
            change LatticeVertexIncidentCell x k ∉
              (cert.P 0 true).cells \ cert.O.cells
            simp [hk]
          have hacomp := P3161T2IncidentBoundary _ x ⟨j, hj⟩ ⟨k, hmiss⟩
          have hxplus : x ∈ (plusArc.toFinset : Set GaussianInt) := by
            rw [hplusSet]
            exact ⟨hacomp, hxOB⟩
          have hboth : x ∈
              (plusArc.toFinset : Set GaussianInt) ∩
                (minusArc.toFinset : Set GaussianInt) :=
            ⟨hxplus, hxminus⟩
          rw [hinter] at hboth
          rcases hboth with he | he
          · exact hxnotA.1 he
          · exact hxnotA.2 he
        have hallB : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            (cert.P 0 false).cells := by
          intro j
          rcases hallAB x hxO j with hA | hB
          · by_cases hOcell : LatticeVertexIncidentCell x j ∈ cert.O.cells
            · exact hOB hOcell
            · have : LatticeVertexIncidentCell x j ∈
                (TileCellComplement (cert.P 0 true) cert.O).cells := by
                change LatticeVertexIncidentCell x j ∈
                  (cert.P 0 true).cells \ cert.O.cells
                exact Finset.mem_sdiff.mpr ⟨hA, hOcell⟩
              exact (noAcomp j this).elim
          · exact hB
        have hBfoot : x ∈ FootprintVertices (cert.P 0 false) := by
          rw [FootprintVertices, ite_eq_left ⟨x, hallB 0⟩]
          exact ⟨x, hallB 0, Or.inl rfl⟩
        have hBnotb := full_nonboundary (cert.P 0 false) x hallB
        exact (hxnotP ((hP x).mpr ⟨hxD, 0, false, hBfoot, hBnotb⟩)).elim
  · intro hxR
    exact boundary_footprint cert.O x hO (endpoint_boundaries x hxR).2.2

private theorem hcount :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (∀ (x : GaussianInt), (x ∈
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) → (∀
            (i : Fin 3), ∀ (s : Bool), x ∈ BoundaryFootprintVertices (cert.P i s) ↔ i = 0)) → (∀
            (x : GaussianInt), (x ∈ ({cert.precursorBoundary.a, cert.precursorBoundary.b} :
            Finset GaussianInt)) → (Nat.card
            {is : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (cert.P is.1 is.2)} = 2)) ) := by
  classical
  intro C q cfg T cert hboundary x hxR
  let e : {is : Fin 3 × Bool //
      x ∈ BoundaryFootprintVertices (cert.P is.1 is.2)} ≃ Bool :=
    { toFun := fun z => z.val.2
      invFun := fun s => ⟨(0, s), (hboundary x hxR 0 s).mpr rfl⟩
      left_inv := by
        intro z
        apply Subtype.ext
        apply Prod.ext
        · exact ((hboundary x hxR z.val.1 z.val.2).mp z.property).symm
        · rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  simp

private theorem hnoncentral :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (LatticeTile T) → (∀ (D : Finset
            GaussianInt), (∀ (x : GaussianInt), x ∈ D ↔ x ∈ FootprintVertices T ∧ x ∉
            BoundaryFootprintVertices T) → ((Finset.Nonempty cert.O.cells) → ((cert.O.cells = ∅ ↔
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))).1 = (0 : ℤ)) → ((∀ (x : GaussianInt), (x ∈
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) → (x ∈
            D)) → ((∀ (x : GaussianInt), (x ∈ ({cert.precursorBoundary.a,
            cert.precursorBoundary.b} : Finset GaussianInt)) → (Nat.card
            {is : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (cert.P is.1 is.2)} = 2)) → (∀ (x
            : GaussianInt), (x ∈ ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset
            GaussianInt)) → (GaussianRealPoint x ≠ TileCentroid T))))))) ) := by
  classical
  intro C q cfg T cert hlat D hD hO hzero endpoint_inD hcount x hxR
  have hxT : x ∈ FootprintVertices T ∧ x ∉ BoundaryFootprintVertices T :=
    (hD x).mp (endpoint_inD x hxR)
  intro hcentral
  have hzeroCurv := (BandOrderedGeneralInteriorStarClassification
    q cfg C T cert hlat x hxT.1 hxT.2).2.2.2 (hcount x hxR) hcentral
  exact ((Finset.nonempty_iff_ne_empty.mp hO) (hzero.mpr hzeroCurv))

end PositivePrecursorGeometry

theorem P4339T1PositivePrecursorRoots
    (C : BandCircle) (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (hlat : LatticeTile T)
    (D P : Finset GaussianInt)
    (hD : ∀ x, x ∈ D ↔
      x ∈ FootprintVertices T ∧ x ∉ BoundaryFootprintVertices T)
    (hP : ∀ x, x ∈ P ↔ x ∈ D ∧ ∃ i s,
      x ∈ FootprintVertices (cert.P i s) ∧
        x ∉ BoundaryFootprintVertices (cert.P i s))
    (hO : cert.O.cells.Nonempty) :
    let W := D \ P
    let R : Finset GaussianInt := {cert.precursorBoundary.a, cert.precursorBoundary.b}
    R ⊆ W ∧
    (∀ x ∈ W, x ∈ FootprintVertices cert.O ↔ x ∈ R) ∧
    (∀ x ∈ R,
      Nat.card {is : Fin 3 × Bool //
        x ∈ BoundaryFootprintVertices (cert.P is.1 is.2)} = 2 ∧
      GaussianRealPoint x ≠ TileCentroid T) := by
-- BODY
  classical
  dsimp only
  obtain ⟨hcent, hzero, _, hOlattice, _, _, hpair, hdisjoint⟩ :=
    P4339T1PrecursorSupportGeometry C q cfg T cert
  have hAcomp := cert.precursor_complement_lattice.1
  have hBcomp := cert.precursor_complement_lattice.2
  have raw_incident := PositivePrecursorGeometry.raw_incident
  have boundary_incident := PositivePrecursorGeometry.boundary_incident
  have full_nonboundary := PositivePrecursorGeometry.full_nonboundary C q cfg T cert hzero
  have hallAB := PositivePrecursorGeometry.hallAB C q cfg T cert
      (PositivePrecursorGeometry.trans_zero (PositivePrecursorGeometry.htrans0))
  have inD := PositivePrecursorGeometry.inD C q cfg T cert D hD full_nonboundary
      (PositivePrecursorGeometry.hallT C q cfg T cert hallAB)
  have hOA := PositivePrecursorGeometry.hOA C q cfg T cert
  have hOB := PositivePrecursorGeometry.hOB C q cfg T cert
  have boundary_footprint := PositivePrecursorGeometry.boundary_footprint boundary_incident
      (PositivePrecursorGeometry.incident_footprint)
  have hbranch := cert.precursorBoundary.branch
  rcases hbranch with ⟨_, plusArc, minusArc, _, _, hplusHead, hplusLast,
    hminusHead, hminusLast, hplusSet, hminusSet, _, _, hunion, hinter, _, _⟩ | hdeg
  · have haPlus := PositivePrecursorGeometry.haPlus C q cfg T cert plusArc hplusHead
    have hR := PositivePrecursorGeometry.hR C q cfg T cert
    have endpoint_boundaries := PositivePrecursorGeometry.endpoint_boundaries C q cfg T cert
        plusArc minusArc haPlus (PositivePrecursorGeometry.hbPlus C q cfg T cert plusArc
        hplusLast) (PositivePrecursorGeometry.hbMinus C q cfg T cert minusArc hminusHead)
        (PositivePrecursorGeometry.haMinus C q cfg T cert minusArc hminusLast)
        (PositivePrecursorGeometry.arcPlus C q cfg T cert plusArc hplusSet)
        (PositivePrecursorGeometry.arcMinus C q cfg T cert minusArc hminusSet) hR
    have hcompA_nonempty : (TileCellComplement (cert.P 0 true) cert.O).cells.Nonempty :=
      (LatticeTileGridStructure _ hAcomp).1.1
    have hcompB_nonempty : (TileCellComplement (cert.P 0 false) cert.O).cells.Nonempty :=
      (LatticeTileGridStructure _ hBcomp).1.1
    have other_absent := PositivePrecursorGeometry.other_absent C q cfg T cert hO hdisjoint
        hallAB boundary_footprint endpoint_boundaries
    have hboundary := PositivePrecursorGeometry.hboundary C q cfg T cert boundary_incident
        (PositivePrecursorGeometry.hboundaryA C q cfg T cert hO hpair raw_incident
        boundary_incident boundary_footprint endpoint_boundaries hcompA_nonempty hcompB_nonempty)
        (PositivePrecursorGeometry.hboundaryB C q cfg T cert hpair boundary_incident
        endpoint_boundaries hcompA_nonempty hcompB_nonempty) other_absent
    have endpoint_inD := PositivePrecursorGeometry.endpoint_inD C q cfg T cert D hO inD
        boundary_footprint endpoint_boundaries
    have hcount := PositivePrecursorGeometry.hcount C q cfg T cert hboundary
    refine ⟨(PositivePrecursorGeometry.hRsubset C q cfg T cert D P endpoint_inD
        (PositivePrecursorGeometry.endpoint_notP C q cfg T cert D P hP raw_incident other_absent
        hboundary)), (PositivePrecursorGeometry.hWfoot C q cfg T cert D P hP hO raw_incident
        full_nonboundary hallAB hOA hOB boundary_footprint plusArc minusArc hplusSet hminusSet
        hunion hinter hR endpoint_boundaries), ?_⟩
    intro x hxR
    exact ⟨hcount x hxR, (PositivePrecursorGeometry.hnoncentral C q cfg T cert hlat D hD hO hzero
        endpoint_inD hcount) x hxR⟩
  · exact False.elim ((Finset.nonempty_iff_ne_empty.mp hO) hdeg.1)

end ApollonianSuperharmonic

end
