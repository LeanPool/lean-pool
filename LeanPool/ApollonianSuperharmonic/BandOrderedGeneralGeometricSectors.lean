/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.LatticeFootprintIncidence

public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidenceZeroOppositeChord
public import LeanPool.ApollonianSuperharmonic.ExactPatchBoundaryInterface
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIntersectionClassification
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate

-- [TABLET NODE: BandOrderedGeneralGeometricSectors]

/-!
# BandOrderedGeneralGeometricSectors

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace GeometricSectorGeometry

private theorem hdisjoint :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        (∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (P.tile a).cells) → (∀ (a :
            PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → (Disjoint (P.tile
            a).cells (P.tile b).cells)) ) := by
  classical
  intro q cfg C₀ T cert P hindexed a b hab
  apply Finset.disjoint_left.mpr
  intro x hxa hxb
  exact hab ((hindexed x).unique hxa hxb)

private abbrev raw_incident := ApollonianSuperharmonic.LatticeFootprintIncidence.incidentCell

private theorem radial :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        ∀ (x : GaussianInt), ∀ (owner : Fin 4 → PeriodicSubtileIndex), (∀ j,
            LatticeVertexIncidentCell x j ∈ (P.tile (owner j)).cells) → (∀ (j : Fin 4), x ∈
            edgeAt x j ∧ edgeAt x j ∈ FootprintEdges (P.tile (owner j)) ∩ FootprintEdges (P.tile
            (owner (j + 1)))) ) := by
  classical
  intro q cfg C₀ T cert P edgeAt x owner howner j
  refine ⟨?_, ?_, ?_⟩
  · fin_cases j <;> simp [edgeAt]
  · refine ⟨LatticeVertexIncidentCell x j, howner j, ?_⟩
    fin_cases j <;> simp [LatticeVertexIncidentCell, edgeAt,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc, Finset.pair_comm]
  · refine ⟨LatticeVertexIncidentCell x (j + 1), howner (j + 1), ?_⟩
    fin_cases j <;> simp [LatticeVertexIncidentCell, edgeAt,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc, Finset.pair_comm]

private theorem radialMembers :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        (∀ (x : GaussianInt), ∀ (owner : Fin 4 → PeriodicSubtileIndex), (∀ j,
            LatticeVertexIncidentCell x j ∈ (P.tile (owner j)).cells) → (∀ (j : Fin 4), x ∈
            edgeAt x j ∧ edgeAt x j ∈ FootprintEdges (P.tile (owner j)) ∩ FootprintEdges (P.tile
            (owner (j + 1))))) → (∀ (x : GaussianInt), ∀ (owner : Fin 4 → PeriodicSubtileIndex),
            (∀ j, LatticeVertexIncidentCell x j ∈ (P.tile (owner j)).cells) → (∀ (j : Fin 4),
            edgeAt x j ∈ FootprintEdges (P.tile (owner j)) ∧ edgeAt x j ∈ FootprintEdges (P.tile
            (owner (j + 1))))) ) := by
  classical
  intro q cfg C₀ T cert P edgeAt radial x owner howner j
  simpa only [Set.mem_inter_iff] using (radial x owner howner j).2

private theorem hzero :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        ∀ (whole : FiniteInducedTilePatch P.plane P.tile), (whole.indices =
            ({⟨.A, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.C, 0, 0⟩,
              ⟨.D, 0, 0⟩, ⟨.E, 0, 0⟩, ⟨.F, 0, 0⟩} :
              Finset PeriodicSubtileIndex)) → (∀ (a : PeriodicSubtileIndex), (a ∈ whole.indices)
                  → (a.first = 0 ∧ a.second = 0)) ) := by
  classical
  intro q cfg C₀ T cert P whole hidx a ha
  rw [hidx] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem hnoedge :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → ((¬P.plane.adjacent
            a b) → (¬ (FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)).Nonempty)) ) := by
  classical
  intro q cfg C₀ T cert P a b hab hadj hne
  exact hadj (((PeriodicTileIntersectionClassification P).1 a b hab).1.1 hne)

private theorem hcommonempty :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (¬ (FootprintEdges (P.tile a)
            ∩ FootprintEdges (P.tile b)).Nonempty) → (CommonFootprintEdgeVertices (P.tile a)
            (P.tile b) = ∅) ) := by
  classical
  intro q cfg C₀ T cert P a b hnoedge
  ext x
  simp only [CommonFootprintEdgeVertices, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨e, he, hx⟩ := hx
  exact hnoedge ⟨e, he⟩

private theorem hjk :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        ∀ (hindexed : ∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (P.tile a).cells), ∀
            (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → (∀ (x :
            GaussianInt), ∀ (j : Fin (4 : ℕ)), ∀ (k : Fin (4 : ℕ)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun r =>
          (hindexed (LatticeVertexIncidentCell x r)).choose
        (owner j = a) → ((owner k = b) → (j ≠ k))) ) := by
  classical
  intro q cfg C₀ T cert P hindexed a b hab x j k owner hja' hkb' h
  exact hab (hja'.symm.trans (h ▸ hkb'))

private theorem hnotconsecutive :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        ∀ (hindexed : ∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (P.tile a).cells),
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        (∀ (x : GaussianInt), ∀ (owner : Fin 4 → PeriodicSubtileIndex), (∀ j,
            LatticeVertexIncidentCell x j ∈ (P.tile (owner j)).cells) → (∀ (j : Fin 4), x ∈
            edgeAt x j ∧ edgeAt x j ∈ FootprintEdges (P.tile (owner j)) ∩ FootprintEdges (P.tile
            (owner (j + 1))))) → (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (¬
            (FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)).Nonempty) → (∀ (x :
            GaussianInt), ∀ (j : Fin (4 : ℕ)), ∀ (k : Fin (4 : ℕ)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun r =>
          (hindexed (LatticeVertexIncidentCell x r)).choose
        (∀ (r : Fin 4), LatticeVertexIncidentCell x r ∈ (P.tile (owner r)).cells) → ((owner j =
            a) → ((owner k = b) → (¬ (k = j + 1 ∨ j = k + 1)))))) ) := by
  classical
  intro q cfg C₀ T cert P hindexed edgeAt radial a b hnoedge x j k owner ho hja' hkb' h
  rcases h with h | h
  · have he := radial x owner ho j
    have hown : owner (j + 1) = b := by rw [← h]; exact hkb'
    apply hnoedge
    exact ⟨edgeAt x j, by
      rcases he.2 with ⟨h1, h2⟩
      exact ⟨by simpa [hja'] using h1,
        by simpa [hown] using h2⟩⟩
  · have he := radial x owner ho k
    have hown : owner (k + 1) = a := by rw [← h]; exact hja'
    apply hnoedge
    exact ⟨edgeAt x k, by
      rcases he.2 with ⟨h1, h2⟩
      exact ⟨by simpa [hown] using h2,
        by simpa [hkb'] using h1⟩⟩

private theorem hpos :
    (by
      classical
      exact
        ∀ (j k : Fin (4 : ℕ)),
          k = j + (2 : Fin (4 : ℕ)) →
            let l := j + (1 : Fin (4 : ℕ));
            let m := j + (3 : Fin (4 : ℕ));
            j ≠ l ∧ j ≠ k ∧ j ≠ m ∧ l ≠ k ∧ l ≠ m ∧ k ≠ m) := by
  classical
  intro j k hop l m
  rw [hop]
  fin_cases j <;> decide

private theorem hlk :
    (by
      classical
      exact
        ∀ (j k : Fin (4 : ℕ)),
          k = j + (2 : Fin (4 : ℕ)) →
            let l := j + (1 : Fin (4 : ℕ));
            l + (1 : Fin (4 : ℕ)) = k) := by
  classical
  intro j k hop l
  rw [hop]
  fin_cases j <;> decide

private theorem hkm :
    (by
      classical
      exact
        ∀ (j k : Fin (4 : ℕ)),
          k = j + (2 : Fin (4 : ℕ)) →
            let m := j + (3 : Fin (4 : ℕ));
            k + (1 : Fin (4 : ℕ)) = m) := by
  classical
  intro j k hop m
  rw [hop]
  fin_cases j <;> decide

private theorem hlA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        ∀ (hindexed : ∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (P.tile a).cells),
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        (∀ (x : GaussianInt), ∀ (owner : Fin 4 → PeriodicSubtileIndex), (∀ j,
            LatticeVertexIncidentCell x j ∈ (P.tile (owner j)).cells) → (∀ (j : Fin 4), edgeAt x
            j ∈ FootprintEdges (P.tile (owner j)) ∧ edgeAt x j ∈ FootprintEdges (P.tile (owner (j
            + 1))))) → (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (¬
            (FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)).Nonempty) → (∀ (x :
            GaussianInt), ∀ (j : Fin (4 : ℕ)), ∀ (k : Fin (4 : ℕ)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun r =>
          (hindexed (LatticeVertexIncidentCell x r)).choose
        (∀ (r : Fin 4), LatticeVertexIncidentCell x r ∈ (P.tile (owner r)).cells) → ((owner k =
            b) → (
        let l := j + 1
        (l + 1 = k) → (owner l ≠ a))))) ) := by
  classical
  intro q cfg C₀ T cert P hindexed edgeAt radialMembers a b hnoedge x j k owner ho hkb' l hlk heq
  have hoK : owner (l + 1) = b := by rw [hlk]; exact hkb'
  have he := radialMembers x owner ho l
  apply hnoedge
  refine ⟨edgeAt x l, ?_⟩
  exact ⟨by simpa [heq] using he.1,
    by simpa [heq, hoK] using he.2⟩

private theorem hlB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        ∀ (hindexed : ∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (P.tile a).cells),
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        (∀ (x : GaussianInt), ∀ (owner : Fin 4 → PeriodicSubtileIndex), (∀ j,
            LatticeVertexIncidentCell x j ∈ (P.tile (owner j)).cells) → (∀ (j : Fin 4), edgeAt x
            j ∈ FootprintEdges (P.tile (owner j)) ∧ edgeAt x j ∈ FootprintEdges (P.tile (owner (j
            + 1))))) → (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (¬
            (FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)).Nonempty) → (∀ (x :
            GaussianInt), ∀ (j : Fin (4 : ℕ)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun r =>
          (hindexed (LatticeVertexIncidentCell x r)).choose
        (∀ (r : Fin 4), LatticeVertexIncidentCell x r ∈ (P.tile (owner r)).cells) → ((owner j =
            a) → (
        let l := j + 1
        owner l ≠ b)))) ) := by
  classical
  intro q cfg C₀ T cert P hindexed edgeAt radialMembers a b hnoedge x j owner ho hja' l heq
  have hoJ : owner j = a := hja'
  have hoL : owner (j + 1) = b := by simpa [l] using heq
  have he := radialMembers x owner ho j
  apply hnoedge
  refine ⟨edgeAt x j, ?_⟩
  exact ⟨by simpa [hoJ] using he.1,
    by simpa [hoL] using he.2⟩

private theorem hmA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        ∀ (hindexed : ∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (P.tile a).cells),
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        (∀ (x : GaussianInt), ∀ (owner : Fin 4 → PeriodicSubtileIndex), (∀ j,
            LatticeVertexIncidentCell x j ∈ (P.tile (owner j)).cells) → (∀ (j : Fin 4), edgeAt x
            j ∈ FootprintEdges (P.tile (owner j)) ∧ edgeAt x j ∈ FootprintEdges (P.tile (owner (j
            + 1))))) → (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (¬
            (FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)).Nonempty) → (∀ (x :
            GaussianInt), ∀ (j : Fin (4 : ℕ)), ∀ (k : Fin (4 : ℕ)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun r =>
          (hindexed (LatticeVertexIncidentCell x r)).choose
        (∀ (r : Fin 4), LatticeVertexIncidentCell x r ∈ (P.tile (owner r)).cells) → ((owner k =
            b) → (
        let m := j + 3
        (k + 1 = m) → (owner m ≠ a))))) ) := by
  classical
  intro q cfg C₀ T cert P hindexed edgeAt radialMembers a b hnoedge x j k owner ho hkb' m hkm heq
  have hoM : owner (k + 1) = a := by rw [hkm]; exact heq
  have he := radialMembers x owner ho k
  apply hnoedge
  refine ⟨edgeAt x k, ?_⟩
  exact ⟨by simpa [hoM] using he.2,
    by simpa [hkb'] using he.1⟩

private theorem hmB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        ∀ (hindexed : ∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (P.tile a).cells),
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        (∀ (x : GaussianInt), ∀ (owner : Fin 4 → PeriodicSubtileIndex), (∀ j,
            LatticeVertexIncidentCell x j ∈ (P.tile (owner j)).cells) → (∀ (j : Fin 4), edgeAt x
            j ∈ FootprintEdges (P.tile (owner j)) ∧ edgeAt x j ∈ FootprintEdges (P.tile (owner (j
            + 1))))) → (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (¬
            (FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)).Nonempty) → (∀ (x :
            GaussianInt), ∀ (j : Fin (4 : ℕ)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun r =>
          (hindexed (LatticeVertexIncidentCell x r)).choose
        (∀ (r : Fin 4), LatticeVertexIncidentCell x r ∈ (P.tile (owner r)).cells) → ((owner j =
            a) → (
        let m := j + 3
        (m + 1 = j) → (owner m ≠ b))))) ) := by
  classical
  intro q cfg C₀ T cert P hindexed edgeAt radialMembers a b hnoedge x j owner ho hja' m hmj heq
  have hoJ : owner (m + 1) = a := by rw [hmj]; exact hja'
  have he := radialMembers x owner ho m
  apply hnoedge
  refine ⟨edgeAt x m, ?_⟩
  exact ⟨by simpa [hoJ] using he.2,
    by simpa [heq] using he.1⟩

private theorem hlm :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C₀ : BandCircle),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T),
                  let P := cert.modified;
                  ∀
                    (hindexed :
                      ∀ (x : LatticeCell),
                        ∃! a : PeriodicSubtileIndex, x ∈ (P.tile a).cells),
                    (∀ (a : PeriodicSubtileIndex), LatticeTile (P.tile a)) →
                      ∀ (a : PeriodicSubtileIndex),
                        ∀ (b : PeriodicSubtileIndex),
                          ∀ (x : GaussianInt),
                            ∀ (j : Fin (4 : ℕ)),
                              ∀ (k : Fin (4 : ℕ)),
                                let owner : Fin 4 → PeriodicSubtileIndex := fun r =>
                                (hindexed (LatticeVertexIncidentCell x r)).choose;
                              (∀ (r : Fin 4),
                                LatticeVertexIncidentCell x r ∈
                                (P.tile (owner r)).cells) →
                                owner j = a →
                                owner k = b →
                                j ≠ k →
                                ¬(k = j + 1 ∨ j = k + 1) →
                                k = j + 2 →
                                let l := j + 1;
                              let m := j + 3;
                              j ≠ l ∧ j ≠ k ∧ j ≠ m ∧ l ≠ k ∧ l ≠ m ∧ k ≠ m →
                                l + 1 = k →
                                k + 1 = m →
                                m + 1 = j → owner l ≠ a → owner l ≠ b → owner l ≠ owner m
    ) := by
  classical
  intro q cfg C₀ T cert P hindexed htiles a b x j k owner ho hja' hkb' hjk hnotconsecutive hop l
      m hpos hlk hkm hmj hlA hlB heq
  have hcheck := (LatticeTileGridStructure _ (htiles (owner l))).2.1 x
  have hnJ : LatticeVertexIncidentCell x j ∉ (P.tile (owner l)).cells := by
    intro hmem
    exact hlA ((hindexed _).unique hmem (by simpa [hja'] using ho j))
  have hnK : LatticeVertexIncidentCell x k ∉ (P.tile (owner l)).cells := by
    intro hmem
    exact hlB ((hindexed _).unique hmem (by simpa [hkb'] using ho k))
  have hcellM : LatticeVertexIncidentCell x m ∈ (P.tile (owner l)).cells := by
    simpa [heq] using ho m
  have hcellL : LatticeVertexIncidentCell x l ∈ (P.tile (owner l)).cells := ho l
  rw [hop] at hnK
  fin_cases j
  · apply hcheck
    right
    exact ⟨by simpa [l, LatticeVertexIncidentCell] using hcellL,
      by simpa [m, LatticeVertexIncidentCell] using hcellM,
      by simpa [LatticeVertexIncidentCell] using hnJ,
      by simpa [LatticeVertexIncidentCell] using hnK⟩
  · apply hcheck
    left
    exact ⟨by simpa [m, LatticeVertexIncidentCell] using hcellM,
      by simpa [l, LatticeVertexIncidentCell] using hcellL,
      by simpa [LatticeVertexIncidentCell] using hnJ,
      by simpa [LatticeVertexIncidentCell] using hnK⟩
  · apply hcheck
    right
    exact ⟨by simpa [m, LatticeVertexIncidentCell] using hcellM,
      by simpa [l, LatticeVertexIncidentCell] using hcellL,
      by simpa [LatticeVertexIncidentCell] using hnK,
      by simpa [LatticeVertexIncidentCell] using hnJ⟩
  · apply hcheck
    left
    exact ⟨by simpa [l, LatticeVertexIncidentCell] using hcellL,
      by simpa [m, LatticeVertexIncidentCell] using hcellM,
      by simpa [LatticeVertexIncidentCell] using hnK,
      by simpa [LatticeVertexIncidentCell] using hnJ⟩

private theorem hjlO :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        ∀ (hindexed : ∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (P.tile a).cells), ∀
            (a : PeriodicSubtileIndex), ∀ (x : GaussianInt), ∀ (j : Fin (4 : ℕ)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun r =>
          (hindexed (LatticeVertexIncidentCell x r)).choose
        (owner j = a) → (
        let l := j + 1
        (owner l ≠ a) → (owner j ≠ owner l)) ) := by
  classical
  intro q cfg C₀ T cert P hindexed a x j owner hja' l hlA heq
  exact hlA (heq.symm.trans hja')

private theorem hjkO :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        ∀ (hindexed : ∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (P.tile a).cells), ∀
            (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → (∀ (x :
            GaussianInt), ∀ (j : Fin (4 : ℕ)), ∀ (k : Fin (4 : ℕ)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun r =>
          (hindexed (LatticeVertexIncidentCell x r)).choose
        (owner j = a) → ((owner k = b) → (owner j ≠ owner k))) ) := by
  classical
  intro q cfg C₀ T cert P hindexed a b hab x j k owner hja' hkb' heq
  exact hab (hja'.symm.trans (heq.trans hkb'))

private theorem hjmO :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        ∀ (hindexed : ∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (P.tile a).cells), ∀
            (a : PeriodicSubtileIndex), ∀ (x : GaussianInt), ∀ (j : Fin (4 : ℕ)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun r =>
          (hindexed (LatticeVertexIncidentCell x r)).choose
        (owner j = a) → (
        let m := j + 3
        (owner m ≠ a) → (owner j ≠ owner m)) ) := by
  classical
  intro q cfg C₀ T cert P hindexed a x j owner hja' m hmA heq
  exact hmA (heq.symm.trans hja')

private theorem hlkO :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        ∀ (hindexed : ∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (P.tile a).cells), ∀
            (b : PeriodicSubtileIndex), ∀ (x : GaussianInt), ∀ (j : Fin (4 : ℕ)), ∀ (k : Fin (4 :
            ℕ)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun r =>
          (hindexed (LatticeVertexIncidentCell x r)).choose
        (owner k = b) → (
        let l := j + 1
        (owner l ≠ b) → (owner l ≠ owner k)) ) := by
  classical
  intro q cfg C₀ T cert P hindexed b x j k owner hkb' l hlB heq
  exact hlB (heq.trans hkb')

private theorem hkmO :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        ∀ (hindexed : ∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (P.tile a).cells), ∀
            (b : PeriodicSubtileIndex), ∀ (x : GaussianInt), ∀ (j : Fin (4 : ℕ)), ∀ (k : Fin (4 :
            ℕ)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun r =>
          (hindexed (LatticeVertexIncidentCell x r)).choose
        (owner k = b) → (
        let m := j + 3
        (owner m ≠ b) → (owner k ≠ owner m)) ) := by
  classical
  intro q cfg C₀ T cert P hindexed b x j k owner hkb' m hmB heq
  exact hmB (heq.symm.trans hkb')

private theorem hinj :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C₀ : BandCircle),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T),
                  let P := cert.modified;
                  ∀
                    (hindexed :
                      ∀ (x : LatticeCell),
                        ∃! a : PeriodicSubtileIndex, x ∈ (P.tile a).cells),
                    ∀ (a : PeriodicSubtileIndex),
                      ∀ (b : PeriodicSubtileIndex),
                        ∀ (x : GaussianInt),
                          ∀ (j : Fin (4 : ℕ)),
                            ∀ (k : Fin (4 : ℕ)),
                              let owner : Fin 4 → PeriodicSubtileIndex := fun r =>
                                (hindexed (LatticeVertexIncidentCell x r)).choose
                              owner j = a →
                                j ≠ k →
                                ¬(k = j + 1 ∨ j = k + 1) →
                                k = j + 2 →
                                let l := j + 1
                              let m := j + 3
                              j ≠ l ∧ j ≠ k ∧ j ≠ m ∧ l ≠ k ∧ l ≠ m ∧ k ≠ m →
                                l + 1 = k →
                                k + 1 = m →
                                m + 1 = j →
                                owner l ≠ a →
                                owner l ≠ b →
                                owner m ≠ a →
                                owner m ≠ b →
                                owner l ≠ owner m →
                                owner j ≠ owner l →
                                owner j ≠ owner k →
                                owner j ≠ owner m →
                                owner l ≠ owner k →
                                owner k ≠ owner m → Function.Injective owner
    ) := by
  classical
  intro q cfg C₀ T cert P hindexed a b x j k owner hja' hjk hnotconsecutive hop l m hpos hlk hkm
      hmj hlA hlB hmA hmB hlm hjlO hjkO hjmO hlkO hkmO r s hrs
  have positions (t : Fin 4) : t = j ∨ t = l ∨ t = k ∨ t = m := by
    rw [hop]
    fin_cases j <;> fin_cases t <;> simp [l, m]
  rcases positions r with hr | hr | hr | hr <;>
    rcases positions s with hs | hs | hs | hs
  all_goals subst r; subst s
  all_goals first
    | rfl
    | exact (hjlO hrs).elim
    | exact (hjlO hrs.symm).elim
    | exact (hjkO hrs).elim
    | exact (hjkO hrs.symm).elim
    | exact (hjmO hrs).elim
    | exact (hjmO hrs.symm).elim
    | exact (hlkO hrs).elim
    | exact (hlkO hrs.symm).elim
    | exact (hlm hrs).elim
    | exact (hlm hrs.symm).elim
    | exact (hkmO hrs).elim
    | exact (hkmO hrs.symm).elim

private theorem edgeAdjacent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        ∀ (u : PeriodicSubtileIndex), ∀ (v : PeriodicSubtileIndex), (u ≠ v) → (((FootprintEdges
            (P.tile u) ∩
            FootprintEdges (P.tile v)).Nonempty) → (AllowedSubtileIncidence u v)) ) := by
  classical
  intro q cfg C₀ T cert P u v huv hedge
  have hclassification := (PeriodicTileIntersectionClassification P).1 u v huv
  have hadj := hclassification.1.1 hedge
  exact cert.modified_adjacency u v |>.mp hadj

private theorem rawCell :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        ∀ (hindexed : ∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (P.tile a).cells), (∀
            (a : PeriodicSubtileIndex), LatticeTile (P.tile a)) → (∀ (x : GaussianInt),
        let owner : Fin 4 → PeriodicSubtileIndex := fun r =>
          (hindexed (LatticeVertexIncidentCell x r)).choose
        (∀ (r : Fin 4), LatticeVertexIncidentCell x r ∈ (P.tile (owner r)).cells) → (∀ (r : Fin
            4), x ∈ FootprintVertices (P.tile (owner r)))) ) := by
  classical
  intro q cfg C₀ T cert P hindexed htiles x owner ho r
  have hneSet := (LatticeTileGridStructure _ (htiles (owner r))).1.1
  obtain ⟨c, hc⟩ := hneSet
  have hne : (P.tile (owner r)).cells.Nonempty := ⟨c, hc⟩
  simp only [FootprintVertices, hne, ite_true, Set.mem_ofPred_eq]
  refine ⟨LatticeVertexIncidentCell x r, ho r, ?_⟩
  fin_cases r <;> simp [LatticeVertexIncidentCell,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    Zsqrtd.ext_iff]

private theorem hxEdges :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        ∀ (hindexed : ∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (P.tile a).cells),
            (PeriodicTileAdjacentContactRegularity P) → (∀ (x : GaussianInt), ∀ (j : Fin (4 : ℕ)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun r =>
          (hindexed (LatticeVertexIncidentCell x r)).choose
        let l := j + 1
        let m := j + 3
        (cert.modified.plane.adjacent (owner l) (owner m)) → ((x ∈ FootprintVertices (P.tile
            (owner l)) ∩ FootprintVertices (P.tile (owner m))) → (x ∈ CommonFootprintEdgeVertices
            (P.tile (owner l)) (P.tile (owner m))))) ) := by
  classical
  intro q cfg C₀ T cert P hindexed hregular x j owner l m hadjBD hxRaw
  rw [← hregular.adjacent_raw_eq_edge_vertices _ _ hadjBD]
  exact hxRaw

private theorem hnotseq (j r : Fin 4) :
    ¬ ((r = j + 1 ∧ r + 1 = j + 3) ∨ (r = j + 3 ∧ r + 1 = j + 1)) := by
  fin_cases j <;> fin_cases r <;> decide +kernel

private theorem hdnot :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (whole : FiniteInducedTilePatch cert.modified.plane cert.modified.tile), ∀
            (d : PeriodicSubtileIndex), ∀ (rest : FiniteInducedTilePatch cert.modified.plane
            cert.modified.tile), (rest.indices = whole.indices.erase d) → (d ∉ rest.indices) ) := by
  classical
  intro q cfg C₀ T cert whole d rest hrestIdx
  rw [hrestIdx]
  simp

private theorem hdisj :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        (∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (P.tile a).cells) → (∀ (d :
            PeriodicSubtileIndex), ∀ (rest : FiniteInducedTilePatch cert.modified.plane
            cert.modified.tile), (d ∉ rest.indices) → (Disjoint (rest.unionTile).cells (P.tile
            d).cells)) ) := by
  classical
  intro q cfg C₀ T cert P hindexed d rest hdnot
  apply Finset.disjoint_left.mpr
  intro x hxU hxd
  obtain ⟨a, ha, hxa⟩ := (rest.exact_union x).1 hxU
  have had : a = d := (hindexed x).unique hxa hxd
  exact hdnot (had ▸ ha)

private theorem hunion :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        ∀ (whole : FiniteInducedTilePatch cert.modified.plane cert.modified.tile),
            (whole.unionTile = T) → (∀ (d : PeriodicSubtileIndex), (d ∈ whole.indices) → (∀ (rest
            : FiniteInducedTilePatch cert.modified.plane cert.modified.tile), (rest.unionTile =
            TileCellComplement T (cert.modified.tile d)) → (∀ z : LatticeCell, z ∈
            whole.unionTile.cells ↔ z ∈ (P.tile d).cells ∨ z ∈ rest.unionTile.cells))) ) := by
  classical
  intro q cfg C₀ T cert P whole hwhole d hd rest hrestUnion
  have hwholeCells : whole.unionTile.cells = T.cells :=
    congrArg ProtoTile.cells hwhole
  have hrestCells : rest.unionTile.cells =
      T.cells \ (P.tile d).cells := by
    rw [hrestUnion]
    rfl
  intro z
  constructor
  · intro hz
    have hzT : z ∈ T.cells := hwholeCells ▸ hz
    by_cases hzd : z ∈ (P.tile d).cells
    · exact Or.inl hzd
    · right
      rw [hrestCells]
      exact Finset.mem_sdiff.mpr ⟨hzT, hzd⟩
  · rintro (hzd | hzr)
    · rw [hwholeCells]
      exact hwholeCells ▸ (whole.exact_union z).2 ⟨d, hd, hzd⟩
    · have hzT : z ∈ T.cells := by
        rw [hrestCells] at hzr
        exact (Finset.mem_sdiff.mp hzr).1
      exact hwholeCells.symm ▸ hzT

private theorem hdn :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C₀ : BandCircle),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T),
                  let P := cert.modified;
                  (∀ (whole : FiniteInducedTilePatch P.plane P.tile),
                      whole.indices =
                          ({⟨.A, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.C, 0, 0⟩, ⟨.D, 0, 0⟩, ⟨.E, 0, 0⟩,
                              ⟨.F, 0, 0⟩} :
                            Finset PeriodicSubtileIndex) →
                        ∀ (a : PeriodicSubtileIndex),
                          a ∈ whole.indices → a.first = 0 ∧ a.second = 0) →
                    ∀
                      (whole :
                        FiniteInducedTilePatch cert.modified.plane cert.modified.tile),
                      whole.indices =
                          {(⟨SixSubtileLabel.A, (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex),
                            (⟨SixSubtileLabel.B, (0 : ℤ), (0 : ℤ)⟩ :
                              PeriodicSubtileIndex),
                            (⟨SixSubtileLabel.C, (0 : ℤ), (0 : ℤ)⟩ :
                              PeriodicSubtileIndex),
                            (⟨SixSubtileLabel.D, (0 : ℤ), (0 : ℤ)⟩ :
                              PeriodicSubtileIndex),
                            (⟨SixSubtileLabel.E, (0 : ℤ), (0 : ℤ)⟩ :
                              PeriodicSubtileIndex),
                            (⟨SixSubtileLabel.F, (0 : ℤ), (0 : ℤ)⟩ :
                              PeriodicSubtileIndex)} →
                        ∀ (d : PeriodicSubtileIndex),
                          d ∈ whole.indices →
                            ∀
                              (rest :
                                FiniteInducedTilePatch cert.modified.plane
                                cert.modified.tile),
                              rest.indices = whole.indices.erase d →
                                rest.unionTile =
                                TileCellComplement T (cert.modified.tile d) →
                                (∀ z : LatticeCell,
                                z ∈ whole.unionTile.cells ↔
                                z ∈ (P.tile d).cells ∨ z ∈ rest.unionTile.cells) →
                                let n : PeriodicSubtileIndex :=
                                match d.label with
                              | .A => ⟨.B, 0, 0⟩
                              | .B => ⟨.A, 0, 0⟩
                              | .C => ⟨.A, 0, 0⟩
                              | .D => ⟨.A, 0, 0⟩
                              | .E => ⟨.B, 0, 0⟩
                              | .F => ⟨.A, 0, 0⟩
                              AllowedSubtileIncidence d n
    ) := by
  classical
  intro q cfg C₀ T cert P hzero whole hidx d hd rest hrestIdx hrestUnion hunion n
  cases d with
  | mk lab i j =>
    have hz := hzero whole hidx ⟨lab, i, j⟩ hd
    rcases hz with ⟨hi, hj⟩
    change i = 0 at hi
    change j = 0 at hj
    subst i
    subst j
    cases lab
    · exact AllowedSubtileIncidence.AB 0 0
    · exact AllowedSubtileIncidence.symm (AllowedSubtileIncidence.AB 0 0)
    · exact AllowedSubtileIncidence.symm (AllowedSubtileIncidence.AC 0 0)
    · exact AllowedSubtileIncidence.symm (AllowedSubtileIncidence.AD 0 0)
    · exact AllowedSubtileIncidence.symm (AllowedSubtileIncidence.BE 0 0)
    · exact AllowedSubtileIncidence.symm (AllowedSubtileIncidence.AF 0 0)

private theorem hnd :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C₀ : BandCircle),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T),
                  let P := cert.modified;
                  (∀ (whole : FiniteInducedTilePatch P.plane P.tile),
                      whole.indices =
                          ({⟨.A, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.C, 0, 0⟩, ⟨.D, 0, 0⟩, ⟨.E, 0, 0⟩,
                              ⟨.F, 0, 0⟩} :
                            Finset PeriodicSubtileIndex) →
                        ∀ (a : PeriodicSubtileIndex),
                          a ∈ whole.indices → a.first = 0 ∧ a.second = 0) →
                    ∀
                      (whole :
                        FiniteInducedTilePatch cert.modified.plane cert.modified.tile),
                      whole.indices =
                          {(⟨SixSubtileLabel.A, (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex),
                            (⟨SixSubtileLabel.B, (0 : ℤ), (0 : ℤ)⟩ :
                              PeriodicSubtileIndex),
                            (⟨SixSubtileLabel.C, (0 : ℤ), (0 : ℤ)⟩ :
                              PeriodicSubtileIndex),
                            (⟨SixSubtileLabel.D, (0 : ℤ), (0 : ℤ)⟩ :
                              PeriodicSubtileIndex),
                            (⟨SixSubtileLabel.E, (0 : ℤ), (0 : ℤ)⟩ :
                              PeriodicSubtileIndex),
                            (⟨SixSubtileLabel.F, (0 : ℤ), (0 : ℤ)⟩ :
                              PeriodicSubtileIndex)} →
                        ∀ (d : PeriodicSubtileIndex),
                          d ∈ whole.indices →
                            ∀
                              (rest :
                                FiniteInducedTilePatch cert.modified.plane
                                cert.modified.tile),
                              rest.indices = whole.indices.erase d →
                                rest.unionTile =
                                TileCellComplement T (cert.modified.tile d) →
                                (∀ z : LatticeCell,
                                z ∈ whole.unionTile.cells ↔
                                z ∈ (P.tile d).cells ∨ z ∈ rest.unionTile.cells) →
                                let n : PeriodicSubtileIndex :=
                                match d.label with
                              | .A => ⟨.B, 0, 0⟩
                              | .B => ⟨.A, 0, 0⟩
                              | .C => ⟨.A, 0, 0⟩
                              | .D => ⟨.A, 0, 0⟩
                              | .E => ⟨.B, 0, 0⟩
                              | .F => ⟨.A, 0, 0⟩;
                              n ≠ d
    ) := by
  classical
  intro q cfg C₀ T cert P hzero whole hidx d hd rest hrestIdx hrestUnion hunion n
  cases d with
  | mk lab i j =>
    have hz := hzero whole hidx ⟨lab, i, j⟩ hd
    rcases hz with ⟨hi, hj⟩
    change i = 0 at hi
    change j = 0 at hj
    subst i
    subst j
    cases lab <;> decide

private theorem hnWhole :
    (by
      classical
        exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C₀ : BandCircle),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T),
                  let P := cert.modified;
                  (∀ (whole : FiniteInducedTilePatch P.plane P.tile),
                      (whole.indices =
                          ({⟨.A, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.C, 0, 0⟩, ⟨.D, 0, 0⟩,
                              ⟨.E, 0, 0⟩, ⟨.F, 0, 0⟩} :
                            Finset PeriodicSubtileIndex)) →
                        (∀ (a : PeriodicSubtileIndex),
                          (a ∈ whole.indices) → (a.first = 0 ∧ a.second = 0))) →
                    (∀
                      (whole :
                        FiniteInducedTilePatch cert.modified.plane
                          cert.modified.tile),
                      (whole.indices =
                          {(⟨SixSubtileLabel.A, (0 : ℤ), (0 : ℤ)⟩ :
                              PeriodicSubtileIndex),
                            (⟨SixSubtileLabel.B, (0 : ℤ), (0 : ℤ)⟩ :
                              PeriodicSubtileIndex),
                            (⟨SixSubtileLabel.C, (0 : ℤ), (0 : ℤ)⟩ :
                              PeriodicSubtileIndex),
                            (⟨SixSubtileLabel.D, (0 : ℤ), (0 : ℤ)⟩ :
                              PeriodicSubtileIndex),
                            (⟨SixSubtileLabel.E, (0 : ℤ), (0 : ℤ)⟩ :
                              PeriodicSubtileIndex),
                            (⟨SixSubtileLabel.F, (0 : ℤ), (0 : ℤ)⟩ :
                              PeriodicSubtileIndex)}) →
                        (∀ (d : PeriodicSubtileIndex),
                          (d ∈ whole.indices) →
                            (let n : PeriodicSubtileIndex :=
                              match d.label with
                              | .A => ⟨.B, 0, 0⟩
                              | .B => ⟨.A, 0, 0⟩
                              | .C => ⟨.A, 0, 0⟩
                              | .D => ⟨.A, 0, 0⟩
                              | .E => ⟨.B, 0, 0⟩
                              | .F => ⟨.A, 0, 0⟩;
                            (n ∈ whole.indices))))) := by
  classical
  intro q cfg C₀ T cert P hzero whole hidx d hd n
  cases d with
  | mk lab i j =>
    have hz := hzero whole hidx ⟨lab, i, j⟩ hd
    rcases hz with ⟨hi, hj⟩
    change i = 0 at hi
    change j = 0 at hj
    subst i
    subst j
    rw [hidx]
    cases lab <;> simp [n]

private theorem hnrest :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (whole : FiniteInducedTilePatch cert.modified.plane cert.modified.tile), ∀
            (d : PeriodicSubtileIndex), ∀ (rest : FiniteInducedTilePatch cert.modified.plane
            cert.modified.tile), (rest.indices = whole.indices.erase d) → (
        let n : PeriodicSubtileIndex := match d.label with
          | .A => ⟨.B, 0, 0⟩
          | .B => ⟨.A, 0, 0⟩
          | .C => ⟨.A, 0, 0⟩
          | .D => ⟨.A, 0, 0⟩
          | .E => ⟨.B, 0, 0⟩
          | .F => ⟨.A, 0, 0⟩
        (n ≠ d) → ((n ∈ whole.indices) → (n ∈ rest.indices))) ) := by
  classical
  intro q cfg C₀ T cert whole d rest hrestIdx n hnd hnWhole
  rw [hrestIdx, Finset.mem_erase]
  exact ⟨hnd, hnWhole⟩

private theorem hcommon :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        ∀ (d : PeriodicSubtileIndex), ∀ (rest : FiniteInducedTilePatch cert.modified.plane
            cert.modified.tile),
        let n : PeriodicSubtileIndex := match d.label with
          | .A => ⟨.B, 0, 0⟩
          | .B => ⟨.A, 0, 0⟩
          | .C => ⟨.A, 0, 0⟩
          | .D => ⟨.A, 0, 0⟩
          | .E => ⟨.B, 0, 0⟩
          | .F => ⟨.A, 0, 0⟩
        (n ∈ rest.indices) → ((P.plane.adjacent d n) → ((FootprintEdges (P.tile d) ∩
            FootprintEdges rest.unionTile).Nonempty)) ) := by
  classical
  intro q cfg C₀ T cert P d rest n hnrest hneAdj
  obtain ⟨e, he⟩ := P.adjacent_has_common_edge d n hneAdj
  change e ∈ FootprintEdges (P.tile d) ∧ e ∈ FootprintEdges (P.tile n) at he
  rcases he with ⟨hed, hen⟩
  change ∃ x ∈ (P.tile n).cells, _ at hen
  rcases hen with ⟨x, hx, hedge⟩
  refine ⟨e, hed, ?_⟩
  refine ⟨x, (rest.exact_union x).2 ⟨n, hnrest, hx⟩, hedge⟩

private theorem hcommonComm :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        ∀ (d : PeriodicSubtileIndex), ∀ (rest : FiniteInducedTilePatch cert.modified.plane
            cert.modified.tile), CommonFootprintEdgeVertices (P.tile d) rest.unionTile =
            CommonFootprintEdgeVertices rest.unionTile (P.tile d) ) := by
  classical
  intro q cfg C₀ T cert P d rest
  ext x
  simp [CommonFootprintEdgeVertices, Set.mem_inter_iff, and_comm]

end GeometricSectorGeometry

namespace GeometricSectorAssembly

private theorem hnoPinch :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.modified
        (∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (P.tile a).cells) →
            ((PeriodicTileAdjacentContactRegularity P) → ((∀ (a : PeriodicSubtileIndex),
            LatticeTile (P.tile a)) → ((∀ (a : PeriodicSubtileIndex), ∀ (b :
            PeriodicSubtileIndex), (a ≠ b) → (Disjoint (P.tile a).cells (P.tile b).cells)) → ((∀
            (U : ProtoTile), ∀ (x : GaussianInt), (U.cells.Nonempty) → ((x ∈ FootprintVertices U)
            → (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells))) → (
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        (∀ (x : GaussianInt), ∀ (owner : Fin 4 → PeriodicSubtileIndex), (∀ j,
            LatticeVertexIncidentCell x j ∈ (P.tile (owner j)).cells) → (∀ (j : Fin 4), x ∈
            edgeAt x j ∧ edgeAt x j ∈ FootprintEdges (P.tile (owner j)) ∩ FootprintEdges (P.tile
            (owner (j + 1))))) → ((∀ (x : GaussianInt), ∀ (owner : Fin 4 → PeriodicSubtileIndex),
            (∀ j, LatticeVertexIncidentCell x j ∈ (P.tile (owner j)).cells) → (∀ (j : Fin 4),
            edgeAt x j ∈ FootprintEdges (P.tile (owner j)) ∧ edgeAt x j ∈ FootprintEdges (P.tile
            (owner (j + 1))))) → (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex),
            (a.first = 0 ∧ a.second = 0) → ((b.first = 0 ∧ b.second = 0) → ((a ≠ b) →
            (FootprintVertices (P.tile a) ∩ FootprintVertices (P.tile b) =
            CommonFootprintEdgeVertices (P.tile a) (P.tile b))))))))))) ) := by
  classical
  intro q cfg C₀ T cert P hindexed hregular htiles hdisjoint raw_incident edgeAt radial
      radialMembers a b ha hb hab
  by_cases hadj : P.plane.adjacent a b
  · exact hregular.adjacent_raw_eq_edge_vertices a b hadj
  · have hnoedge : ¬ (FootprintEdges (P.tile a) ∩
        FootprintEdges (P.tile b)).Nonempty := GeometricSectorGeometry.hnoedge q cfg C₀ T cert
            a b hab hadj
    have hcommonempty : CommonFootprintEdgeVertices (P.tile a) (P.tile b) = ∅ :=
        GeometricSectorGeometry.hcommonempty q cfg C₀ T cert a b hnoedge
    have hrawempty : FootprintVertices (P.tile a) ∩
        FootprintVertices (P.tile b) = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      have hneA : (P.tile a).cells.Nonempty :=
        (LatticeTileGridStructure _ (htiles a)).1.1
      have hneB : (P.tile b).cells.Nonempty :=
        (LatticeTileGridStructure _ (htiles b)).1.1
      obtain ⟨j, hja⟩ := raw_incident (P.tile a) x hneA hx.1
      obtain ⟨k, hkb⟩ := raw_incident (P.tile b) x hneB hx.2
      let owner : Fin 4 → PeriodicSubtileIndex := fun r =>
        (hindexed (LatticeVertexIncidentCell x r)).choose
      have ho (r : Fin 4) :
          LatticeVertexIncidentCell x r ∈ (P.tile (owner r)).cells :=
        (hindexed _).choose_spec.1
      have hja' : owner j = a := (hindexed _).unique (ho j) hja
      have hkb' : owner k = b := (hindexed _).unique (ho k) hkb
      have hjk : j ≠ k := GeometricSectorGeometry.hjk q cfg C₀ T cert hindexed a b hab x j k
          hja' hkb'
      have hnotconsecutive : ¬ (k = j + 1 ∨ j = k + 1) :=
          GeometricSectorGeometry.hnotconsecutive q cfg C₀ T cert hindexed radial a b hnoedge x
          j k ho hja' hkb'
      have hop : k = j + 2 := by
        fin_cases j <;> fin_cases k <;> simp_all
      let l := j + 1
      let m := j + 3
      -- The remaining incident sectors are owned by the two other labels.
      have hfalse : False := by
        have hpos : j ≠ l ∧ j ≠ k ∧ j ≠ m ∧ l ≠ k ∧ l ≠ m ∧ k ≠ m :=
            GeometricSectorGeometry.hpos j k hop
        have hlk : l + 1 = k := GeometricSectorGeometry.hlk j
            k hop
        have hkm : k + 1 = m := GeometricSectorGeometry.hkm j
            k hop
        have hmj : m + 1 = j := by fin_cases j <;> simp [m]
        have hlA : owner l ≠ a := GeometricSectorGeometry.hlA q cfg C₀ T cert hindexed
            radialMembers a b hnoedge x j k ho hkb' hlk
        have hlB : owner l ≠ b := GeometricSectorGeometry.hlB q cfg C₀ T cert hindexed
            radialMembers a b hnoedge x j ho hja'
        have hmA : owner m ≠ a := GeometricSectorGeometry.hmA q cfg C₀ T cert hindexed
            radialMembers a b hnoedge x j k ho hkb' hkm
        have hmB : owner m ≠ b := GeometricSectorGeometry.hmB q cfg C₀ T cert hindexed
            radialMembers a b hnoedge x j ho hja' hmj
        have hlm : owner l ≠ owner m := GeometricSectorGeometry.hlm q cfg C₀ T cert hindexed
            htiles a b x j k ho hja' hkb' hjk hnotconsecutive hop hpos hlk hkm hmj hlA hlB
        have hjlO : owner j ≠ owner l := GeometricSectorGeometry.hjlO q cfg C₀ T cert hindexed
            a x j hja' hlA
        have hjkO : owner j ≠ owner k := GeometricSectorGeometry.hjkO q cfg C₀ T cert hindexed
            a b hab x j k hja' hkb'
        have hjmO : owner j ≠ owner m := GeometricSectorGeometry.hjmO q cfg C₀ T cert hindexed
            a x j hja' hmA
        have hlkO : owner l ≠ owner k := GeometricSectorGeometry.hlkO q cfg C₀ T cert hindexed
            b x j k hkb' hlB
        have hkmO : owner k ≠ owner m := GeometricSectorGeometry.hkmO q cfg C₀ T cert hindexed
            b x j k hkb' hmB
        have hinj : Function.Injective owner := GeometricSectorGeometry.hinj q cfg C₀ T cert
            hindexed a b x j k hja' hjk hnotconsecutive hop hpos hlk hkm hmj hlA hlB hmA
            hmB hlm hjlO hjkO hjmO hlkO hkmO
        have edgeAdjacent (u v : PeriodicSubtileIndex) (huv : u ≠ v)
            (hedge : (FootprintEdges (P.tile u) ∩
              FootprintEdges (P.tile v)).Nonempty) :
            AllowedSubtileIncidence u v := GeometricSectorGeometry.edgeAdjacent q cfg C₀ T cert
                u v huv hedge
        have hcycle01 : AllowedSubtileIncidence (owner j) (owner l) :=
          edgeAdjacent _ _ hjlO ⟨edgeAt x j, by
            exact ⟨(radialMembers x owner ho j).1,
              by simpa [l] using (radialMembers x owner ho j).2⟩⟩
        have hcycle12 : AllowedSubtileIncidence (owner l) (owner k) :=
          edgeAdjacent _ _ hlkO ⟨edgeAt x l, by
            exact ⟨(radialMembers x owner ho l).1,
              by simpa [hlk] using (radialMembers x owner ho l).2⟩⟩
        have hcycle23 : AllowedSubtileIncidence (owner k) (owner m) :=
          edgeAdjacent _ _ hkmO ⟨edgeAt x k, by
            exact ⟨(radialMembers x owner ho k).1,
              by simpa [hkm] using (radialMembers x owner ho k).2⟩⟩
        have hcycle30 : AllowedSubtileIncidence (owner m) (owner j) :=
          edgeAdjacent _ _ (by
            intro heq
            exact hmA (heq.trans hja'))
            ⟨edgeAt x m, by
              exact ⟨(radialMembers x owner ho m).1,
                by simpa [hmj] using (radialMembers x owner ho m).2⟩⟩
        have hzeroJ : (owner j).first = 0 ∧ (owner j).second = 0 := by
          simpa [hja'] using ha
        have hzeroK : (owner k).first = 0 ∧ (owner k).second = 0 := by
          simpa [hkb'] using hb
        have hchord := AllowedSubtileIncidenceZeroOppositeChord
          (owner j) (owner l) (owner k) (owner m) hzeroJ hzeroK
          hcycle01 hcycle12 hcycle23 hcycle30
          (hinj.ne hpos.1) (hinj.ne hpos.2.1) (hinj.ne hpos.2.2.1)
          (hinj.ne hpos.2.2.2.1) (hinj.ne hpos.2.2.2.2.1)
          (hinj.ne hpos.2.2.2.2.2)
        rcases hchord with hac | hbd
        · exact hadj ((cert.modified_adjacency a b).mpr (by
            simpa [hja', hkb'] using hac))
        · have hadjBD := (cert.modified_adjacency (owner l) (owner m)).mpr hbd
          have rawCell (r : Fin 4) :
              x ∈ FootprintVertices (P.tile (owner r)) := GeometricSectorGeometry.rawCell q cfg
                  C₀ T cert hindexed htiles x ho r
          have hxRaw : x ∈ FootprintVertices (P.tile (owner l)) ∩
              FootprintVertices (P.tile (owner m)) := ⟨rawCell l, rawCell m⟩
          have hxEdges : x ∈ CommonFootprintEdgeVertices
              (P.tile (owner l)) (P.tile (owner m)) := GeometricSectorGeometry.hxEdges q cfg C₀
                  T cert hindexed hregular x j hadjBD hxRaw
          obtain ⟨e, he, hxe⟩ := hxEdges
          obtain ⟨r, _, hsector⟩ := P3102T2CommonEdgeSectorTransition
            (P.tile (owner l)) (P.tile (owner m)) x e
            (hdisjoint _ _ (hinj.ne hpos.2.2.2.2.1)) hxe he
          have hnotseq (r : Fin 4) :
              ¬ ((r = l ∧ r + 1 = m) ∨ (r = m ∧ r + 1 = l)) := GeometricSectorGeometry.hnotseq j r
          rcases hsector with ⟨hr, hs⟩ | ⟨hr, hs⟩
          · have hrl : owner r = owner l := (hindexed _).unique (ho r) hr
            have hsm : owner (r + 1) = owner m :=
              (hindexed _).unique (ho (r + 1)) hs
            exact hnotseq r (Or.inl ⟨hinj hrl, hinj hsm⟩)
          · have hrm : owner r = owner m := (hindexed _).unique (ho r) hr
            have hsl : owner (r + 1) = owner l :=
              (hindexed _).unique (ho (r + 1)) hs
            exact hnotseq r (Or.inr ⟨hinj hrm, hinj hsl⟩)
      exact hfalse
    rw [hrawempty, hcommonempty]

end GeometricSectorAssembly

theorem BandOrderedGeneralGeometricSectors
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T) :
    ∀ whole : FiniteInducedTilePatch
        cert.modified.plane cert.modified.tile,
      whole.indices =
          ({⟨.A, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.C, 0, 0⟩,
            ⟨.D, 0, 0⟩, ⟨.E, 0, 0⟩, ⟨.F, 0, 0⟩} :
            Finset PeriodicSubtileIndex) →
      whole.unionTile = T →
      (∀ a ∈ whole.indices, ∀ b ∈ whole.indices, a ≠ b →
        FootprintVertices (cert.modified.tile a) ∩
            FootprintVertices (cert.modified.tile b) =
          CommonFootprintEdgeVertices
            (cert.modified.tile a) (cert.modified.tile b)) ∧
      ∀ d ∈ whole.indices,
        ∀ rest : FiniteInducedTilePatch
            cert.modified.plane cert.modified.tile,
          rest.indices = whole.indices.erase d →
          rest.unionTile =
            TileCellComplement T (cert.modified.tile d) →
          ExactPatchBoundaryInterface rest d := by
-- BODY
  classical
  let P := cert.modified
  have hindexed := PeriodicTileIndexedMultiplicityOne P
  have hregular := (PeriodicTileIntersectionClassification P).2
  have htiles (a : PeriodicSubtileIndex) : LatticeTile (P.tile a) :=
    P.tiles_are_disks a
  have hdisjoint (a b : PeriodicSubtileIndex) (hab : a ≠ b) :
      Disjoint (P.tile a).cells (P.tile b).cells := GeometricSectorGeometry.hdisjoint q cfg C₀ T
          cert hindexed a b hab
  have raw_incident (U : ProtoTile) (x : GaussianInt)
      (hne : U.cells.Nonempty) (hx : x ∈ FootprintVertices U) :
      ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells :=
          GeometricSectorGeometry.raw_incident U x hne hx
  let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
    ![{x, x + ⟨0, 1⟩}, {x - 1, x},
      {x - ⟨0, 1⟩, x}, {x, x + 1}]
  have radial (x : GaussianInt) (owner : Fin 4 → PeriodicSubtileIndex)
      (howner : ∀ j, LatticeVertexIncidentCell x j ∈ (P.tile (owner j)).cells)
      (j : Fin 4) :
      x ∈ edgeAt x j ∧ edgeAt x j ∈
        FootprintEdges (P.tile (owner j)) ∩
          FootprintEdges (P.tile (owner (j + 1))) := GeometricSectorGeometry.radial q cfg C₀ T
              cert x owner howner j
  have radialMembers (x : GaussianInt) (owner : Fin 4 → PeriodicSubtileIndex)
      (howner : ∀ j, LatticeVertexIncidentCell x j ∈ (P.tile (owner j)).cells)
      (j : Fin 4) :
      edgeAt x j ∈ FootprintEdges (P.tile (owner j)) ∧
        edgeAt x j ∈ FootprintEdges (P.tile (owner (j + 1))) :=
            GeometricSectorGeometry.radialMembers q cfg C₀ T cert radial x owner howner j
  have hzero (whole : FiniteInducedTilePatch P.plane P.tile)
      (hidx : whole.indices =
        ({⟨.A, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.C, 0, 0⟩,
          ⟨.D, 0, 0⟩, ⟨.E, 0, 0⟩, ⟨.F, 0, 0⟩} :
          Finset PeriodicSubtileIndex))
      (a : PeriodicSubtileIndex) (ha : a ∈ whole.indices) :
      a.first = 0 ∧ a.second = 0 := GeometricSectorGeometry.hzero q cfg C₀ T cert whole hidx a ha
  have hnoPinch (a b : PeriodicSubtileIndex)
      (ha : a.first = 0 ∧ a.second = 0)
      (hb : b.first = 0 ∧ b.second = 0) (hab : a ≠ b) :
      FootprintVertices (P.tile a) ∩ FootprintVertices (P.tile b) =
        CommonFootprintEdgeVertices (P.tile a) (P.tile b) := GeometricSectorAssembly.hnoPinch q
            cfg C₀ T cert hindexed hregular htiles hdisjoint raw_incident radial radialMembers a
            b ha hb hab
  intro whole hidx hwhole
  have hwholeTile : LatticeTile whole.unionTile :=
    FinitePatchTopology P.plane P.tile (PeriodicTileMultiplicityOne P)
      hindexed (fun a b _ hab => P.adjacent_has_common_edge a b hab) whole
  constructor
  · intro a ha b hb hab
    exact hnoPinch a b (hzero whole hidx a ha) (hzero whole hidx b hb) hab
  · intro d hd rest hrestIdx hrestUnion
    have hrestTile : LatticeTile rest.unionTile :=
      FinitePatchTopology P.plane P.tile (PeriodicTileMultiplicityOne P)
        hindexed (fun a b _ hab => P.adjacent_has_common_edge a b hab) rest
    have hdnot : d ∉ rest.indices := GeometricSectorGeometry.hdnot q cfg C₀ T cert whole d rest
        hrestIdx
    have hdisj : Disjoint (rest.unionTile).cells (P.tile d).cells :=
        GeometricSectorGeometry.hdisj q cfg C₀ T cert hindexed d rest hdnot
    have hunion : ∀ z : LatticeCell,
        z ∈ whole.unionTile.cells ↔ z ∈ (P.tile d).cells ∨
          z ∈ rest.unionTile.cells := GeometricSectorGeometry.hunion q cfg C₀ T cert whole hwhole
              d hd rest hrestUnion
    let n : PeriodicSubtileIndex := match d.label with
      | .A => ⟨.B, 0, 0⟩
      | .B => ⟨.A, 0, 0⟩
      | .C => ⟨.A, 0, 0⟩
      | .D => ⟨.A, 0, 0⟩
      | .E => ⟨.B, 0, 0⟩
      | .F => ⟨.A, 0, 0⟩
    have hdn : AllowedSubtileIncidence d n := GeometricSectorGeometry.hdn q cfg C₀ T cert hzero
        whole hidx d hd rest hrestIdx hrestUnion hunion
    have hnd : n ≠ d := GeometricSectorGeometry.hnd q cfg C₀ T cert hzero whole hidx d hd rest
        hrestIdx hrestUnion hunion
    have hnWhole : n ∈ whole.indices := GeometricSectorGeometry.hnWhole q cfg C₀ T cert hzero
        whole hidx d hd
    have hnrest : n ∈ rest.indices := GeometricSectorGeometry.hnrest q cfg C₀ T cert whole d rest
        hrestIdx hnd hnWhole
    have hneAdj : P.plane.adjacent d n :=
      (cert.modified_adjacency d n).mpr hdn
    have hcommon : (FootprintEdges (P.tile d) ∩
        FootprintEdges rest.unionTile).Nonempty := GeometricSectorGeometry.hcommon q cfg C₀ T
            cert d rest hnrest hneAdj
    have hinterface := LatticeTileDiskUnionInterface
      (P.tile d) rest.unionTile whole.unionTile (htiles d) hrestTile hwholeTile
      hdisj.symm hunion hcommon
    rcases hinterface with ⟨_, ⟨x, y, hpath⟩, hedges, hvertices⟩
    have hcommonComm :
        CommonFootprintEdgeVertices (P.tile d) rest.unionTile =
          CommonFootprintEdgeVertices rest.unionTile (P.tile d) :=
              GeometricSectorGeometry.hcommonComm q cfg C₀ T cert d rest
    exact ⟨x, y, by
      simpa [hcommonComm, Set.inter_comm] using hpath,
      by simpa [Set.inter_comm] using hedges,
      by simpa [hcommonComm, Set.inter_comm] using hvertices⟩

end ApollonianSuperharmonic

end
