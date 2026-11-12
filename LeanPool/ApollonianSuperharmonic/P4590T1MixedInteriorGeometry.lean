/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4590T1OppositeCellsStar
public import LeanPool.ApollonianSuperharmonic.P4339T1PrecursorSupportGeometry

-- [TABLET NODE: P4590T1MixedInteriorGeometry]

/-!
# P4590T1MixedInteriorGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace MixedInteriorGeometry

private theorem raw_incident :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (z : GaussianInt), (U.cells.Nonempty) → ((z ∈ FootprintVertices U) →
            (∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ U.cells)) ) := by
  classical
  intro U z hne hz
  simp only [FootprintVertices, hne, ite_true, Set.mem_ofPred_eq] at hz
  rcases hz with ⟨a, ha, rfl | rfl | rfl | rfl⟩
  · exact ⟨0, by simpa [LatticeVertexIncidentCell] using ha⟩
  · exact ⟨1, by simpa [LatticeVertexIncidentCell] using ha⟩
  · exact ⟨3, by simpa [LatticeVertexIncidentCell] using ha⟩
  · exact ⟨2, by simpa [LatticeVertexIncidentCell, sub_sub] using ha⟩

private theorem incident_foot :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (U : ProtoTile), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈
            U.cells) → (x ∈ FootprintVertices U) ) := by
  classical
  intro x U j hj
  rw [FootprintVertices, ite_eq_left ⟨LatticeVertexIncidentCell x j, hj⟩]
  refine ⟨LatticeVertexIncidentCell x j, hj, ?_⟩
  fin_cases j <;> simp [LatticeVertexIncidentCell, sub_eq_add_neg,
    add_assoc, add_comm, add_left_comm, Zsqrtd.ext_iff]

private theorem footprint_iff_incident :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), (∀ (U : ProtoTile), ∀ (z : GaussianInt), (U.cells.Nonempty)
            → ((z ∈ FootprintVertices U) → (∃ j : Fin 4, LatticeVertexIncidentCell z j ∈
            U.cells))) → ((∀ (i : Fin 3), ∀ (s : Bool), (cert.P i s).cells.Nonempty) → ((∀ (U :
            ProtoTile), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ U.cells) → (x ∈
            FootprintVertices U)) → (∀ (i : Fin 3), ∀ (s : Bool), x ∈ FootprintVertices (cert.P i
            s) ↔ ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ (cert.P i s).cells))) ) := by
  classical
  intro q cfg C T cert x raw_incident hparentNe incident_foot i s
  constructor
  · exact raw_incident (cert.P i s) x (hparentNe i s)
  · rintro ⟨j, hj⟩
    exact incident_foot (cert.P i s) j hj

private theorem noThirdBoundary :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt),
        let boundaryOwners := {is : Fin 3 × Bool //
          x ∈ BoundaryFootprintVertices (cert.P is.1 is.2)}
        (Fintype.card boundaryOwners = 2) → (∀ (a : Fin 3 × Bool), ∀ (b : Fin 3 × Bool), ∀ (c :
            Fin 3 × Bool), (a ≠ b) → ((a ≠ c) → ((b ≠ c) → ((x ∈ BoundaryFootprintVertices
            (cert.P a.1 a.2)) → ((x ∈ BoundaryFootprintVertices (cert.P b.1 b.2)) → (x ∉
            BoundaryFootprintVertices (cert.P c.1 c.2))))))) ) := by
  classical
  intro q cfg C T cert x boundaryOwners hboundaryOwnersCard a b c hab hac hbc ha hb hc
  let f : Fin 3 → boundaryOwners := fun n =>
    if h : n = 0 then ⟨a, ha⟩ else
    if h : n = 1 then ⟨b, hb⟩ else ⟨c, hc⟩
  have hf : Function.Injective f := by
    intro n m hnm
    have hv := congrArg Subtype.val hnm
    fin_cases n <;> fin_cases m <;> simp [f] at hv <;>
      simp_all []
  have hle := Fintype.card_le_of_injective f hf
  rw [hboundaryOwnersCard] at hle
  norm_num at hle

private theorem pair_boundary :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), (∀ (i : Fin 3), ∀ (s : Bool), x ∈ FootprintVertices (cert.P
            i s) ↔ ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ (cert.P i s).cells) → ((∀ (i :
            Fin 3), ∀ (j : Fin 3), ∀ (s : Bool), ∀ (t : Bool), ((i, s) ≠ (j, t)) → ((¬ (i = 0 ∧ j
            = 0)) → (Disjoint (cert.P i s).cells (cert.P j t).cells))) → (∀ (i : Fin 3), ∀ (j :
            Fin 3), ∀ (s : Bool), ∀ (t : Bool), ((i, s) ≠ (j, t)) → ((¬ (i = 0 ∧ j = 0)) → ((x ∈
            FootprintVertices (cert.P i s)) → ((x ∈ FootprintVertices (cert.P j t)) → (x ∈
            BoundaryFootprintVertices (cert.P i s) ∧ x ∈ BoundaryFootprintVertices (cert.P j
            t))))))) ) := by
  classical
  intro q cfg C T cert x footprint_iff_incident selected_disjoint i j s t hij hnot hi hj
  obtain ⟨ki, hki⟩ := (footprint_iff_incident i s).1 hi
  obtain ⟨kj, hkj⟩ := (footprint_iff_incident j t).1 hj
  refine ⟨?_, ?_⟩
  · apply P3161T2IncidentBoundary _ x ⟨ki, hki⟩
    refine ⟨kj, ?_⟩
    intro h
    exact (Finset.disjoint_left.mp (selected_disjoint i j s t hij hnot)) h hkj
  · apply P3161T2IncidentBoundary _ x ⟨kj, hkj⟩
    refine ⟨ki, ?_⟩
    intro h
    exact Finset.disjoint_left.mp (selected_disjoint i j s t hij hnot).symm h hki

private theorem noOtherFoot :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), (∀ (i : Fin 3), ∀ (s : Bool), x ∈ FootprintVertices (cert.P
            i s) ↔ ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ (cert.P i s).cells) → ((∀ (a :
            Fin 3 × Bool), ∀ (b : Fin 3 × Bool), ∀ (c : Fin 3 × Bool), (a ≠ b) → ((a ≠ c) → ((b ≠
            c) → ((x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)) → ((x ∈
            BoundaryFootprintVertices (cert.P b.1 b.2)) → (x ∉ BoundaryFootprintVertices (cert.P
            c.1 c.2))))))) → ((∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (s : Bool), ∀ (t : Bool), ((i, s)
            ≠ (j, t)) → ((¬ (i = 0 ∧ j = 0)) → ((x ∈ FootprintVertices (cert.P i s)) → ((x ∈
            FootprintVertices (cert.P j t)) → (x ∈ BoundaryFootprintVertices (cert.P i s) ∧ x ∈
            BoundaryFootprintVertices (cert.P j t)))))) → (∀ (a : Fin 3 × Bool), ∀ (b : Fin 3 ×
            Bool), ∀ (c : Fin 3 × Bool), (a ≠ b) → ((a ≠ c) → ((b ≠ c) → ((¬ (a.1 = 0 ∧ b.1 = 0))
            → ((Disjoint (cert.P a.1 a.2).cells (cert.P c.1 c.2).cells ∨
            Disjoint (cert.P b.1 b.2).cells (cert.P c.1 c.2).cells) → ((x ∈ FootprintVertices
                (cert.P a.1 a.2)) → ((x ∈ FootprintVertices (cert.P b.1 b.2)) → (x ∉
                FootprintVertices (cert.P c.1 c.2))))))))))) ) := by
  classical
  intro q cfg C T cert x footprint_iff_incident noThirdBoundary pair_boundary a b c hab hac hbc
      hnot hdisj ha hb
  have hba := (pair_boundary a.1 b.1 a.2 b.2 hab hnot ha hb).1
  have hbb := (pair_boundary a.1 b.1 a.2 b.2 hab hnot ha hb).2
  intro hc
  obtain ⟨jc, hjc⟩ := (footprint_iff_incident c.1 c.2).1 hc
  rcases hdisj with hdisj | hdisj
  · obtain ⟨ja, hja⟩ := (footprint_iff_incident a.1 a.2).1 ha
    have hjamiss : LatticeVertexIncidentCell x ja ∉ (cert.P c.1 c.2).cells :=
      Finset.disjoint_left.mp hdisj hja
    have hbc' := P3161T2IncidentBoundary _ x ⟨jc, hjc⟩ ⟨ja, hjamiss⟩
    exact noThirdBoundary a b c hab hac hbc hba hbb hbc'
  · obtain ⟨jb, hjb⟩ := (footprint_iff_incident b.1 b.2).1 hb
    have hjbmiss : LatticeVertexIncidentCell x jb ∉ (cert.P c.1 c.2).cells :=
      Finset.disjoint_left.mp hdisj hjb
    have hbc' := P3161T2IncidentBoundary _ x ⟨jc, hjc⟩ ⟨jb, hjbmiss⟩
    exact noThirdBoundary a b c hab hac hbc hba hbb hbc'

private theorem pair_cover :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells) → ((∀
            (U : ProtoTile), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ U.cells) → (x ∈
            FootprintVertices U)) → ((∀ (a : Fin 3 × Bool), ∀ (b : Fin 3 × Bool), ∀ (c : Fin 3 ×
            Bool), (a ≠ b) → ((a ≠ c) → ((b ≠ c) → ((¬ (a.1 = 0 ∧ b.1 = 0)) → ((Disjoint (cert.P
            a.1 a.2).cells (cert.P c.1 c.2).cells ∨ Disjoint (cert.P b.1 b.2).cells (cert.P c.1
            c.2).cells) → ((x ∈ FootprintVertices (cert.P a.1 a.2)) → ((x ∈ FootprintVertices
            (cert.P b.1 b.2)) → (x ∉ FootprintVertices (cert.P c.1 c.2))))))))) → (∀ (a : Fin 3 ×
            Bool), ∀ (b : Fin 3 × Bool), ∀ (c : Fin 3 × Bool), (a ≠ b) → ((a ≠ c) → ((b ≠ c) →
            ((¬ (a.1 = 0 ∧ b.1 = 0)) → ((∀ c', c' ≠ a → c' ≠ b →
            Disjoint (cert.P a.1 a.2).cells (cert.P c'.1 c'.2).cells ∨
              Disjoint (cert.P b.1 b.2).cells (cert.P c'.1 c'.2).cells) → ((x ∈ FootprintVertices
                  (cert.P a.1 a.2)) → ((x ∈ FootprintVertices (cert.P b.1 b.2)) → (∀ j : Fin 4,
                  LatticeVertexIncidentCell x j ∈ (cert.P a.1 a.2).cells ∨
                  LatticeVertexIncidentCell x j ∈ (cert.P b.1 b.2).cells)))))))))) ) := by
  classical
  intro q cfg C T cert x hstar incident_foot noOtherFoot a b c hab hac hbc hnot hthird ha hb j
  have hcell := hstar j
  obtain ⟨i, s, howner⟩ := (cert.outer_union _).1 hcell
  have hownerFoot := incident_foot (cert.P i s) j howner
  by_cases hia : (i, s) = a
  · exact Or.inl (hia ▸ howner)
  by_cases hib : (i, s) = b
  · exact Or.inr (hib ▸ howner)
  · exact (noOtherFoot a b (i, s) hab (fun h => hia h.symm)
      (fun h => hib h.symm) hnot
      (hthird (i, s) hia hib) ha hb hownerFoot).elim

private theorem pair_result :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), (∀ (i : Fin 3), ∀ (s : Bool), x ∈ FootprintVertices (cert.P
            i s) ↔ ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ (cert.P i s).cells) → ((∀ (i :
            Fin 3), ∀ (j : Fin 3), ∀ (s : Bool), ∀ (t : Bool), ((i, s) ≠ (j, t)) → ((¬ (i = 0 ∧ j
            = 0)) → (Disjoint (cert.P i s).cells (cert.P j t).cells))) → ((∀ (i : Fin 3), ∀ (j :
            Fin 3), ∀ (s : Bool), ∀ (t : Bool), ((i, s) ≠ (j, t)) → ((¬ (i = 0 ∧ j = 0)) → ((x ∈
            FootprintVertices (cert.P i s)) → ((x ∈ FootprintVertices (cert.P j t)) → (x ∈
            BoundaryFootprintVertices (cert.P i s) ∧ x ∈ BoundaryFootprintVertices (cert.P j
            t)))))) → ((∀ (a : Fin 3 × Bool), ∀ (b : Fin 3 × Bool), ∀ (c : Fin 3 × Bool), (a ≠ b)
            → ((a ≠ c) → ((b ≠ c) → ((¬ (a.1 = 0 ∧ b.1 = 0)) → ((Disjoint (cert.P a.1 a.2).cells
            (cert.P c.1 c.2).cells ∨ Disjoint (cert.P b.1 b.2).cells (cert.P c.1 c.2).cells) →
            ((x ∈ FootprintVertices (cert.P a.1 a.2)) → ((x ∈ FootprintVertices (cert.P b.1 b.2))
            → (x ∉ FootprintVertices (cert.P c.1 c.2))))))))) → ((∀ (a : Fin 3 × Bool), ∀ (b :
            Fin 3 × Bool), ∀ (c : Fin 3 × Bool), (a ≠ b) → ((a ≠ c) → ((b ≠ c) → ((¬ (a.1 = 0 ∧
            b.1 = 0)) → ((∀ c', c' ≠ a → c' ≠ b → Disjoint (cert.P a.1 a.2).cells (cert.P c'.1
            c'.2).cells ∨ Disjoint (cert.P b.1 b.2).cells (cert.P c'.1 c'.2).cells) → ((x ∈
            FootprintVertices (cert.P a.1 a.2)) → ((x ∈ FootprintVertices (cert.P b.1 b.2)) → (∀
            j : Fin 4, LatticeVertexIncidentCell x j ∈ (cert.P a.1 a.2).cells ∨
            LatticeVertexIncidentCell x j ∈ (cert.P b.1 b.2).cells)))))))) → (∀ (a : Fin 3 ×
            Bool), ∀ (b : Fin 3 × Bool), ∀ (k : Fin 3 × Bool), (a ≠ b) → ((a ≠ k) → ((b ≠ k) →
            ((¬ (a.1 = 0 ∧ b.1 = 0)) → ((∀ c', c' ≠ a → c' ≠ b →
            Disjoint (cert.P a.1 a.2).cells (cert.P c'.1 c'.2).cells ∨
              Disjoint (cert.P b.1 b.2).cells (cert.P c'.1 c'.2).cells) → ((x ∈ FootprintVertices
                  (cert.P a.1 a.2)) → ((x ∈ FootprintVertices (cert.P b.1 b.2)) → ((∀ y, y = x ∨
                  y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ → y ∈ FootprintVertices
                  (cert.P a.1 a.2) ∨ y ∈ FootprintVertices (cert.P b.1 b.2)) ∧ x ∉
                  FootprintVertices (cert.P k.1 k.2))))))))))))) ) := by
  classical
  intro q cfg C T cert x footprint_iff_incident selected_disjoint pair_boundary noOtherFoot
      pair_cover a b k hab hak hbk hnot hthird ha hb
  have hdisjAB := selected_disjoint a.1 b.1 a.2 b.2 hab hnot
  have hboundaryAB := pair_boundary a.1 b.1 a.2 b.2 hab hnot ha hb
  have hcover := pair_cover a b k hab hak hbk hnot hthird ha hb
  have hU := (footprint_iff_incident a.1 a.2).1 ha
  have hV := (footprint_iff_incident b.1 b.2).1 hb
  have hchecker := (LatticeTileGridStructure (cert.P a.1 a.2)
    (cert.parent_lattice a.1 a.2)).2.1 x
  have hopposite : ∃ j : Fin 4,
      (LatticeVertexIncidentCell x j ∈ (cert.P a.1 a.2).cells ∧
        LatticeVertexIncidentCell x (j + 2) ∈ (cert.P b.1 b.2).cells) ∨
      (LatticeVertexIncidentCell x j ∈ (cert.P b.1 b.2).cells ∧
        LatticeVertexIncidentCell x (j + 2) ∈ (cert.P a.1 a.2).cells) := by
    by_contra hn
    have same02 : (LatticeVertexIncidentCell x 0 ∈ (cert.P a.1 a.2).cells ↔
        LatticeVertexIncidentCell x 2 ∈ (cert.P a.1 a.2).cells) := by
      constructor
      · intro h0
        rcases hcover 2 with h2 | h2
        · exact h2
        · exact (hn ⟨0, Or.inl ⟨h0, by simpa using h2⟩⟩).elim
      · intro h2
        rcases hcover 0 with h0 | h0
        · exact h0
        · exact (hn ⟨0, Or.inr ⟨by simpa using h0, h2⟩⟩).elim
    have same13 : (LatticeVertexIncidentCell x 1 ∈ (cert.P a.1 a.2).cells ↔
        LatticeVertexIncidentCell x 3 ∈ (cert.P a.1 a.2).cells) := by
      constructor
      · intro h1
        rcases hcover 3 with h3 | h3
        · exact h3
        · exact (hn ⟨1, Or.inl ⟨h1, by simpa using h3⟩⟩).elim
      · intro h3
        rcases hcover 1 with h1 | h1
        · exact h1
        · exact (hn ⟨1, Or.inr ⟨by simpa using h1, h3⟩⟩).elim
    by_cases h0 : LatticeVertexIncidentCell x 0 ∈ (cert.P a.1 a.2).cells
    · by_cases h1 : LatticeVertexIncidentCell x 1 ∈ (cert.P a.1 a.2).cells
      · have h2 := same02.1 h0
        have h3 := same13.1 h1
        obtain ⟨j, hj⟩ := hV
        have hallU : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            (cert.P a.1 a.2).cells := by
          intro j
          fin_cases j <;> simpa [LatticeVertexIncidentCell] using
            (by
              first
              | exact h0
              | exact h1
              | exact h2
              | exact h3)
        exact (Finset.disjoint_left.mp hdisjAB (hallU j) hj).elim
      · have h2 := same02.1 h0
        have h3not : LatticeVertexIncidentCell x 3 ∉ (cert.P a.1 a.2).cells := by
          intro h3
          exact h1 (same13.2 h3)
        have hbad : (LatticeVertexIncidentCell x 0 ∈ (cert.P a.1 a.2).cells ∧
            LatticeVertexIncidentCell x 2 ∈ (cert.P a.1 a.2).cells ∧
            LatticeVertexIncidentCell x 1 ∉ (cert.P a.1 a.2).cells ∧
            LatticeVertexIncidentCell x 3 ∉ (cert.P a.1 a.2).cells) ∨
            (LatticeVertexIncidentCell x 1 ∈ (cert.P a.1 a.2).cells ∧
            LatticeVertexIncidentCell x 3 ∈ (cert.P a.1 a.2).cells ∧
            LatticeVertexIncidentCell x 0 ∉ (cert.P a.1 a.2).cells ∧
            LatticeVertexIncidentCell x 2 ∉ (cert.P a.1 a.2).cells) := Or.inl ⟨h0, h2, h1, h3not⟩
        exact hchecker (by simpa [NoCheckerboardCellVertex,
          LatticeVertexIncidentCell] using hbad)
    · by_cases h1 : LatticeVertexIncidentCell x 1 ∈ (cert.P a.1 a.2).cells
      · have h2not : LatticeVertexIncidentCell x 2 ∉ (cert.P a.1 a.2).cells := by
          intro h2
          exact h0 (same02.2 h2)
        have h3 := same13.1 h1
        have hbad : (LatticeVertexIncidentCell x 0 ∈ (cert.P a.1 a.2).cells ∧
            LatticeVertexIncidentCell x 2 ∈ (cert.P a.1 a.2).cells ∧
            LatticeVertexIncidentCell x 1 ∉ (cert.P a.1 a.2).cells ∧
            LatticeVertexIncidentCell x 3 ∉ (cert.P a.1 a.2).cells) ∨
            (LatticeVertexIncidentCell x 1 ∈ (cert.P a.1 a.2).cells ∧
            LatticeVertexIncidentCell x 3 ∈ (cert.P a.1 a.2).cells ∧
            LatticeVertexIncidentCell x 0 ∉ (cert.P a.1 a.2).cells ∧
            LatticeVertexIncidentCell x 2 ∉ (cert.P a.1 a.2).cells) := Or.inr ⟨h1, h3, h0, h2not⟩
        exact hchecker (by simpa [NoCheckerboardCellVertex,
          LatticeVertexIncidentCell] using hbad)
      · have h2not : LatticeVertexIncidentCell x 2 ∉ (cert.P a.1 a.2).cells :=
          fun h => h0 (same02.2 h)
        have h3not : LatticeVertexIncidentCell x 3 ∉ (cert.P a.1 a.2).cells :=
          fun h => h1 (same13.2 h)
        obtain ⟨j, hj⟩ := hU
        fin_cases j
        · exact h0 (by simpa [LatticeVertexIncidentCell] using hj)
        · exact h1 (by simpa [LatticeVertexIncidentCell] using hj)
        · exact h2not (by simpa [LatticeVertexIncidentCell] using hj)
        · exact h3not (by simpa [LatticeVertexIncidentCell] using hj)
  have hstar' := P4590T1OppositeCellsStar
    (cert.P a.1 a.2) (cert.P b.1 b.2) x (by
      obtain ⟨j, h⟩ := hopposite
      rcases h with h | h
      · exact ⟨j, h⟩
      · let j' : Fin 4 := j + 2
        have hj' : j' + 2 = j := by fin_cases j <;> decide
        exact ⟨j', h.2, by rw [hj']; exact h.1⟩)
  refine ⟨hstar', ?_⟩
  exact noOtherFoot a b k hab hak hbk hnot
    (hthird k (fun h => hak h.symm) (fun h => hbk h.symm)) ha hb

private theorem hthirdAD :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (s : Bool), ∀ (t : Bool), ((i, s) ≠ (j, t)) →
            ((¬ (i = 0 ∧ j = 0)) → (Disjoint (cert.P i s).cells (cert.P j t).cells))) → (
        let A : Fin 3 × Bool := (0, true)
        let D : Fin 3 × Bool := (1, false)
        ∀ c', c' ≠ A → c' ≠ D → Disjoint (cert.P A.1 A.2).cells (cert.P c'.1 c'.2).cells ∨
            Disjoint (cert.P D.1 D.2).cells (cert.P c'.1 c'.2).cells) ) := by
  classical
  intro q cfg C T cert selected_disjoint A D c' hca hcd
  rcases c' with ⟨i, s⟩
  fin_cases i <;> cases s
  all_goals first
  | exact Or.inl (selected_disjoint _ _ _ _ (by decide) (by decide))
  | exact Or.inr (selected_disjoint _ _ _ _ (by decide) (by decide))

private theorem hthirdAF :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (s : Bool), ∀ (t : Bool), ((i, s) ≠ (j, t)) →
            ((¬ (i = 0 ∧ j = 0)) → (Disjoint (cert.P i s).cells (cert.P j t).cells))) → (
        let A : Fin 3 × Bool := (0, true)
        let F : Fin 3 × Bool := (2, false)
        ∀ c', c' ≠ A → c' ≠ F → Disjoint (cert.P A.1 A.2).cells (cert.P c'.1 c'.2).cells ∨
            Disjoint (cert.P F.1 F.2).cells (cert.P c'.1 c'.2).cells) ) := by
  classical
  intro q cfg C T cert selected_disjoint A F c' hca hcf
  rcases c' with ⟨i, s⟩
  fin_cases i <;> cases s
  all_goals first
  | exact Or.inl (selected_disjoint _ _ _ _ (by decide) (by decide))
  | exact Or.inr (selected_disjoint _ _ _ _ (by decide) (by decide))

private theorem hthirdCB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (s : Bool), ∀ (t : Bool), ((i, s) ≠ (j, t)) →
            ((¬ (i = 0 ∧ j = 0)) → (Disjoint (cert.P i s).cells (cert.P j t).cells))) → (
        let B : Fin 3 × Bool := (0, false)
        let C' : Fin 3 × Bool := (1, true)
        ∀ c', c' ≠ C' → c' ≠ B → Disjoint (cert.P C'.1 C'.2).cells (cert.P c'.1 c'.2).cells ∨
            Disjoint (cert.P B.1 B.2).cells (cert.P c'.1 c'.2).cells) ) := by
  classical
  intro q cfg C T cert selected_disjoint B C' c' hcc hcb
  rcases c' with ⟨i, s⟩
  fin_cases i <;> cases s
  all_goals first
  | exact Or.inl (selected_disjoint _ _ _ _ (by decide) (by decide))
  | exact Or.inr (selected_disjoint _ _ _ _ (by decide) (by decide))

private theorem hthirdEB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (s : Bool), ∀ (t : Bool), ((i, s) ≠ (j, t)) →
            ((¬ (i = 0 ∧ j = 0)) → (Disjoint (cert.P i s).cells (cert.P j t).cells))) → (
        let B : Fin 3 × Bool := (0, false)
        let E : Fin 3 × Bool := (2, true)
        ∀ c', c' ≠ E → c' ≠ B → Disjoint (cert.P E.1 E.2).cells (cert.P c'.1 c'.2).cells ∨
            Disjoint (cert.P B.1 B.2).cells (cert.P c'.1 c'.2).cells) ) := by
  classical
  intro q cfg C T cert selected_disjoint B E c' hce hcb
  rcases c' with ⟨i, s⟩
  fin_cases i <;> cases s
  all_goals first
  | exact Or.inl (selected_disjoint _ _ _ _ (by decide) (by decide))
  | exact Or.inr (selected_disjoint _ _ _ _ (by decide) (by decide))

private theorem hthirdCF :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (s : Bool), ∀ (t : Bool), ((i, s) ≠ (j, t)) →
            ((¬ (i = 0 ∧ j = 0)) → (Disjoint (cert.P i s).cells (cert.P j t).cells))) → (
        let C' : Fin 3 × Bool := (1, true)
        let F : Fin 3 × Bool := (2, false)
        ∀ c', c' ≠ C' → c' ≠ F → Disjoint (cert.P C'.1 C'.2).cells (cert.P c'.1 c'.2).cells ∨
            Disjoint (cert.P F.1 F.2).cells (cert.P c'.1 c'.2).cells) ) := by
  classical
  intro q cfg C T cert selected_disjoint C' F c' hcc hcf
  rcases c' with ⟨i, s⟩
  fin_cases i <;> cases s
  all_goals first
  | exact Or.inl (selected_disjoint _ _ _ _ (by decide) (by decide))
  | exact Or.inr (selected_disjoint _ _ _ _ (by decide) (by decide))

private theorem hthirdED :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (s : Bool), ∀ (t : Bool), ((i, s) ≠ (j, t)) →
            ((¬ (i = 0 ∧ j = 0)) → (Disjoint (cert.P i s).cells (cert.P j t).cells))) → (
        let D : Fin 3 × Bool := (1, false)
        let E : Fin 3 × Bool := (2, true)
        ∀ c', c' ≠ E → c' ≠ D → Disjoint (cert.P E.1 E.2).cells (cert.P c'.1 c'.2).cells ∨
            Disjoint (cert.P D.1 D.2).cells (cert.P c'.1 c'.2).cells) ) := by
  classical
  intro q cfg C T cert selected_disjoint D E c' hce hcd
  rcases c' with ⟨i, s⟩
  fin_cases i <;> cases s
  all_goals first
  | exact Or.inl (selected_disjoint _ _ _ _ (by decide) (by decide))
  | exact Or.inr (selected_disjoint _ _ _ _ (by decide) (by decide))

end MixedInteriorGeometry

theorem P4590T1MixedInteriorGeometry
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q) (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (hT : LatticeTile T) (x : GaussianInt)
    (hx : x ∈ FootprintVertices T) (hxb : x ∉ BoundaryFootprintVertices T)
    (hk : Nat.card {is : Fin 3 × Bool //
      x ∈ BoundaryFootprintVertices (cert.P is.1 is.2)} = 2) :
    (x ∈ FootprintVertices (cert.P 0 true) → x ∈ FootprintVertices (cert.P 1 false) →
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.P 0 true) ∨ y ∈ FootprintVertices (cert.P 1 false)) ∧
        x ∉ FootprintVertices (cert.P 0 false)) ∧
    (x ∈ FootprintVertices (cert.P 0 true) → x ∈ FootprintVertices (cert.P 2 false) →
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.P 0 true) ∨ y ∈ FootprintVertices (cert.P 2 false)) ∧
        x ∉ FootprintVertices (cert.P 1 true)) ∧
    (x ∈ FootprintVertices (cert.P 1 true) → x ∈ FootprintVertices (cert.P 0 false) →
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.P 1 true) ∨ y ∈ FootprintVertices (cert.P 0 false)) ∧
        x ∉ FootprintVertices (cert.P 0 true)) ∧
    (x ∈ FootprintVertices (cert.P 2 true) → x ∈ FootprintVertices (cert.P 0 false) →
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.P 2 true) ∨ y ∈ FootprintVertices (cert.P 0 false)) ∧
        x ∉ FootprintVertices (cert.P 1 false)) ∧
    (x ∈ FootprintVertices (cert.P 1 true) → x ∈ FootprintVertices (cert.P 2 false) →
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.P 1 true) ∨ y ∈ FootprintVertices (cert.P 2 false)) ∧
        x ∉ FootprintVertices (cert.P 0 true)) ∧
    (x ∈ FootprintVertices (cert.P 2 true) → x ∈ FootprintVertices (cert.P 1 false) →
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.P 2 true) ∨ y ∈ FootprintVertices (cert.P 1 false)) ∧
        x ∉ FootprintVertices (cert.P 0 false)) := by
-- BODY
  classical
  have hTne : T.cells.Nonempty :=
    (LatticeTileGridStructure T hT).1.1
  have raw_incident (U : ProtoTile) (z : GaussianInt)
      (hne : U.cells.Nonempty) (hz : z ∈ FootprintVertices U) :
      ∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ U.cells := MixedInteriorGeometry.raw_incident
          U z hne hz
  have hstar : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells :=
    (P4456T2VertexInterior T hTne x hx).2.mp hxb
  have hparentNe (i : Fin 3) (s : Bool) :
      (cert.P i s).cells.Nonempty :=
    (LatticeTileGridStructure _ (cert.parent_lattice i s)).1.1
  have hprec := P4339T1PrecursorSupportGeometry C q cfg T cert
  have hsep : ∀ (i : Fin 3) (s : Bool) (j : Fin 3) (t : Bool),
      (i, s) ≠ (j, t) → ¬ (i = 0 ∧ j = 0) →
      Disjoint (cert.P i s).cells (cert.P j t).cells := hprec.2.2.2.2.2.2.2
  have hzero : (cert.P 0 true).cells ∩ (cert.P 0 false).cells = cert.O.cells :=
    hprec.2.2.2.2.2.2.1
  have hboundaryCount : Nat.card {is : Fin 3 × Bool //
      x ∈ BoundaryFootprintVertices (cert.P is.1 is.2)} = 2 := hk
  have incident_foot (U : ProtoTile) (j : Fin 4)
      (hj : LatticeVertexIncidentCell x j ∈ U.cells) :
      x ∈ FootprintVertices U := MixedInteriorGeometry.incident_foot x U j hj
  have footprint_iff_incident (i : Fin 3) (s : Bool) :
      x ∈ FootprintVertices (cert.P i s) ↔
        ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ (cert.P i s).cells :=
            MixedInteriorGeometry.footprint_iff_incident q cfg C T cert x raw_incident hparentNe
            incident_foot i s
  have selected_disjoint (i j : Fin 3) (s t : Bool)
      (hij : (i, s) ≠ (j, t)) (hnot : ¬ (i = 0 ∧ j = 0)) :
      Disjoint (cert.P i s).cells (cert.P j t).cells := hsep i s j t hij hnot
  let boundaryOwners := {is : Fin 3 × Bool //
    x ∈ BoundaryFootprintVertices (cert.P is.1 is.2)}
  have hboundaryOwnersCard : Fintype.card boundaryOwners = 2 := by
    simpa [boundaryOwners, Nat.card_eq_fintype_card] using hboundaryCount
  have noThirdBoundary (a b c : Fin 3 × Bool)
      (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (ha : x ∈ BoundaryFootprintVertices (cert.P a.1 a.2))
      (hb : x ∈ BoundaryFootprintVertices (cert.P b.1 b.2)) :
      x ∉ BoundaryFootprintVertices (cert.P c.1 c.2) := MixedInteriorGeometry.noThirdBoundary q
          cfg C T cert x hboundaryOwnersCard a b c hab hac hbc ha hb
  have pair_boundary (i j : Fin 3) (s t : Bool)
      (hij : (i, s) ≠ (j, t)) (hnot : ¬ (i = 0 ∧ j = 0))
      (hi : x ∈ FootprintVertices (cert.P i s))
      (hj : x ∈ FootprintVertices (cert.P j t)) :
      x ∈ BoundaryFootprintVertices (cert.P i s) ∧
        x ∈ BoundaryFootprintVertices (cert.P j t) := MixedInteriorGeometry.pair_boundary q cfg C
            T cert x footprint_iff_incident selected_disjoint i j s t hij hnot hi hj
  have noOtherFoot (a b c : Fin 3 × Bool)
      (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (hnot : ¬ (a.1 = 0 ∧ b.1 = 0))
      (hdisj : Disjoint (cert.P a.1 a.2).cells (cert.P c.1 c.2).cells ∨
        Disjoint (cert.P b.1 b.2).cells (cert.P c.1 c.2).cells)
      (ha : x ∈ FootprintVertices (cert.P a.1 a.2))
      (hb : x ∈ FootprintVertices (cert.P b.1 b.2)) :
      x ∉ FootprintVertices (cert.P c.1 c.2) := MixedInteriorGeometry.noOtherFoot q cfg C T cert
          x footprint_iff_incident noThirdBoundary pair_boundary a b c hab hac hbc hnot hdisj ha hb
  have pair_cover (a b c : Fin 3 × Bool)
      (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (hnot : ¬ (a.1 = 0 ∧ b.1 = 0))
      (hthird : ∀ c', c' ≠ a → c' ≠ b →
        Disjoint (cert.P a.1 a.2).cells (cert.P c'.1 c'.2).cells ∨
          Disjoint (cert.P b.1 b.2).cells (cert.P c'.1 c'.2).cells)
      (ha : x ∈ FootprintVertices (cert.P a.1 a.2))
      (hb : x ∈ FootprintVertices (cert.P b.1 b.2)) :
      ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ (cert.P a.1 a.2).cells ∨
        LatticeVertexIncidentCell x j ∈ (cert.P b.1 b.2).cells :=
            MixedInteriorGeometry.pair_cover q cfg C T cert x hstar incident_foot noOtherFoot a b
            c hab hac hbc hnot hthird ha hb
  have pair_result (a b k : Fin 3 × Bool)
      (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k)
      (hnot : ¬ (a.1 = 0 ∧ b.1 = 0))
      (hthird : ∀ c', c' ≠ a → c' ≠ b →
        Disjoint (cert.P a.1 a.2).cells (cert.P c'.1 c'.2).cells ∨
          Disjoint (cert.P b.1 b.2).cells (cert.P c'.1 c'.2).cells)
      (ha : x ∈ FootprintVertices (cert.P a.1 a.2))
      (hb : x ∈ FootprintVertices (cert.P b.1 b.2)) :
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.P a.1 a.2) ∨
          y ∈ FootprintVertices (cert.P b.1 b.2)) ∧
        x ∉ FootprintVertices (cert.P k.1 k.2) := MixedInteriorGeometry.pair_result q cfg C T
            cert x footprint_iff_incident selected_disjoint pair_boundary noOtherFoot pair_cover
            a b k hab hak hbk hnot hthird ha hb
  let A : Fin 3 × Bool := (0, true)
  let B : Fin 3 × Bool := (0, false)
  let C' : Fin 3 × Bool := (1, true)
  let D : Fin 3 × Bool := (1, false)
  let E : Fin 3 × Bool := (2, true)
  let F : Fin 3 × Bool := (2, false)
  have hthirdAD : ∀ c', c' ≠ A → c' ≠ D →
      Disjoint (cert.P A.1 A.2).cells (cert.P c'.1 c'.2).cells ∨
        Disjoint (cert.P D.1 D.2).cells (cert.P c'.1 c'.2).cells :=
            MixedInteriorGeometry.hthirdAD q cfg C T cert selected_disjoint
  have hthirdAF : ∀ c', c' ≠ A → c' ≠ F →
      Disjoint (cert.P A.1 A.2).cells (cert.P c'.1 c'.2).cells ∨
        Disjoint (cert.P F.1 F.2).cells (cert.P c'.1 c'.2).cells :=
            MixedInteriorGeometry.hthirdAF q cfg C T cert selected_disjoint
  have hthirdCB : ∀ c', c' ≠ C' → c' ≠ B →
      Disjoint (cert.P C'.1 C'.2).cells (cert.P c'.1 c'.2).cells ∨
        Disjoint (cert.P B.1 B.2).cells (cert.P c'.1 c'.2).cells :=
            MixedInteriorGeometry.hthirdCB q cfg C T cert selected_disjoint
  have hthirdEB : ∀ c', c' ≠ E → c' ≠ B →
      Disjoint (cert.P E.1 E.2).cells (cert.P c'.1 c'.2).cells ∨
        Disjoint (cert.P B.1 B.2).cells (cert.P c'.1 c'.2).cells :=
            MixedInteriorGeometry.hthirdEB q cfg C T cert selected_disjoint
  have hthirdCF : ∀ c', c' ≠ C' → c' ≠ F →
      Disjoint (cert.P C'.1 C'.2).cells (cert.P c'.1 c'.2).cells ∨
        Disjoint (cert.P F.1 F.2).cells (cert.P c'.1 c'.2).cells :=
            MixedInteriorGeometry.hthirdCF q cfg C T cert selected_disjoint
  have hthirdED : ∀ c', c' ≠ E → c' ≠ D →
      Disjoint (cert.P E.1 E.2).cells (cert.P c'.1 c'.2).cells ∨
        Disjoint (cert.P D.1 D.2).cells (cert.P c'.1 c'.2).cells :=
            MixedInteriorGeometry.hthirdED q cfg C T cert selected_disjoint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ha hd
    exact pair_result A D B (by decide) (by decide) (by decide) (by simp [A, D])
      hthirdAD ha hd
  · intro ha hf
    exact pair_result A F C' (by decide) (by decide) (by decide) (by simp [A, F])
      hthirdAF ha hf
  · intro hc hb
    exact pair_result C' B A (by decide) (by decide) (by decide) (by simp [C', B])
      hthirdCB hc hb
  · intro he hb
    exact pair_result E B D (by decide) (by decide) (by decide) (by simp [E, B])
      hthirdEB he hb
  · intro hc hf
    exact pair_result C' F A (by decide) (by decide) (by decide) (by simp [C', F])
      hthirdCF hc hf
  · intro he hd
    exact pair_result E D B (by decide) (by decide) (by decide) (by simp [E, D])
      hthirdED he hd

end ApollonianSuperharmonic

end
