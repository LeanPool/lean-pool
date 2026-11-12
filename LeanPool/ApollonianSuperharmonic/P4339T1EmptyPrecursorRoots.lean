/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4339T1PrecursorSupportGeometry
public import LeanPool.ApollonianSuperharmonic.P3161T2IncidentBoundary

-- [TABLET NODE: P4339T1EmptyPrecursorRoots]

/-!
# P4339T1EmptyPrecursorRoots

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4339T1EmptyPrecursorRoots
    (C : BandCircle) (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (D P : Finset GaussianInt)
    (hD : ∀ x, x ∈ D ↔
      x ∈ FootprintVertices T ∧ x ∉ BoundaryFootprintVertices T)
    (hP : ∀ x, x ∈ P ↔ x ∈ D ∧ ∃ i s,
      x ∈ FootprintVertices (cert.P i s) ∧
        x ∉ BoundaryFootprintVertices (cert.P i s))
    (hO : cert.O.cells = ∅) :
    let W := D \ P
    let R : Finset GaussianInt := {cert.precursor_boundary.a, cert.precursor_boundary.b}
    R ⊆ W ∧
    (∀ x ∈ W, x ∈ FootprintVertices cert.O ↔ x ∈ R) ∧
    (∀ x ∈ R,
      Nat.card {is : Fin 3 × Bool //
        x ∈ BoundaryFootprintVertices (cert.P is.1 is.2)} = 2 ∧
      GaussianRealPoint x = TileCentroid T) := by
-- BODY
  classical
  dsimp only
  obtain ⟨hcent, _, _, _, hQ, hS, hpair, hdisjoint⟩ :=
    P4339T1PrecursorSupportGeometry C q cfg T cert
  obtain ⟨hab, hanchor⟩ : cert.precursor_boundary.a = cert.precursor_boundary.b ∧
      cert.precursor_boundary.a = cert.O.anchor := by
    rcases cert.precursor_boundary.branch with hp | ⟨_, hab, ha, _⟩
    · exact ((Finset.nonempty_iff_ne_empty.mp hp.1) hO).elim
    · exact ⟨hab, ha⟩
  let a := cert.precursor_boundary.a
  have hR (x : GaussianInt) :
      x ∈ ({cert.precursor_boundary.a, cert.precursor_boundary.b} :
        Finset GaussianInt) ↔ x = a := by
    simp [← hab, a]
  have hfootO (x : GaussianInt) : x ∈ FootprintVertices cert.O ↔ x = a := by
    simp [FootprintVertices, hO, ← hanchor, a]
  have hpoint : GaussianRealPoint a = TileCentroid T := by
    calc
      GaussianRealPoint a = TileCentroid cert.O := by
        simp [TileCentroid, hO, GaussianRealPoint, ← hanchor, a]
      _ = TileCentroid T := hcent
  have raw_incident (U : ProtoTile) (x : GaussianInt) (hn : U.cells.Nonempty)
      (hx : x ∈ FootprintVertices U) :
      ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells := by
    as_aux_lemma =>
    clear * - U x hn hx
    rw [FootprintVertices, ite_eq_left hn] at hx
    obtain ⟨z, hz, rfl | rfl | rfl | rfl⟩ := hx
    · exact ⟨0, hz⟩
    · exact ⟨1, by simpa [LatticeVertexIncidentCell] using hz⟩
    · exact ⟨3, by simpa [LatticeVertexIncidentCell] using hz⟩
    · refine ⟨2, ?_⟩
      change z + 1 + ⟨0, 1⟩ - 1 - ⟨0, 1⟩ ∈ U.cells
      convert hz using 1; abel
  have boundary_incident (U : ProtoTile) (x : GaussianInt) (hn : U.cells.Nonempty)
      (hx : x ∈ BoundaryFootprintVertices U) :
      ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells := by
    as_aux_lemma =>
    clear * - U x hn hx
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
  have full_nonboundary (U : ProtoTile) (x : GaussianInt)
      (hall : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells) :
      x ∉ BoundaryFootprintVertices U := by
    as_aux_lemma =>
    clear * - U x hall
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
  have trans_zero (U : ProtoTile) : TileTranslation U 0 = U := by
    cases U
    simp [TileTranslation, GaussianTranslation, show GaussianTranslation 0 = id from
      funext (fun z => add_zero z)]
  have hallAB : ∀ j : Fin 4,
      LatticeVertexIncidentCell a j ∈ (cert.P 0 true).cells ∨
        LatticeVertexIncidentCell a j ∈ (cert.P 0 false).cells := by
    intro j
    have hcorner : a ∈ FootprintVertices
        (⟨{LatticeVertexIncidentCell a j}, LatticeVertexIncidentCell a j⟩ : ProtoTile) := by
      rw [FootprintVertices, ite_eq_left (Finset.singleton_nonempty _)]
      refine ⟨LatticeVertexIncidentCell a j, by simp, ?_⟩
      fin_cases j <;> simp [LatticeVertexIncidentCell, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc]
    have hisolated := cert.precursor_isolated 0 0 a
      (by simpa only [Int.cast_zero, zero_mul, zero_add, trans_zero] using
        (hfootO a).mpr rfl) (LatticeVertexIncidentCell a j) hcorner
    simpa only [SubtileOccurrenceInterpretation, Int.cast_zero, zero_mul,
      zero_add, trans_zero] using hisolated
  have hfirst := (cert.precursor_boundary.first_transition a).mpr rfl
  obtain ⟨jA, hjA⟩ := boundary_incident _ a hQ hfirst.1
  obtain ⟨jB, hjB⟩ := boundary_incident _ a hS hfirst.2.1
  have hA : LatticeVertexIncidentCell a jA ∈ (cert.P 0 true).cells :=
    (Finset.mem_sdiff.mp (cert.precursor_boundary.first_plus_child hjA)).1
  have hB : LatticeVertexIncidentCell a jB ∈ (cert.P 0 false).cells :=
    (Finset.mem_sdiff.mp (cert.precursor_boundary.first_minus_child hjB)).1
  have hAB : Disjoint (cert.P 0 true).cells (cert.P 0 false).cells :=
    Finset.disjoint_iff_inter_eq_empty.mpr (hpair.trans hO)
  have hboundaryA : a ∈ BoundaryFootprintVertices (cert.P 0 true) :=
    P3161T2IncidentBoundary _ a ⟨jA, hA⟩
      ⟨jB, fun hc => Finset.disjoint_left.mp hAB hc hB⟩
  have hboundaryB : a ∈ BoundaryFootprintVertices (cert.P 0 false) :=
    P3161T2IncidentBoundary _ a ⟨jB, hB⟩
      ⟨jA, fun hc => Finset.disjoint_left.mp hAB hA hc⟩
  have other_absent (i : Fin 3) (s : Bool) (hi : i ≠ 0) (j : Fin 4) :
      LatticeVertexIncidentCell a j ∉ (cert.P i s).cells := by
    intro hc
    rcases hallAB j with ht | hf
    · exact Finset.disjoint_left.mp
        (hdisjoint i s 0 true (fun he => hi (congrArg Prod.fst he))
          (fun he => hi he.1)) hc ht
    · exact Finset.disjoint_left.mp
        (hdisjoint i s 0 false (fun he => hi (congrArg Prod.fst he))
          (fun he => hi he.1)) hc hf
  have hboundary (i : Fin 3) (s : Bool) :
      a ∈ BoundaryFootprintVertices (cert.P i s) ↔ i = 0 := by
    by_cases hi : i = 0
    · subst i
      cases s <;> simp only [iff_true] <;> assumption
    · refine ⟨fun hb => ?_, fun he => (hi he).elim⟩
      obtain ⟨j, hj⟩ := boundary_incident _ a
        (LatticeTileGridStructure _ (cert.parent_lattice i s)).1.1 hb
      exact (other_absent i s hi j hj).elim
  have hallT (j : Fin 4) : LatticeVertexIncidentCell a j ∈ T.cells := by
    rcases hallAB j with ht | hf
    · exact (cert.outer_union _).mpr ⟨0, true, ht⟩
    · exact (cert.outer_union _).mpr ⟨0, false, hf⟩
  have hDa : a ∈ D := by
    apply (hD a).mpr
    refine ⟨?_, full_nonboundary T a hallT⟩
    have h0 : a ∈ T.cells := hallT 0
    rw [FootprintVertices, ite_eq_left ⟨a, h0⟩]
    exact ⟨a, h0, Or.inl rfl⟩
  have hnotP : a ∉ P := by
    intro hp
    obtain ⟨_, i, s, hf, hnb⟩ := (hP a).mp hp
    by_cases hi : i = 0
    · exact hnb ((hboundary i s).mpr hi)
    · obtain ⟨j, hj⟩ := raw_incident _ a
        (LatticeTileGridStructure _ (cert.parent_lattice i s)).1.1 hf
      exact other_absent i s hi j hj
  have hWa : a ∈ D \ P := Finset.mem_sdiff.mpr ⟨hDa, hnotP⟩
  have hcount : Nat.card {is : Fin 3 × Bool //
      a ∈ BoundaryFootprintVertices (cert.P is.1 is.2)} = 2 := by
    let e : {is : Fin 3 × Bool //
        a ∈ BoundaryFootprintVertices (cert.P is.1 is.2)} ≃ Bool :=
      { toFun := fun z => z.val.2
        invFun := fun s => ⟨(0, s), (hboundary 0 s).mpr rfl⟩
        left_inv := by
          intro z
          apply Subtype.ext
          apply Prod.ext
          · exact ((hboundary z.val.1 z.val.2).mp z.property).symm
          · rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e]
    simp
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact (hR x).mp hx ▸ hWa
  · intro x _
    exact (hfootO x).trans (hR x).symm
  · intro x hx
    obtain rfl := (hR x).mp hx
    exact ⟨hcount, hpoint⟩

end ApollonianSuperharmonic

end
