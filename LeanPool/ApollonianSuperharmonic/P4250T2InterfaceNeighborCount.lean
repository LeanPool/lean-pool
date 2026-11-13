/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AdjacentCellInterior

public import LeanPool.ApollonianSuperharmonic.LatticeFootprintIncidence

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.TileTranslationProperties

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralInteriorStarClassification

-- [TABLET NODE: P4250T2InterfaceNeighborCount]

/-!
# P4250T2InterfaceNeighborCount

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace InterfaceNeighborGeometry

private theorem incident_foot :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (z : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell z j ∈
            U.cells) → (z ∈ FootprintVertices U) ) := by
  classical
  intro U z j hj
  as_aux_lemma =>
  rw [FootprintVertices, ite_eq_left (show U.cells.Nonempty from ⟨_, hj⟩)]
  refine ⟨_, hj, ?_⟩
  fin_cases j <;> simp [LatticeVertexIncidentCell, Zsqrtd.ext_iff]

private theorem full_iff :
    (by
      classical
      exact
        (∀ (U : ProtoTile), ∀ (z : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell z j ∈
            U.cells) → (z ∈ FootprintVertices U)) → ((∀ (U : ProtoTile), (U.cells.Nonempty) → (∀
            (z : GaussianInt), (z ∈ FootprintVertices U) → (∃ j : Fin 4,
            LatticeVertexIncidentCell z j ∈ U.cells))) → (∀ (U : ProtoTile), ∀ (z : GaussianInt),
            (z ∈ FootprintVertices U ∧ z ∉ BoundaryFootprintVertices U) ↔ ∀ j : Fin 4,
            LatticeVertexIncidentCell z j ∈ U.cells)) ) := by
  classical
  intro incident_foot foot_incident U z
  as_aux_lemma =>
  constructor
  · rintro ⟨hf, hb⟩
    have hne : U.cells.Nonempty := by
      by_contra hn
      exact hb (by simpa [FootprintVertices, BoundaryFootprintVertices, hn] using hf)
    obtain ⟨j, hj⟩ := foot_incident U hne z hf
    intro l
    by_contra hl
    exact hb (P3161T2IncidentBoundary U z ⟨j, hj⟩ ⟨l, hl⟩)
  · intro hall
    refine ⟨incident_foot U z 0 (hall 0), ?_⟩
    have hne : U.cells.Nonempty := ⟨_, hall 0⟩
    intro hb
    rw [BoundaryFootprintVertices, ite_eq_left hne] at hb
    rcases hb with ⟨e, ⟨w, (⟨rfl, hw⟩ | ⟨rfl, hw⟩)⟩, hze⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hze
      rcases hze with rfl | rfl
      · rcases hw with hw | hw
        · exact hw.2 (by simpa [LatticeVertexIncidentCell] using hall 3)
        · exact hw.1 (by simpa [LatticeVertexIncidentCell] using hall 0)
      · rcases hw with hw | hw
        · exact hw.2 (by simpa [LatticeVertexIncidentCell, sub_sub] using hall 2)
        · exact hw.1 (by simpa [LatticeVertexIncidentCell] using hall 1)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hze
      rcases hze with rfl | rfl
      · rcases hw with hw | hw
        · exact hw.2 (by simpa [LatticeVertexIncidentCell] using hall 1)
        · exact hw.1 (by simpa [LatticeVertexIncidentCell] using hall 0)
      · rcases hw with hw | hw
        · exact hw.2 (by simpa [LatticeVertexIncidentCell, sub_eq_add_neg,
            add_assoc, add_comm, add_left_comm] using hall 2)
        · exact hw.1 (by simpa [LatticeVertexIncidentCell] using hall 3)

private theorem boundary_foot :
    (by
      classical
      exact
        (∀ (U : ProtoTile), ∀ (z : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell z j ∈
            U.cells) → (z ∈ FootprintVertices U)) → (∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈
            BoundaryFootprintVertices U) → (z ∈ FootprintVertices U)) ) := by
  classical
  intro incident_foot U z hz
  as_aux_lemma =>
  by_cases hne : U.cells.Nonempty
  · rw [BoundaryFootprintVertices, ite_eq_left hne] at hz
    rcases hz with ⟨e, ⟨w, (⟨rfl, hw⟩ | ⟨rfl, hw⟩)⟩, hze⟩
    all_goals simp only [Finset.mem_insert, Finset.mem_singleton] at hze
    · rcases hze with rfl | rfl <;> rcases hw with hw | hw
      · exact incident_foot U _ 0 hw.1
      · exact incident_foot U _ 3 (by simpa [LatticeVertexIncidentCell] using hw.2)
      · exact incident_foot U (w + 1) 1 (by simpa [LatticeVertexIncidentCell] using hw.1)
      · exact incident_foot U (w + 1) 2 (by simpa [LatticeVertexIncidentCell, sub_sub] using
          hw.2)
    · rcases hze with rfl | rfl <;> rcases hw with hw | hw
      · exact incident_foot U _ 0 hw.1
      · exact incident_foot U _ 1 (by simpa [LatticeVertexIncidentCell] using hw.2)
      · exact incident_foot U (w + ⟨0, 1⟩) 3 (by simpa [LatticeVertexIncidentCell] using hw.1)
      · exact incident_foot U (w + ⟨0, 1⟩) 2 (by simpa [LatticeVertexIncidentCell,
          sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hw.2)
  · simpa [FootprintVertices, BoundaryFootprintVertices, hne] using hz

private theorem edge_endpoint :
    (by
      classical
      exact
        (∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells) → ((z - ⟨0, 1⟩ ∈ U.cells) →
            (OpenLatticeEdge z (z + 1) ⊆ interior (TileRealization U)))) → ((∀ (U : ProtoTile), ∀
            (z : GaussianInt), (z ∈ U.cells) → ((z - 1 ∈ U.cells) → (OpenLatticeEdge z (z + ⟨0,
            1⟩) ⊆ interior (TileRealization U)))) → (∀ (U : ProtoTile), ∀ (z : GaussianInt), ∀ (j
            : Fin 4), (∀ a, ∀ b, FourNeighborAdjacent a b →
            a ∈ BoundaryFootprintVertices U → b ∈ BoundaryFootprintVertices U →
            ¬ OpenLatticeEdge a b ⊆ interior (TileRealization U)) → ((z ∈
                BoundaryFootprintVertices U) → ((LatticeVertexIncidentCell z j ∈ U.cells) →
                ((LatticeVertexIncidentCell z (j + 1) ∈ U.cells) → (![z + ⟨0, 1⟩, z - 1, z - ⟨0,
                1⟩, z + 1] j ∉ BoundaryFootprintVertices U)))))) ) := by
  classical
  intro horizontal_interior vertical_interior U z j hreg hz hj hj'
  as_aux_lemma =>
  intro hy
  fin_cases j
  all_goals simp only [LatticeVertexIncidentCell, Int.reduceNeg, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_one, Matrix.cons_val_zero, Fin.reduceAdd, Matrix.cons_val,
      Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, Fin.zero_eta, zero_add]
      at hj hj' hy
  · have he := vertical_interior U z hj hj'
    apply hreg z (z + ⟨0, 1⟩)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact hz
    · exact hy
    · exact he
  · have he := horizontal_interior U (z - 1) hj hj'
    exact hreg (z - 1) z (Or.inl (by simp)) hy hz (by simpa using he)
  · have he := vertical_interior U (z - ⟨0, 1⟩) hj'
      (by simpa [LatticeVertexIncidentCell, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc] using hj)
    exact hreg (z - ⟨0, 1⟩) z (Or.inr (Or.inr (Or.inl (by simp)))) hy hz
      (by simpa using he)
  · exact hreg z (z + 1) (Or.inl rfl) hz hy (horizontal_interior U z hj' hj)

private theorem hOA :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), cert.O.cells ⊆ (cert.P 0 true).cells
            ) := by
  classical
  intro C q cfg T cert c hc
  exact (cert.plus_union c).mpr ⟨0, false, by simpa [← cert.precursor_eq] using hc⟩

private theorem hOB :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), cert.O.cells ⊆ (cert.P 0 false).cells
            ) := by
  classical
  intro C q cfg T cert c hc
  exact (cert.minus_union c).mpr ⟨0, true, by simpa [← cert.precursor_cells] using hc⟩

private theorem hAB :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ((∀ (m : ℤ), ∀ (n : ℤ),
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v (⟨SixSubtileLabel.A, m, n⟩ :
            PeriodicSubtileIndex)).cells ∩ (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (⟨SixSubtileLabel.B, m, n⟩ : PeriodicSubtileIndex)).cells = (TileTranslation cert.O
            ((↑m : GaussianInt) * cert.u + (↑n : GaussianInt) * cert.v)).cells) ∧ ∀ (a :
            PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), a ≠ b → ¬((a.label =
            SixSubtileLabel.A ∧ b.label = SixSubtileLabel.B ∨ a.label = SixSubtileLabel.B ∧
            b.label = SixSubtileLabel.A) ∧ a.first = b.first ∧ a.second = b.second) → Disjoint
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v a).cells
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v b).cells) → ((cert.P 0
            true).cells ∩ (cert.P 0 false).cells = cert.O.cells) ) := by
  classical
  intro C q cfg T cert hsep
  have hzero : GaussianTranslation 0 = id := by funext z; simp [GaussianTranslation]
  simpa [SubtileOccurrenceInterpretation, TileTranslation, hzero] using hsep.1 0 0

private theorem parentLabel_injective :
    (by
      classical
      exact
        let parentLabel (a : Fin 3 × Bool) : SixSubtileLabel :=
          match a.1.val, a.2 with
          | 0, true => .A
          | 0, false => .B
          | 1, true => .C
          | 1, false => .D
          | 2, true => .E
          | _, _ => .F
        Function.Injective parentLabel ) := by
  classical
  intro parentLabel
  rintro ⟨i, s⟩ ⟨j, t⟩ hab
  fin_cases i <;> fin_cases j <;> cases s <;> cases t <;>
    simp [parentLabel] at hab ⊢

private theorem parentOccurrence :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T),
        let parentLabel (a : Fin 3 × Bool) : SixSubtileLabel :=
          match a.1.val, a.2 with
          | 0, true => .A
          | 0, false => .B
          | 1, true => .C
          | 1, false => .D
          | 2, true => .E
          | _, _ => .F
        let parentIndex (a : Fin 3 × Bool) : PeriodicSubtileIndex := ⟨parentLabel a, 0, 0⟩
        ∀ (a : Fin 3 × Bool), SubtileOccurrenceInterpretation cert.P cert.u cert.v (parentIndex
            a) = TileTranslation (cert.P a.1 a.2) 0 ) := by
  classical
  intro C q cfg T cert parentLabel parentIndex a
  rcases a with ⟨i, s⟩
  fin_cases i <;> cases s <;>
    simp [parentIndex, parentLabel, SubtileOccurrenceInterpretation]

private theorem parent_disjoint :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ((∀ (m : ℤ), ∀ (n : ℤ),
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v (⟨SixSubtileLabel.A, m, n⟩ :
            PeriodicSubtileIndex)).cells ∩ (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (⟨SixSubtileLabel.B, m, n⟩ : PeriodicSubtileIndex)).cells = (TileTranslation cert.O
            ((↑m : GaussianInt) * cert.u + (↑n : GaussianInt) * cert.v)).cells) ∧ ∀ (a :
            PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), a ≠ b → ¬((a.label =
            SixSubtileLabel.A ∧ b.label = SixSubtileLabel.B ∨ a.label = SixSubtileLabel.B ∧
            b.label = SixSubtileLabel.A) ∧ a.first = b.first ∧ a.second = b.second) → Disjoint
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v a).cells
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v b).cells) → (
        let parentLabel (a : Fin 3 × Bool) : SixSubtileLabel :=
          match a.1.val, a.2 with
          | 0, true => .A
          | 0, false => .B
          | 1, true => .C
          | 1, false => .D
          | 2, true => .E
          | _, _ => .F
        (Function.Injective parentLabel) → (
        let parentIndex (a : Fin 3 × Bool) : PeriodicSubtileIndex := ⟨parentLabel a, 0, 0⟩
        (∀ (a : Fin 3 × Bool), SubtileOccurrenceInterpretation cert.P cert.u cert.v (parentIndex
            a) = TileTranslation (cert.P a.1 a.2) 0) → (∀ (a : Fin 3 × Bool), ∀ (b : Fin 3 ×
            Bool), (a ≠ b) → ((¬ (a = (0, true) ∧ b = (0, false) ∨
            a = (0, false) ∧ b = (0, true))) → (Disjoint (cert.P a.1 a.2).cells (cert.P b.1
                b.2).cells))))) ) := by
  classical
  intro C q cfg T cert hsep parentLabel parentLabel_injective parentIndex parentOccurrence a b
      hab hnotAB
  as_aux_lemma =>
  have hidx : parentIndex a ≠ parentIndex b := by
    intro he
    exact hab (parentLabel_injective (congrArg PeriodicSubtileIndex.label he))
  have hd := hsep.2 (parentIndex a) (parentIndex b) hidx ?_
  · rw [parentOccurrence a, parentOccurrence b] at hd
    have hzero : GaussianTranslation 0 = id := by funext z; simp [GaussianTranslation]
    simpa [TileTranslation, hzero] using hd
  · intro hp
    apply hnotAB
    rcases hp.1 with hp | hp
    · left
      constructor
      · apply parentLabel_injective
        exact hp.1
      · apply parentLabel_injective
        exact hp.2
    · right
      constructor
      · apply parentLabel_injective
        exact hp.1
      · apply parentLabel_injective
        exact hp.2

private theorem parent_unique :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ((cert.P 0 true).cells ∩ (cert.P 0
            false).cells = cert.O.cells) → ((∀ (a : Fin 3 × Bool), ∀ (b : Fin 3 × Bool), (a ≠ b)
            → ((¬ (a = (0, true) ∧ b = (0, false) ∨ a = (0, false) ∧ b = (0, true))) → (Disjoint
            (cert.P a.1 a.2).cells (cert.P b.1 b.2).cells))) → (∀ (c : LatticeCell), (c ∉
            cert.O.cells) → (∀ (a : Fin 3 × Bool), ∀ (b : Fin 3 × Bool), (c ∈ (cert.P a.1
            a.2).cells) → ((c ∈ (cert.P b.1 b.2).cells) → (a = b))))) ) := by
  classical
  intro C q cfg T cert hAB parent_disjoint c hc a b ha hb
  by_contra hab
  by_cases hpair : a = (0, true) ∧ b = (0, false) ∨
      a = (0, false) ∧ b = (0, true)
  · apply hc
    rw [← hAB]
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Finset.mem_inter.mpr ⟨ha, hb⟩
    · exact Finset.mem_inter.mpr ⟨hb, ha⟩
  · exact Finset.disjoint_left.mp (parent_disjoint a b hab hpair) ha hb

private theorem hchildPos :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (∀ (i :
            Fin 3), 0 < (q i.succ).1) ) := by
  classical
  intro q cfg i
  have := (ProperBandCurvatureStructure q cfg.proper).2.1 i
  have := cfg.noLine i.succ
  omega

private theorem prototile_disk :
    (by
      classical
      exact
        ∀ (c : CircleCoordinates), (∃ r : Fin 4 → CircleCoordinates,
            SemiProperQuadruple r ∧ ∃ i, r i = c) → (∀ (U : ProtoTile), (BandPrototile c U) → ((0
                < c.1 ∨ U.cells.Nonempty) → (LatticeTile U))) ) := by
  classical
  intro c hcircle U hU hvalid
  as_aux_lemma =>
  cases hU with
  | line w z hw =>
    rcases hvalid with h | h <;> simp at h
  | unit z a anchor =>
    let E : BandCircle :=
      ⟨⟨(1, 1 + 2 * z), Or.inl (by norm_num), hcircle⟩, by norm_num⟩
    obtain ⟨V, hV, harea, _⟩ := CurvatureOneTileBase E rfl
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp harea
    let V' := TileTranslation V (a - b)
    have hV' : LatticeTile V' := (TileDiskAreaCovariance V (a - b)).1.mp hV
    have hcells' : V'.cells = {a} := by
      simp [V', TileTranslation, hb, GaussianTranslation]
    unfold LatticeTile TileRealization at hV' ⊢
    rw [hcells'] at hV'
    exact hV'
  | @decompose r hr S U hS hcells hfoot hcent =>
    exact (BandTileSimultaneousInduction r hr U
      (.decompose hr hS hcells hfoot hcent)).1

private theorem retained_pos :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), (∀
            (i : Fin 3), 0 < (q i.succ).1) → (∀ (i : Fin 3), (i = 1 ∨ i = 2) → (0 <
            (cfg.firstPredecessor i.succ).1)) ) := by
  classical
  intro q cfg hchildPos i hi
  rcases hi with rfl | rfl
  · simpa [cfg.firstParentTwo] using hchildPos 1
  · simpa [cfg.firstParentThree] using hchildPos 2

private theorem no_parent_interior :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (D : Finset GaussianInt), ∀ (P :
            Finset GaussianInt), (∀ (x : GaussianInt), x ∈ P ↔ x ∈ D ∧ ∃ (i : Fin (3 : ℕ)) (s :
            Bool), x ∈ FootprintVertices (cert.P i s) ∧ x ∉ BoundaryFootprintVertices (cert.P i
            s)) → (∀ (x : GaussianInt), (x ∈ D) → ((x ∉ P) → (∀ (i : Fin 3), ∀ (s : Bool), (x ∈
            FootprintVertices (cert.P i s)) → (x ∈ BoundaryFootprintVertices (cert.P i s))))) )
            := by
  classical
  intro C q cfg T cert D P hP x hxD hxP i s hf
  by_contra hb
  exact hxP ((hP x).mpr ⟨hxD, i, s, hf, hb⟩)

private theorem no_diagonal :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ {α : Type}, ∀ (F : α → ProtoTile), (∀ a, LatticeTile (F a)) → (∀
            (owner : Fin 4 → α), (∀ j, ∀ a, LatticeVertexIncidentCell x j ∈ (F a).cells ↔ owner j
            = a) → (¬ (owner 0 = owner 2 ∧ owner 1 ≠ owner 0 ∧ owner 3 ≠ owner 0) ∧ ¬ (owner 1 =
            owner 3 ∧ owner 0 ≠ owner 1 ∧ owner 2 ≠ owner 1))) ) := by
  classical
  intro x α F hF owner hown
  as_aux_lemma =>
  constructor
  · rintro ⟨h02, h1, h3⟩
    have hcheck := (LatticeTileGridStructure (F (owner 0)) (hF (owner 0))).2.1 x
    apply hcheck
    left
    have h0 := (hown 0 (owner 0)).mpr rfl
    have h2 := (hown 2 (owner 0)).mpr h02.symm
    have hn1 : LatticeVertexIncidentCell x 1 ∉ (F (owner 0)).cells :=
      fun h => h1 ((hown 1 (owner 0)).mp h)
    have hn3 : LatticeVertexIncidentCell x 3 ∉ (F (owner 0)).cells :=
      fun h => h3 ((hown 3 (owner 0)).mp h)
    simpa [LatticeVertexIncidentCell] using And.intro h0 ⟨h2, hn1, hn3⟩
  · rintro ⟨h13, h0, h2⟩
    have hcheck := (LatticeTileGridStructure (F (owner 1)) (hF (owner 1))).2.1 x
    apply hcheck
    right
    have h1 := (hown 1 (owner 1)).mpr rfl
    have h3 := (hown 3 (owner 1)).mpr h13.symm
    have hn0 : LatticeVertexIncidentCell x 0 ∉ (F (owner 1)).cells :=
      fun h => h0 ((hown 0 (owner 1)).mp h)
    have hn2 : LatticeVertexIncidentCell x 2 ∉ (F (owner 1)).cells :=
      fun h => h2 ((hown 2 (owner 1)).mp h)
    simpa [LatticeVertexIncidentCell] using And.intro h1 ⟨h3, hn0, hn2⟩

private theorem label_sectors :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ {α : Type}, ∀ (F : α → ProtoTile), (∀ a, ∀ b, a ≠ b → Disjoint (F
            a).cells (F b).cells) → ((∀ j : Fin 4, ∃ a, LatticeVertexIncidentCell x j ∈ (F
            a).cells) → (∃ owner : Fin 4 → α, ∀ j, ∀ a, LatticeVertexIncidentCell x j ∈ (F
            a).cells ↔ owner j = a)) ) := by
  classical
  intro x α F hd hcover
  as_aux_lemma =>
  let owner (j : Fin 4) := Classical.choose (hcover j)
  have hs (j) : LatticeVertexIncidentCell x j ∈ (F (owner j)).cells :=
    Classical.choose_spec (hcover j)
  refine ⟨owner, fun j a => ⟨?_, ?_⟩⟩
  · intro ha
    by_contra hn
    exact Finset.disjoint_left.mp (hd (owner j) a hn) (hs j) ha
  · rintro rfl
    exact hs j

private theorem common_parent_iff :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (∀ (a : Fin 3 × Bool), ∀ (b : Fin 3 ×
            Bool), (a ≠ b) → ((¬ (a = (0, true) ∧ b = (0, false) ∨ a = (0, false) ∧ b = (0,
            true))) → (Disjoint (cert.P a.1 a.2).cells (cert.P b.1 b.2).cells))) → (∀ (x :
            GaussianInt), (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ∨
            LatticeVertexIncidentCell x j ∈ (cert.P 0 false).cells) → (∀ (j : Fin 4), (∃ i s,
                LatticeVertexIncidentCell x j ∈ (cert.P i s).cells ∧ LatticeVertexIncidentCell x
                (j + 1) ∈ (cert.P i s).cells) ↔ (LatticeVertexIncidentCell x j ∈ (cert.P 0
                true).cells ∧ LatticeVertexIncidentCell x (j + 1) ∈ (cert.P 0 true).cells) ∨
                (LatticeVertexIncidentCell x j ∈ (cert.P 0 false).cells ∧
                LatticeVertexIncidentCell x (j + 1) ∈ (cert.P 0 false).cells))) ) := by
  classical
  intro C q cfg T cert parent_disjoint x hcover j
  as_aux_lemma =>
  constructor
  · rintro ⟨i, s, hj, hj'⟩
    by_cases ha : (i, s) = ((0 : Fin 3), true)
    · cases ha
      exact Or.inl ⟨hj, hj'⟩
    by_cases hb : (i, s) = ((0 : Fin 3), false)
    · cases hb
      exact Or.inr ⟨hj, hj'⟩
    have hd (b : Fin 3 × Bool) (hba : b = (0, true) ∨ b = (0, false)) :
        Disjoint (cert.P i s).cells (cert.P b.1 b.2).cells := by
      apply parent_disjoint (i, s) b
      · rcases hba with rfl | rfl <;> assumption
      · rintro (⟨h, _⟩ | ⟨h, _⟩)
        · exact ha h
        · exact hb h
    rcases hcover j with h | h
    · exact (Finset.disjoint_left.mp (hd (0, true) (Or.inl rfl)) hj h).elim
    · exact (Finset.disjoint_left.mp (hd (0, false) (Or.inr rfl)) hj h).elim
  · rintro (h | h)
    · exact ⟨0, true, h⟩
    · exact ⟨0, false, h⟩

private theorem shared_cells :
    (by
      classical
      exact
        ∀ (x : GaussianInt),
        let neighbor : Fin 4 → GaussianInt := ![x + ⟨0, 1⟩, x - 1, x - ⟨0, 1⟩, x + 1]
        ∀ (j : Fin 4), ∃ a b : Fin 4, LatticeVertexIncidentCell x j = LatticeVertexIncidentCell
            (neighbor j) a ∧ LatticeVertexIncidentCell x (j + 1) = LatticeVertexIncidentCell
            (neighbor j) b ) := by
  classical
  intro x neighbor j
  fin_cases j
  · exact ⟨3, 2, by simp [neighbor, LatticeVertexIncidentCell], by
      simp [neighbor, LatticeVertexIncidentCell, sub_eq_add_neg, add_comm, add_left_comm,
          add_assoc]⟩
  · exact ⟨0, 3, by simp [neighbor, LatticeVertexIncidentCell], by simp [neighbor,
      LatticeVertexIncidentCell]⟩
  · exact ⟨1, 0, by simp [neighbor, LatticeVertexIncidentCell, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc], by simp [neighbor, LatticeVertexIncidentCell]⟩
  · exact ⟨2, 1, by simp [neighbor, LatticeVertexIncidentCell], by simp [neighbor,
      LatticeVertexIncidentCell]⟩

private theorem neighbor_bridge :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (D : Finset GaussianInt), ∀ (P :
            Finset GaussianInt), (∀ (x : GaussianInt), x ∈ D ↔ x ∈ FootprintVertices T ∧ x ∉
            BoundaryFootprintVertices T) → ((∀ (x : GaussianInt), x ∈ P ↔ x ∈ D ∧ ∃ (i : Fin (3 :
            ℕ)) (s : Bool), x ∈ FootprintVertices (cert.P i s) ∧ x ∉ BoundaryFootprintVertices
            (cert.P i s)) → ((∀ (U : ProtoTile), ∀ (z : GaussianInt), ∀ (j : Fin 4),
            (LatticeVertexIncidentCell z j ∈ U.cells) → (z ∈ FootprintVertices U)) → ((∀ (U :
            ProtoTile), ∀ (z : GaussianInt), (z ∈ FootprintVertices U ∧ z ∉
            BoundaryFootprintVertices U) ↔ ∀ j : Fin 4, LatticeVertexIncidentCell z j ∈ U.cells)
            → ((∀ (U : ProtoTile), ∀ (z : GaussianInt), ∀ (j : Fin 4), (∀ a, ∀ b,
            FourNeighborAdjacent a b → a ∈ BoundaryFootprintVertices U → b ∈
            BoundaryFootprintVertices U → ¬ OpenLatticeEdge a b ⊆ interior (TileRealization U)) →
            ((z ∈ BoundaryFootprintVertices U) → ((LatticeVertexIncidentCell z j ∈ U.cells) →
            ((LatticeVertexIncidentCell z (j + 1) ∈ U.cells) → (![z + ⟨0, 1⟩, z - 1, z - ⟨0, 1⟩,
            z + 1] j ∉ BoundaryFootprintVertices U))))) → ((∀ (i : Fin 3), ∀ (s : Bool), ∀ a, ∀
            b, FourNeighborAdjacent a b → a ∈ BoundaryFootprintVertices (cert.P i s) → b ∈
            BoundaryFootprintVertices (cert.P i s) → ¬ OpenLatticeEdge a b ⊆ interior
            (TileRealization (cert.P i s))) → (∀ (x : GaussianInt), (∀ (i : Fin 3), ∀ (s : Bool),
            (x ∈ FootprintVertices (cert.P i s)) → (x ∈ BoundaryFootprintVertices (cert.P i s))) → (
        let neighbor : Fin 4 → GaussianInt := ![x + ⟨0, 1⟩, x - 1, x - ⟨0, 1⟩, x + 1]
        (∀ (j : Fin 4), ∃ a b : Fin 4, LatticeVertexIncidentCell x j = LatticeVertexIncidentCell
            (neighbor j) a ∧ LatticeVertexIncidentCell x (j + 1) = LatticeVertexIncidentCell
            (neighbor j) b) → (∀ (j : Fin 4), neighbor j ∈ P ↔ ∃ i s, LatticeVertexIncidentCell x
            j ∈ (cert.P i s).cells ∧ LatticeVertexIncidentCell x (j + 1) ∈ (cert.P i
            s).cells)))))))) ) := by
  classical
  intro C q cfg T cert D P hD hP incident_foot full_iff edge_endpoint parent_regular x
      no_parent_interior neighbor shared_cells j
  as_aux_lemma =>
  obtain ⟨a, b, ha, hb⟩ := shared_cells j
  constructor
  · intro hp
    obtain ⟨_, i, s, hf, hn⟩ := (hP _).mp hp
    have hall := (full_iff (cert.P i s) (neighbor j)).mp ⟨hf, hn⟩
    exact ⟨i, s, by rw [ha]; exact hall a, by rw [hb]; exact hall b⟩
  · rintro ⟨i, s, hj, hj'⟩
    have hxf := incident_foot _ x j hj
    have hyf := incident_foot (cert.P i s) (neighbor j) a (by rw [← ha]; exact hj)
    have hxb := no_parent_interior i s hxf
    have hyn : neighbor j ∉ BoundaryFootprintVertices (cert.P i s) :=
      edge_endpoint (cert.P i s) x j (parent_regular i s) hxb hj hj'
    have hyfull := (full_iff (cert.P i s) (neighbor j)).mp ⟨hyf, hyn⟩
    have hyT := (full_iff T (neighbor j)).mpr (fun l =>
      (cert.outer_union _).mpr ⟨i, s, hyfull l⟩)
    exact (hP _).mpr ⟨(hD _).mpr hyT, i, s, hyf, hyn⟩

private theorem neighbor_injective :
    (by
      classical
      exact
        ∀ (x : GaussianInt),
        let neighbor : Fin 4 → GaussianInt := ![x + ⟨0, 1⟩, x - 1, x - ⟨0, 1⟩, x + 1]
        Function.Injective neighbor ) := by
  classical
  intro x neighbor a b hab
  fin_cases a <;> fin_cases b <;> simp [neighbor, Zsqrtd.ext_iff] at hab ⊢ <;> omega

private theorem neighbor_count :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (P : Finset GaussianInt), ∀ (x :
            GaussianInt),
        let neighbor : Fin 4 → GaussianInt := ![x + ⟨0, 1⟩, x - 1, x - ⟨0, 1⟩, x + 1]
        (∀ (j : Fin 4), neighbor j ∈ P ↔ ∃ i s, LatticeVertexIncidentCell x j ∈ (cert.P i
            s).cells ∧ LatticeVertexIncidentCell x (j + 1) ∈ (cert.P i s).cells) →
            ((Function.Injective neighbor) → ((∀ (j : Fin 4), FourNeighborAdjacent (neighbor j)
            x) → ((∀ (y : GaussianInt), (FourNeighborAdjacent y x) → (∃ j : Fin 4, neighbor j =
            y)) → ((P.filter fun y => @decide (FourNeighborAdjacent y x) (Classical.propDecidable
            _)).card = (Finset.univ.filter fun j : Fin 4 => ∃ i s, LatticeVertexIncidentCell x j
            ∈ (cert.P i s).cells ∧ LatticeVertexIncidentCell x (j + 1) ∈ (cert.P i
            s).cells).card)))) ) := by
  classical
  intro C q cfg T cert P x neighbor neighbor_bridge neighbor_injective neighbor_adjacent
      neighbor_exhaust
  symm
  apply Finset.card_bij (fun j _ => neighbor j)
  · intro j hj
    exact Finset.mem_filter.mpr ⟨(neighbor_bridge j).mpr (Finset.mem_filter.mp hj).2,
      by simpa using neighbor_adjacent j⟩
  · intro j hj l hl he
    exact neighbor_injective he
  · intro y hy
    obtain ⟨j, rfl⟩ := neighbor_exhaust y (by simpa using (Finset.mem_filter.mp hy).2)
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (neighbor_bridge j).mp (Finset.mem_filter.mp hy).1⟩, rfl⟩

private theorem hnoO :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (D : Finset GaussianInt), ∀ (P :
            Finset GaussianInt), (∀ x ∈ D \ P, x ∈ FootprintVertices cert.O ↔ x ∈
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) → ((∀
                (U : ProtoTile), ∀ (z :
            GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell z j ∈ U.cells) → (z ∈
            FootprintVertices U)) → (∀ (x : GaussianInt), (x ∈ D \ P) → ((x ∉
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) → (∀
                (j : Fin 4),
            LatticeVertexIncidentCell x j ∉ cert.O.cells)))) ) := by
  classical
  intro C q cfg T cert D P hprecursor incident_foot x hx hnotR j hj
  exact hnotR ((hprecursor x hx).mp (incident_foot cert.O x j hj))

private theorem owner_exists :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (x : GaussianInt), (∀ (j : Fin (4 :
            ℕ)), LatticeVertexIncidentCell x j ∈ T.cells) → (∀ (j : Fin 4), ∃ a : Fin 3 × Bool,
            LatticeVertexIncidentCell x j ∈ (cert.P a.1 a.2).cells) ) := by
  classical
  intro C q cfg T cert x hcells j
  obtain ⟨i, s, h⟩ := (cert.outer_union _).mp (hcells j)
  exact ⟨(i, s), h⟩

private theorem owner_iff :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (∀ (c : LatticeCell), (c ∉
            cert.O.cells) → (∀ (a : Fin 3 × Bool), ∀ (b : Fin 3 × Bool), (c ∈ (cert.P a.1
            a.2).cells) → ((c ∈ (cert.P b.1 b.2).cells) → (a = b)))) → (∀ (x : GaussianInt), (∀
            (j : Fin 4), LatticeVertexIncidentCell x j ∉ cert.O.cells) → (∀ (owner_exists : ∀ (j
            : Fin 4), ∃ a : Fin 3 × Bool, LatticeVertexIncidentCell x j ∈ (cert.P a.1 a.2).cells),
        let owner (j : Fin 4) : Fin 3 × Bool := Classical.choose (owner_exists j)
        (∀ (j : Fin 4), LatticeVertexIncidentCell x j ∈ (cert.P (owner j).1 (owner j).2).cells) →
            (∀ (j : Fin 4), ∀ (a : Fin 3 × Bool), LatticeVertexIncidentCell x j ∈ (cert.P a.1
            a.2).cells ↔ owner j = a))) ) := by
  classical
  intro C q cfg T cert parent_unique x hnoO owner_exists owner owner_spec j a
  constructor
  · intro ha
    exact parent_unique _ (hnoO j) _ _ (owner_spec j) ha
  · rintro rfl
    exact owner_spec j

private theorem hboundary :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (∀ (U : ProtoTile), ∀ (z :
            GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell z j ∈ U.cells) → (z ∈
            FootprintVertices U)) → ((∀ (U : ProtoTile), (U.cells.Nonempty) → (∀ (z :
            GaussianInt), (z ∈ FootprintVertices U) → (∃ j : Fin 4, LatticeVertexIncidentCell z j
            ∈ U.cells))) → ((∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈
            BoundaryFootprintVertices U) → (z ∈ FootprintVertices U)) → (∀ (x : GaussianInt), (∀
            (i : Fin 3), ∀ (s : Bool), (x ∈ FootprintVertices (cert.P i s)) → (x ∈
            BoundaryFootprintVertices (cert.P i s))) → (∀ (owner_exists : ∀ (j : Fin 4), ∃ a :
            Fin 3 × Bool, LatticeVertexIncidentCell x j ∈ (cert.P a.1 a.2).cells),
        let owner (j : Fin 4) : Fin 3 × Bool := Classical.choose (owner_exists j)
        (∀ (j : Fin 4), LatticeVertexIncidentCell x j ∈ (cert.P (owner j).1 (owner j).2).cells) →
            ((∀ (j : Fin 4), ∀ (a : Fin 3 × Bool), LatticeVertexIncidentCell x j ∈ (cert.P a.1
            a.2).cells ↔ owner j = a) → (∀ (a : Fin 3 × Bool), x ∈ BoundaryFootprintVertices
            (cert.P a.1 a.2) ↔ a ∈ Finset.univ.image owner)))))) ) := by
  classical
  intro C q cfg T cert incident_foot foot_incident boundary_foot x no_parent_interior
      owner_exists owner owner_spec owner_iff a
  constructor
  · intro hb
    obtain ⟨j, hj⟩ := foot_incident _
      (LatticeTileGridStructure _ (cert.parent_lattice a.1 a.2)).1.1 x
      (boundary_foot _ x hb)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, (owner_iff j a).mp hj⟩
  · intro ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    exact no_parent_interior _ _ (incident_foot _ x j (owner_spec j))

private theorem hcard :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (x : GaussianInt), ∀ (owner_exists
            : ∀ (j : Fin 4), ∃ a : Fin 3 × Bool, LatticeVertexIncidentCell x j ∈ (cert.P a.1
            a.2).cells),
        let owner (j : Fin 4) : Fin 3 × Bool := Classical.choose (owner_exists j)
        (∀ (a : Fin 3 × Bool), x ∈ BoundaryFootprintVertices (cert.P a.1 a.2) ↔ a ∈
            Finset.univ.image owner) → (Nat.card
            {a : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)} =
            (Finset.univ.image owner).card) ) := by
  classical
  intro C q cfg T cert x owner_exists owner hboundary
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext a
  simp [hboundary a]

private theorem hnot_constant :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (D : Finset GaussianInt), ∀ (P :
            Finset GaussianInt), (∀ (x : GaussianInt), x ∈ P ↔ x ∈ D ∧ ∃ (i : Fin (3 : ℕ)) (s :
            Bool), x ∈ FootprintVertices (cert.P i s) ∧ x ∉ BoundaryFootprintVertices (cert.P i
            s)) → ((∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ FootprintVertices U ∧ z ∉
            BoundaryFootprintVertices U) ↔ ∀ j : Fin 4, LatticeVertexIncidentCell z j ∈ U.cells)
            → (∀ (x : GaussianInt), (x ∈ D) → ((x ∉ P) → (∀ (owner_exists : ∀ (j : Fin 4), ∃ a :
            Fin 3 × Bool, LatticeVertexIncidentCell x j ∈ (cert.P a.1 a.2).cells),
        let owner (j : Fin 4) : Fin 3 × Bool := Classical.choose (owner_exists j)
        (∀ (j : Fin 4), ∀ (a : Fin 3 × Bool), LatticeVertexIncidentCell x j ∈ (cert.P a.1
            a.2).cells ↔ owner j = a) → (∃ j, owner j ≠ owner 0))))) ) := by
  classical
  intro C q cfg T cert D P hP full_iff x hxD hxP owner_exists owner owner_iff
  by_contra hn
  have hall : ∀ j, owner j = owner 0 := by simpa using hn
  have hfull := (full_iff (cert.P (owner 0).1 (owner 0).2) x).mpr
    (fun j => (owner_iff j (owner 0)).mpr (hall j))
  exact hxP ((hP x).mpr ⟨hxD, (owner 0).1, (owner 0).2, hfull⟩)

private theorem finite_countAt614 :
    (by
      classical
      exact
        ∀ owner : Fin 4 → Fin 3 × Bool, (¬ (owner 0 = owner 2 ∧ owner 1 ≠ owner 0 ∧ owner 3 ≠
            owner 0) ∧ ¬ (owner 1 = owner 3 ∧ owner 0 ≠ owner 1 ∧ owner 2 ≠ owner 1)) → (∃ j,
            owner j ≠ owner 0) → (Finset.univ.filter (fun j : Fin 4 => owner j = owner (j +
            1))).card + (Finset.univ.image owner).card = 4 ) := by
  classical
  decide +kernel

private theorem hncount :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (P : Finset GaussianInt), ∀ (x :
            GaussianInt), ((P.filter fun y => @decide (FourNeighborAdjacent y x)
            (Classical.propDecidable _)).card = (Finset.univ.filter fun j : Fin 4 => ∃ i s,
            LatticeVertexIncidentCell x j ∈ (cert.P i s).cells ∧ LatticeVertexIncidentCell x (j +
            1) ∈ (cert.P i s).cells).card) → (∀ (owner_exists : ∀ (j : Fin 4), ∃ a : Fin 3 ×
            Bool, LatticeVertexIncidentCell x j ∈ (cert.P a.1 a.2).cells),
        let owner (j : Fin 4) : Fin 3 × Bool := Classical.choose (owner_exists j)
        (∀ (j : Fin 4), LatticeVertexIncidentCell x j ∈ (cert.P (owner j).1 (owner j).2).cells) →
            ((∀ (j : Fin 4), ∀ (a : Fin 3 × Bool), LatticeVertexIncidentCell x j ∈ (cert.P a.1
            a.2).cells ↔ owner j = a) → ((P.filter fun y => @decide (FourNeighborAdjacent y x)
            (Classical.propDecidable _)).card = (Finset.univ.filter (fun j : Fin 4 => owner j =
            owner (j + 1))).card))) ) := by
  classical
  intro C q cfg T cert P x neighbor_count owner_exists owner owner_spec owner_iff
  rw [neighbor_count]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, s, hj, hj'⟩
    exact ((owner_iff j (i, s)).mp hj).trans ((owner_iff (j + 1) (i, s)).mp hj').symm
  · intro he
    exact ⟨(owner j).1, (owner j).2, owner_spec j,
      (owner_iff (j + 1) (owner j)).mpr he.symm⟩

private theorem hlow :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (x : GaussianInt), ∀ (owner_exists
            : ∀ (j : Fin 4), ∃ a : Fin 3 × Bool, LatticeVertexIncidentCell x j ∈ (cert.P a.1
            a.2).cells),
        let owner (j : Fin 4) : Fin 3 × Bool := Classical.choose (owner_exists j)
        (∃ j, owner j ≠ owner 0) → (2 ≤ (Finset.univ.image owner).card) ) := by
  classical
  intro C q cfg T cert x owner_exists owner hnot_constant
  obtain ⟨j, hj⟩ := hnot_constant
  have hsub : ({owner 0, owner j} : Finset (Fin 3 × Bool)) ⊆ Finset.univ.image owner := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have := Finset.card_le_card hsub
  simpa [Finset.card_pair hj.symm] using this

private theorem hk23 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (P : Finset GaussianInt), ∀ (x :
            GaussianInt), ((P.filter fun y => @decide (FourNeighborAdjacent y x)
            (Classical.propDecidable _)).card = (Finset.univ.filter fun j : Fin 4 => ∃ i s,
            LatticeVertexIncidentCell x j ∈ (cert.P i s).cells ∧ LatticeVertexIncidentCell x (j +
            1) ∈ (cert.P i s).cells).card) → (∀ (owner_exists : ∀ (j : Fin 4), ∃ a : Fin 3 ×
            Bool, LatticeVertexIncidentCell x j ∈ (cert.P a.1 a.2).cells),
        let owner (j : Fin 4) : Fin 3 × Bool := Classical.choose (owner_exists j)
        (Nat.card {a : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)} =
            (Finset.univ.image owner).card) → (((P.filter fun y => @decide (FourNeighborAdjacent
            y x) (Classical.propDecidable _)).card = (Finset.univ.filter (fun j : Fin 4 => owner
            j = owner (j + 1))).card) → ((
        let k := Nat.card
            { is : Fin (3 : ℕ) × Bool // x ∈ BoundaryFootprintVertices (cert.P is.1 is.2) }; (k =
            (2 : ℕ) → GaussianRealPoint x ≠ TileCentroid T → BandOrderedGeneralInteriorWebRow
            cert x false) ∧ (k = (3 : ℕ) → BandOrderedGeneralInteriorWebRow cert x true ∧
            GaussianRealPoint x ≠ TileCentroid T) ∧ k ≠ (4 : ℕ) ∧ (k = (2 : ℕ) →
            GaussianRealPoint x = TileCentroid T → (cfg.firstPredecessor (1 : Fin (4 : ℕ))).1 =
            (0 : ℤ))) → (((Finset.univ.filter fun j : Fin 4 => owner j = owner (j + 1)).card +
            (Finset.image owner Finset.univ).card = (4 : ℕ)) → ((2 ≤ (Finset.univ.image
            owner).card) → (Nat.card
            {a : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)} = 2 ∨ Nat.card
            {a : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)} = 3)))))) ) := by
  classical
  intro C q cfg T cert P x neighbor_count owner_exists owner hcard hncount hclass hsum hlow
  have hk4 := hclass.2.2.1
  omega

private abbrev hzeroAt680 := ApollonianSuperharmonic.TileTranslationProperties.zero

private theorem hcoverAt684 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (D : Finset GaussianInt), ∀ (P :
            Finset GaussianInt), (∀ x ∈ D \ P, x ∈ FootprintVertices cert.O ↔ x ∈
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) → ((∀
                (U : ProtoTile), ∀ (z :
            GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell z j ∈ U.cells) → (z ∈
            FootprintVertices U)) → (∀ (x : GaussianInt), (x ∈ D \ P) → ((x ∈
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) → ((∀
                (U : ProtoTile),
            TileTranslation U 0 = U) → (∀ (j : Fin 4), LatticeVertexIncidentCell x j ∈ (cert.P 0
            true).cells ∨ LatticeVertexIncidentCell x j ∈ (cert.P 0 false).cells))))) ) := by
  classical
  intro C q cfg T cert D P hprecursor incident_foot x hx hxR hzero j
  have hxO := (hprecursor x hx).mpr hxR
  have hc := cert.precursor_isolated 0 0 x (by simpa [hzero] using hxO)
    (LatticeVertexIncidentCell x j)
    (incident_foot (⟨{LatticeVertexIncidentCell x j}, LatticeVertexIncidentCell x j⟩ :
        ProtoTile)
      x j (by simp))
  simpa [SubtileOccurrenceInterpretation, hzero] using hc

private theorem hFdAt697 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ((cert.P 0 true).cells ∩ (cert.P 0
            false).cells = cert.O.cells) → ((cert.O.cells = ∅) → (
        let F : Fin 2 → ProtoTile := ![cert.P 0 true, cert.P 0 false]
        ∀ (a : Fin 2), ∀ (b : Fin 2), (a ≠ b) → (Disjoint (F a).cells (F b).cells))) ) := by
  classical
  intro C q cfg T cert hAB hempty F a b hne
  have hd : Disjoint (cert.P 0 true).cells (cert.P 0 false).cells := by
    rw [Finset.disjoint_iff_inter_eq_empty, hAB, hempty]
  fin_cases a <;> fin_cases b
  · exact (hne rfl).elim
  · exact hd
  · exact hd.symm
  · exact (hne rfl).elim

private theorem hsurjAt709 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (x : GaussianInt), ∀ (jA : Fin (4 :
            ℕ)), ∀ (jB : Fin (4 : ℕ)), (LatticeVertexIncidentCell x jA ∈ (cert.P 0 true).cells) →
            ((LatticeVertexIncidentCell x jB ∈ (cert.P 0 false).cells) → (
        let F : Fin 2 → ProtoTile := ![cert.P 0 true, cert.P 0 false]
        ∀ (owner : Fin (4 : ℕ) → Fin (2 : ℕ)), (∀ (j : Fin (4 : ℕ)), ∀ (a : Fin (2 : ℕ)),
            LatticeVertexIncidentCell x j ∈ (F a).cells ↔ owner j = a) → (Function.Surjective
            owner))) ) := by
  classical
  intro C q cfg T cert x jA jB hA hB F owner hown a
  fin_cases a
  · exact ⟨jA, (hown jA 0).mp hA⟩
  · exact ⟨jB, (hown jB 1).mp hB⟩

private theorem hcommonAt714 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (x : GaussianInt), ((∀ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ∨ LatticeVertexIncidentCell x j
            ∈ (cert.P 0 false).cells) → (∀ (j : Fin 4), (∃ i s, LatticeVertexIncidentCell x j ∈
            (cert.P i s).cells ∧ LatticeVertexIncidentCell x (j + 1) ∈ (cert.P i s).cells) ↔
            (LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ∧ LatticeVertexIncidentCell x
            (j + 1) ∈ (cert.P 0 true).cells) ∨ (LatticeVertexIncidentCell x j ∈ (cert.P 0
            false).cells ∧ LatticeVertexIncidentCell x (j + 1) ∈ (cert.P 0 false).cells))) → ((∀
            (j : Fin 4), LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ∨
            LatticeVertexIncidentCell x j ∈ (cert.P 0 false).cells) → (
        let F : Fin 2 → ProtoTile := ![cert.P 0 true, cert.P 0 false]
        ∀ (owner : Fin (4 : ℕ) → Fin (2 : ℕ)), (∀ (j : Fin (4 : ℕ)), ∀ (a : Fin (2 : ℕ)),
            LatticeVertexIncidentCell x j ∈ (F a).cells ↔ owner j = a) → (∀ (j : Fin 4), (∃ i s,
            LatticeVertexIncidentCell x j ∈ (cert.P i s).cells ∧ LatticeVertexIncidentCell x (j +
            1) ∈ (cert.P i s).cells) ↔ owner j = owner (j + 1)))) ) := by
  classical
  intro C q cfg T cert x common_parent_iff hcover F owner hown j
  rw [common_parent_iff hcover j]
  have hA (j) : LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ↔ owner j = 0 :=
    hown j 0
  have hB (j) : LatticeVertexIncidentCell x j ∈ (cert.P 0 false).cells ↔ owner j = 1 :=
    hown j 1
  rw [hA, hA, hB, hB]
  have hf : ∀ a b : Fin 2, ((a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1)) ↔ a = b := by
    decide +kernel
  exact hf _ _

private theorem hsetAt727 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (x : GaussianInt), ∀ (owner : Fin
            (4 : ℕ) → Fin (2 : ℕ)), (∀ (j : Fin 4), (∃ i s, LatticeVertexIncidentCell x j ∈
            (cert.P i s).cells ∧ LatticeVertexIncidentCell x (j + 1) ∈ (cert.P i s).cells) ↔
            owner j = owner (j + 1)) → ((Finset.univ.filter fun j : Fin 4 => ∃ i s,
            LatticeVertexIncidentCell x j ∈ (cert.P i s).cells ∧ LatticeVertexIncidentCell x (j +
            1) ∈ (cert.P i s).cells) = Finset.univ.filter (fun j : Fin 4 => owner j = owner (j +
            1))) ) := by
  classical
  intro C q cfg T cert x owner hcommon
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcommon j]

private theorem finite_countAt734 :
    (by
      classical
      exact
        ∀ owner : Fin 4 → Fin 2, (¬ (owner 0 = owner 2 ∧ owner 1 ≠ owner 0 ∧ owner 3 ≠ owner 0) ∧
            ¬ (owner 1 = owner 3 ∧ owner 0 ≠ owner 1 ∧ owner 2 ≠ owner 1)) → Function.Surjective
            owner → (Finset.univ.filter (fun j : Fin 4 => owner j = owner (j + 1))).card = 2 ) := by
  classical
  decide +kernel

private theorem hOlat :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (∀ (c : CircleCoordinates), (∃ r :
            Fin 4 → CircleCoordinates, SemiProperQuadruple r ∧ ∃ i, r i = c) → (∀ (U :
            ProtoTile), (BandPrototile c U) → ((0 < c.1 ∨ U.cells.Nonempty) → (LatticeTile U))))
            → ((cert.O.cells.Nonempty) → (LatticeTile cert.O)) ) := by
  classical
  intro C q cfg T cert prototile_disk hOne
  rw [cert.precursor_eq]
  apply prototile_disk _
    ⟨cfg.firstPredecessor, cfg.firstProper.1, (0 : Fin 3).succ, rfl⟩ _
    (cert.plus_occurrence 0 false).1
  exact Or.inr (by simpa [← cert.precursor_eq] using hOne)

private theorem hFlatAt752 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (LatticeTile cert.O) → (
        let F : Fin 3 → ProtoTile :=
          ![TileCellComplement (cert.P 0 true) cert.O,
            TileCellComplement (cert.P 0 false) cert.O, cert.O]
        ∀ (a : Fin 3), LatticeTile (F a)) ) := by
  classical
  intro C q cfg T cert hOlat F a
  fin_cases a
  · exact cert.precursor_complement_lattice.1
  · exact cert.precursor_complement_lattice.2
  · exact hOlat

private theorem hFdAt757 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ((cert.P 0 true).cells ∩ (cert.P 0
            false).cells = cert.O.cells) → (
        let F : Fin 3 → ProtoTile :=
          ![TileCellComplement (cert.P 0 true) cert.O,
            TileCellComplement (cert.P 0 false) cert.O, cert.O]
        ∀ (a : Fin 3), ∀ (b : Fin 3), (a ≠ b) → (Disjoint (F a).cells (F b).cells)) ) := by
  classical
  intro C q cfg T cert hAB F a b hne
  apply Finset.disjoint_left.mpr
  intro c ha hb
  have hcAB : (c ∈ (cert.P 0 true).cells ∧ c ∈ (cert.P 0 false).cells) ↔
      c ∈ cert.O.cells := by rw [← Finset.mem_inter, hAB]
  fin_cases a <;> fin_cases b <;> simp only [Fin.mk_one, Fin.isValue, Fin.reduceFinMk, ne_eq,
      Fin.reduceEq, not_false_eq_true, TileCellComplement, Matrix.cons_val_one,
      Matrix.cons_val_zero, Finset.mem_sdiff, Matrix.cons_val, F, Fin.zero_eta, one_ne_zero,
      not_true_eq_false, zero_ne_one] at hne ha hb
  all_goals
    clear * - hcAB ha hb
    tauto

private theorem triple_sectors :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (∀ (U : ProtoTile), ∀ (z :
            GaussianInt), (z ∈ BoundaryFootprintVertices U) → (z ∈ FootprintVertices U)) → (∀ (x
            : GaussianInt), (LatticeTile cert.O) → (
        let F : Fin 3 → ProtoTile :=
          ![TileCellComplement (cert.P 0 true) cert.O,
            TileCellComplement (cert.P 0 false) cert.O, cert.O]
        ∀ (Q : ProtoTile), ∀ (S : ProtoTile), (LatticeTile Q) → ((LatticeTile S) →
            ((TouchingTriple Q S cert.O) → ((Q.cells ⊆ (F 0).cells) → ((S.cells ⊆ (F 1).cells) →
            ((x ∈ BoundaryFootprintVertices Q ∧
            x ∈ BoundaryFootprintVertices S ∧ x ∈ BoundaryFootprintVertices cert.O) → ((∀ j : Fin
                4, LatticeVertexIncidentCell x j ∈ (F 0).cells ∨ LatticeVertexIncidentCell x j ∈
                (F 1).cells ∨ LatticeVertexIncidentCell x j ∈ (F 2).cells) ∧ (∃ j : Fin 4,
                LatticeVertexIncidentCell x j ∈ (F 0).cells) ∧ (∃ j : Fin 4,
                LatticeVertexIncidentCell x j ∈ (F 1).cells) ∧ (∃ j : Fin 4,
                LatticeVertexIncidentCell x j ∈ (F 2).cells))))))))) ) := by
  classical
  intro C q cfg T cert boundary_foot x hOlat F Q S hQ hS ht hQc hSc htrans
  as_aux_lemma =>
  have hxraw : x ∈ FootprintVertices Q ∩ FootprintVertices S ∩ FootprintVertices cert.O :=
    ⟨⟨boundary_foot Q x htrans.1, boundary_foot S x htrans.2.1⟩,
      boundary_foot cert.O x htrans.2.2⟩
  obtain ⟨hc, hq, hs, ho, _⟩ :=
    LocalLatticeInterfaceSectors.1 Q S cert.O x hQ hS hOlat ht hxraw
  refine ⟨?_, ?_, ?_, ho⟩
  · intro j
    rcases hc j with h | h | h
    · exact Or.inl (hQc h)
    · exact Or.inr (Or.inl (hSc h))
    · exact Or.inr (Or.inr h)
  · obtain ⟨j, hj⟩ := hq
    exact ⟨j, hQc hj⟩
  · obtain ⟨j, hj⟩ := hs
    exact ⟨j, hSc hj⟩

private theorem hsectors :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (∀ (i : Fin 3), ∀ (s : Bool), (i = 1
            ∨ i = 2) → (LatticeTile (cert.Q i s))) → ((∀ (i : Fin 3), ∀ (s : Bool), (i = 1 ∨ i =
            2) → (LatticeTile (cert.S i s))) → (∀ (x : GaussianInt), (x ∈
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) → (
        let F : Fin 3 → ProtoTile :=
          ![TileCellComplement (cert.P 0 true) cert.O,
            TileCellComplement (cert.P 0 false) cert.O, cert.O]
        (∀ (Q : ProtoTile), ∀ (S : ProtoTile), (LatticeTile Q) → ((LatticeTile S) →
            ((TouchingTriple Q S cert.O) → ((Q.cells ⊆ (F 0).cells) → ((S.cells ⊆ (F 1).cells) →
            ((x ∈ BoundaryFootprintVertices Q ∧ x ∈ BoundaryFootprintVertices S ∧ x ∈
            BoundaryFootprintVertices cert.O) → ((∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ (F
            0).cells ∨ LatticeVertexIncidentCell x j ∈ (F 1).cells ∨ LatticeVertexIncidentCell x
            j ∈ (F 2).cells) ∧ (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ (F 0).cells) ∧ (∃ j
            : Fin 4, LatticeVertexIncidentCell x j ∈ (F 1).cells) ∧ (∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ (F 2).cells)))))))) → ((∀ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ (F 0).cells ∨ LatticeVertexIncidentCell x j ∈ (F
            1).cells ∨ LatticeVertexIncidentCell x j ∈ (F 2).cells) ∧ (∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ (F 0).cells) ∧ (∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ (F 1).cells) ∧ (∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ (F 2).cells))))) ) := by
  classical
  intro C q cfg T cert Q_lattice S_lattice x hxR F triple_sectors
  rcases Finset.mem_insert.mp hxR with ha | hb
  · exact triple_sectors (cert.Q 1 true) (cert.S 2 false)
      (Q_lattice 1 true (Or.inl rfl)) (S_lattice 2 false (Or.inr rfl))
      cert.precursorBoundary.first_touching
      cert.precursorBoundary.first_plus_child cert.precursorBoundary.first_minus_child
      ((cert.precursorBoundary.first_transition x).mpr ha)
  · exact triple_sectors (cert.Q 2 true) (cert.S 1 false)
      (Q_lattice 2 true (Or.inr rfl)) (S_lattice 1 false (Or.inl rfl))
      cert.precursorBoundary.second_touching
      cert.precursorBoundary.second_plus_child cert.precursorBoundary.second_minus_child
      ((cert.precursorBoundary.second_transition x).mpr (Finset.mem_singleton.mp hb))

private theorem hcoverAt811 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (cert.O.cells ⊆ (cert.P 0
            true).cells) → (∀ (x : GaussianInt),
        let F : Fin 3 → ProtoTile :=
          ![TileCellComplement (cert.P 0 true) cert.O,
            TileCellComplement (cert.P 0 false) cert.O, cert.O]
        ((∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ (F 0).cells ∨ LatticeVertexIncidentCell x
            j ∈ (F 1).cells ∨ LatticeVertexIncidentCell x j ∈ (F 2).cells) ∧ (∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ (F 0).cells) ∧ (∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ (F 1).cells) ∧ (∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ (F 2).cells)) → (∀ (j : Fin 4),
            LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ∨ LatticeVertexIncidentCell x j
            ∈ (cert.P 0 false).cells)) ) := by
  classical
  intro C q cfg T cert hOA x F hsectors j
  rcases hsectors.1 j with h | h | h
  · exact Or.inl (Finset.mem_sdiff.mp h).1
  · exact Or.inr (Finset.mem_sdiff.mp h).1
  · exact Or.inl (hOA h)

private theorem hsurjAt823 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (x : GaussianInt),
        let F : Fin 3 → ProtoTile :=
          ![TileCellComplement (cert.P 0 true) cert.O,
            TileCellComplement (cert.P 0 false) cert.O, cert.O]
        ((∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ (F 0).cells ∨ LatticeVertexIncidentCell x
            j ∈ (F 1).cells ∨ LatticeVertexIncidentCell x j ∈ (F 2).cells) ∧ (∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ (F 0).cells) ∧ (∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ (F 1).cells) ∧ (∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ (F 2).cells)) → (∀ (owner : Fin (4 : ℕ) → Fin (3 :
            ℕ)), (∀ (j : Fin (4 : ℕ)), ∀ (a : Fin (3 : ℕ)), LatticeVertexIncidentCell x j ∈ (F
            a).cells ↔ owner j = a) → (Function.Surjective owner)) ) := by
  classical
  intro C q cfg T cert x F hsectors owner hown a
  fin_cases a
  · obtain ⟨j, hj⟩ := hsectors.2.1
    exact ⟨j, (hown j 0).mp hj⟩
  · obtain ⟨j, hj⟩ := hsectors.2.2.1
    exact ⟨j, (hown j 1).mp hj⟩
  · obtain ⟨j, hj⟩ := hsectors.2.2.2
    exact ⟨j, (hown j 2).mp hj⟩

private theorem hmemA :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (cert.O.cells ⊆ (cert.P 0
            true).cells) → (∀ (x : GaussianInt),
        let F : Fin 3 → ProtoTile :=
          ![TileCellComplement (cert.P 0 true) cert.O,
            TileCellComplement (cert.P 0 false) cert.O, cert.O]
        ∀ (owner : Fin (4 : ℕ) → Fin (3 : ℕ)), (∀ (j : Fin (4 : ℕ)), ∀ (a : Fin (3 : ℕ)),
            LatticeVertexIncidentCell x j ∈ (F a).cells ↔ owner j = a) → (∀ (j : Fin 4),
            LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ↔ owner j = 0 ∨ owner j = 2)) )
            := by
  classical
  intro C q cfg T cert hOA x F owner hown j
  constructor
  · intro hj
    by_cases ho : LatticeVertexIncidentCell x j ∈ cert.O.cells
    · exact Or.inr ((hown j 2).mp ho)
    · exact Or.inl ((hown j 0).mp (Finset.mem_sdiff.mpr ⟨hj, ho⟩))
  · rintro (h | h)
    · exact (Finset.mem_sdiff.mp ((hown j 0).mpr h)).1
    · exact hOA ((hown j 2).mpr h)

private theorem hmemB :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), (cert.O.cells ⊆ (cert.P 0
            false).cells) → (∀ (x : GaussianInt),
        let F : Fin 3 → ProtoTile :=
          ![TileCellComplement (cert.P 0 true) cert.O,
            TileCellComplement (cert.P 0 false) cert.O, cert.O]
        ∀ (owner : Fin (4 : ℕ) → Fin (3 : ℕ)), (∀ (j : Fin (4 : ℕ)), ∀ (a : Fin (3 : ℕ)),
            LatticeVertexIncidentCell x j ∈ (F a).cells ↔ owner j = a) → (∀ (j : Fin 4),
            LatticeVertexIncidentCell x j ∈ (cert.P 0 false).cells ↔ owner j = 1 ∨ owner j = 2))
            ) := by
  classical
  intro C q cfg T cert hOB x F owner hown j
  constructor
  · intro hj
    by_cases ho : LatticeVertexIncidentCell x j ∈ cert.O.cells
    · exact Or.inr ((hown j 2).mp ho)
    · exact Or.inl ((hown j 1).mp (Finset.mem_sdiff.mpr ⟨hj, ho⟩))
  · rintro (h | h)
    · exact (Finset.mem_sdiff.mp ((hown j 1).mpr h)).1
    · exact hOB ((hown j 2).mpr h)

private theorem hcommonAt854 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (x : GaussianInt), ((∀ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ∨ LatticeVertexIncidentCell x j
            ∈ (cert.P 0 false).cells) → (∀ (j : Fin 4), (∃ i s, LatticeVertexIncidentCell x j ∈
            (cert.P i s).cells ∧ LatticeVertexIncidentCell x (j + 1) ∈ (cert.P i s).cells) ↔
            (LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ∧ LatticeVertexIncidentCell x
            (j + 1) ∈ (cert.P 0 true).cells) ∨ (LatticeVertexIncidentCell x j ∈ (cert.P 0
            false).cells ∧ LatticeVertexIncidentCell x (j + 1) ∈ (cert.P 0 false).cells))) → ((∀
            (j : Fin 4), LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ∨
            LatticeVertexIncidentCell x j ∈ (cert.P 0 false).cells) → (∀ (owner : Fin (4 : ℕ) →
            Fin (3 : ℕ)), (∀ (j : Fin 4), LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ↔
            owner j = 0 ∨ owner j = 2) → ((∀ (j : Fin 4), LatticeVertexIncidentCell x j ∈ (cert.P
            0 false).cells ↔ owner j = 1 ∨ owner j = 2) → (∀ (j : Fin 4), (∃ i s,
            LatticeVertexIncidentCell x j ∈ (cert.P i s).cells ∧ LatticeVertexIncidentCell x (j +
            1) ∈ (cert.P i s).cells) ↔ owner j = owner (j + 1) ∨ owner j = 2 ∨ owner (j + 1) =
            2)))) ) := by
  classical
  intro C q cfg T cert x common_parent_iff hcover owner hmemA hmemB j
  rw [common_parent_iff hcover j, hmemA, hmemA, hmemB, hmemB]
  have hf : ∀ a b : Fin 3,
      (((a = 0 ∨ a = 2) ∧ (b = 0 ∨ b = 2)) ∨
        ((a = 1 ∨ a = 2) ∧ (b = 1 ∨ b = 2))) ↔
        a = b ∨ a = 2 ∨ b = 2 := by decide +kernel
  exact hf _ _

private theorem hsetAt865 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (x : GaussianInt), ∀ (owner : Fin
            (4 : ℕ) → Fin (3 : ℕ)), (∀ (j : Fin 4), (∃ i s, LatticeVertexIncidentCell x j ∈
            (cert.P i s).cells ∧ LatticeVertexIncidentCell x (j + 1) ∈ (cert.P i s).cells) ↔
            owner j = owner (j + 1) ∨ owner j = 2 ∨ owner (j + 1) = 2) → ((Finset.univ.filter fun
            j : Fin 4 => ∃ i s, LatticeVertexIncidentCell x j ∈ (cert.P i s).cells ∧
            LatticeVertexIncidentCell x (j + 1) ∈ (cert.P i s).cells) = Finset.univ.filter (fun j
            : Fin 4 => owner j = owner (j + 1) ∨ owner j = 2 ∨ owner (j + 1) = 2)) ) := by
  classical
  intro C q cfg T cert x owner hcommon
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcommon j]

private theorem finite_countAt873 :
    (by
      classical
      exact
        ∀ owner : Fin 4 → Fin 3, (¬ (owner 0 = owner 2 ∧ owner 1 ≠ owner 0 ∧ owner 3 ≠ owner 0) ∧
            ¬ (owner 1 = owner 3 ∧ owner 0 ≠ owner 1 ∧ owner 2 ≠ owner 1)) → Function.Surjective
            owner → (Finset.univ.filter (fun j : Fin 4 => owner j = owner (j + 1) ∨ owner j = 2 ∨
            owner (j + 1) = 2)).card = 3 ) := by
  classical
  decide +kernel

end InterfaceNeighborGeometry

namespace InterfaceNeighborConclusion

private theorem rootNeighborCount :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
            BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (D : Finset GaussianInt), ∀ (P :
            Finset GaussianInt), (∀ x ∈ D \ P, x ∈ FootprintVertices cert.O ↔ x ∈
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) → ((∀
                (U : ProtoTile), ∀ (z :
            GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell z j ∈ U.cells) → (z ∈
            FootprintVertices U)) → ((∀ (U : ProtoTile), (U.cells.Nonempty) → (∀ (z :
            GaussianInt), (z ∈ FootprintVertices U) → (∃ j : Fin 4, LatticeVertexIncidentCell z j
            ∈ U.cells))) → ((∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈
            BoundaryFootprintVertices U) → (z ∈ FootprintVertices U)) → ((cert.O.cells ⊆ (cert.P
            0 true).cells) → ((cert.O.cells ⊆ (cert.P 0 false).cells) → (((cert.P 0 true).cells ∩
            (cert.P 0 false).cells = cert.O.cells) → ((∀ (c : CircleCoordinates), (∃ r : Fin 4 →
            CircleCoordinates, SemiProperQuadruple r ∧ ∃ i, r i = c) → (∀ (U : ProtoTile),
            (BandPrototile c U) → ((0 < c.1 ∨ U.cells.Nonempty) → (LatticeTile U)))) → ((∀ (i :
            Fin 3), ∀ (s : Bool), (i = 1 ∨ i = 2) → (LatticeTile (cert.Q i s))) → ((∀ (i : Fin
            3), ∀ (s : Bool), (i = 1 ∨ i = 2) → (LatticeTile (cert.S i s))) → (∀ (x :
            GaussianInt), (x ∈ D \ P) → ((∀ {α : Type}, ∀ (F : α → ProtoTile), (∀ a, LatticeTile
            (F a)) → (∀ (owner : Fin 4 → α), (∀ j, ∀ a, LatticeVertexIncidentCell x j ∈ (F
            a).cells ↔ owner j = a) → (¬ (owner 0 = owner 2 ∧ owner 1 ≠ owner 0 ∧ owner 3 ≠ owner
            0) ∧ ¬ (owner 1 = owner 3 ∧ owner 0 ≠ owner 1 ∧ owner 2 ≠ owner 1)))) → ((∀
            {α : Type}, ∀ (F : α → ProtoTile), (∀ a, ∀ b, a ≠ b → Disjoint (F a).cells (F
            b).cells) → ((∀ j : Fin 4, ∃ a, LatticeVertexIncidentCell x j ∈ (F a).cells) → (∃
            owner : Fin 4 → α, ∀ j, ∀ a, LatticeVertexIncidentCell x j ∈ (F a).cells ↔ owner j =
            a))) → (((∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ∨
            LatticeVertexIncidentCell x j ∈ (cert.P 0 false).cells) → (∀ (j : Fin 4), (∃ i s,
            LatticeVertexIncidentCell x j ∈ (cert.P i s).cells ∧ LatticeVertexIncidentCell x (j +
            1) ∈ (cert.P i s).cells) ↔ (LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ∧
            LatticeVertexIncidentCell x (j + 1) ∈ (cert.P 0 true).cells) ∨
            (LatticeVertexIncidentCell x j ∈ (cert.P 0 false).cells ∧ LatticeVertexIncidentCell x
            (j + 1) ∈ (cert.P 0 false).cells))) → (((P.filter fun y => @decide
            (FourNeighborAdjacent y x) (Classical.propDecidable _)).card = (Finset.univ.filter
            fun j : Fin 4 => ∃ i s, LatticeVertexIncidentCell x j ∈ (cert.P i s).cells ∧
            LatticeVertexIncidentCell x (j + 1) ∈ (cert.P i s).cells).card) → ((x ∈
            ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) →
                ((P.filter fun y => @decide
            (FourNeighborAdjacent y x) (Classical.propDecidable _)).card = if cert.O.cells = ∅
            then 2 else 3)))))))))))))))) ) := by
  classical
  intro C q cfg T cert D P hprecursor incident_foot foot_incident boundary_foot hOA hOB hAB
      prototile_disk Q_lattice S_lattice x hx no_diagonal label_sectors common_parent_iff
      neighbor_count hxR
  by_cases hempty : cert.O.cells = ∅
  · rw [ite_eq_left hempty, neighbor_count]
    have hbranch := cert.precursorBoundary.branch
    rcases hbranch with ⟨hne, _⟩ | hbranch
    · exact (Finset.nonempty_iff_ne_empty.mp hne hempty).elim
    have hxa : x = cert.precursorBoundary.a := by
      simpa [hbranch.2.1] using hxR
    have htransition := (cert.precursorBoundary.first_transition x).mpr hxa
    have hQlat := Q_lattice 1 true (Or.inl rfl)
    have hSlat := S_lattice 2 false (Or.inr rfl)
    obtain ⟨jA, hjA⟩ := foot_incident _ (LatticeTileGridStructure _ hQlat).1.1 x
      (boundary_foot _ x htransition.1)
    obtain ⟨jB, hjB⟩ := foot_incident _ (LatticeTileGridStructure _ hSlat).1.1 x
      (boundary_foot _ x htransition.2.1)
    have hA : LatticeVertexIncidentCell x jA ∈ (cert.P 0 true).cells :=
      (Finset.mem_sdiff.mp (cert.precursorBoundary.first_plus_child hjA)).1
    have hB : LatticeVertexIncidentCell x jB ∈ (cert.P 0 false).cells :=
      (Finset.mem_sdiff.mp (cert.precursorBoundary.first_minus_child hjB)).1
    have hzero (U : ProtoTile) : TileTranslation U 0 = U :=
        InterfaceNeighborGeometry.hzeroAt680 U
    have hcover (j : Fin 4) :
        LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ∨
          LatticeVertexIncidentCell x j ∈ (cert.P 0 false).cells :=
              InterfaceNeighborGeometry.hcoverAt684 C q cfg T cert D P hprecursor
              incident_foot x hx hxR hzero j
    let F : Fin 2 → ProtoTile := ![cert.P 0 true, cert.P 0 false]
    have hFlat (a : Fin 2) : LatticeTile (F a) := by
      fin_cases a <;> exact cert.parent_lattice _ _
    have hFd (a b : Fin 2) (hne : a ≠ b) : Disjoint (F a).cells (F b).cells :=
        InterfaceNeighborGeometry.hFdAt697 C q cfg T cert hAB hempty a b hne
    obtain ⟨owner, hown⟩ := label_sectors F hFd (fun j => by
      rcases hcover j with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩)
    have hsurj : Function.Surjective owner := InterfaceNeighborGeometry.hsurjAt709 C q cfg T
        cert x jA jB hA hB owner hown
    have hcommon (j : Fin 4) :
        (∃ i s, LatticeVertexIncidentCell x j ∈ (cert.P i s).cells ∧
          LatticeVertexIncidentCell x (j + 1) ∈ (cert.P i s).cells) ↔
          owner j = owner (j + 1) := InterfaceNeighborGeometry.hcommonAt714 C q cfg T cert x
              common_parent_iff hcover owner hown j
    have hset : (Finset.univ.filter fun j : Fin 4 => ∃ i s,
        LatticeVertexIncidentCell x j ∈ (cert.P i s).cells ∧
        LatticeVertexIncidentCell x (j + 1) ∈ (cert.P i s).cells) =
        Finset.univ.filter (fun j : Fin 4 => owner j = owner (j + 1)) :=
            InterfaceNeighborGeometry.hsetAt727 C q cfg T cert x owner hcommon
    rw [hset]
    have finite_count : ∀ owner : Fin 4 → Fin 2,
        (¬ (owner 0 = owner 2 ∧ owner 1 ≠ owner 0 ∧ owner 3 ≠ owner 0) ∧
         ¬ (owner 1 = owner 3 ∧ owner 0 ≠ owner 1 ∧ owner 2 ≠ owner 1)) →
        Function.Surjective owner →
        (Finset.univ.filter (fun j : Fin 4 => owner j = owner (j + 1))).card = 2 :=
            InterfaceNeighborGeometry.finite_countAt734
    exact finite_count owner (no_diagonal F hFlat owner hown) hsurj
  · rw [ite_eq_right hempty]
    have hOne : cert.O.cells.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    have hOlat : LatticeTile cert.O := InterfaceNeighborGeometry.hOlat C q cfg T cert
        prototile_disk hOne
    let F : Fin 3 → ProtoTile :=
      ![TileCellComplement (cert.P 0 true) cert.O,
        TileCellComplement (cert.P 0 false) cert.O, cert.O]
    have hFlat (a : Fin 3) : LatticeTile (F a) := InterfaceNeighborGeometry.hFlatAt752 C q
        cfg T cert hOlat a
    have hFd (a b : Fin 3) (hne : a ≠ b) : Disjoint (F a).cells (F b).cells :=
        InterfaceNeighborGeometry.hFdAt757 C q cfg T cert hAB a b hne
    have triple_sectors (Q S : ProtoTile) (hQ : LatticeTile Q) (hS : LatticeTile S)
        (ht : TouchingTriple Q S cert.O)
        (hQc : Q.cells ⊆ (F 0).cells) (hSc : S.cells ⊆ (F 1).cells)
        (htrans : x ∈ BoundaryFootprintVertices Q ∧
          x ∈ BoundaryFootprintVertices S ∧ x ∈ BoundaryFootprintVertices cert.O) :
        (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ (F 0).cells ∨
          LatticeVertexIncidentCell x j ∈ (F 1).cells ∨
          LatticeVertexIncidentCell x j ∈ (F 2).cells) ∧
        (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ (F 0).cells) ∧
        (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ (F 1).cells) ∧
        (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ (F 2).cells) :=
            InterfaceNeighborGeometry.triple_sectors C q cfg T cert boundary_foot x hOlat Q S
            hQ hS ht hQc hSc htrans
    have hsectors :
        (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ (F 0).cells ∨
          LatticeVertexIncidentCell x j ∈ (F 1).cells ∨
          LatticeVertexIncidentCell x j ∈ (F 2).cells) ∧
        (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ (F 0).cells) ∧
        (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ (F 1).cells) ∧
        (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ (F 2).cells) :=
            InterfaceNeighborGeometry.hsectors C q cfg T cert Q_lattice S_lattice x hxR
            triple_sectors
    have hcover (j : Fin 4) :
        LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ∨
          LatticeVertexIncidentCell x j ∈ (cert.P 0 false).cells :=
              InterfaceNeighborGeometry.hcoverAt811 C q cfg T cert hOA x hsectors j
    obtain ⟨owner, hown⟩ := label_sectors F hFd (fun j => by
      rcases hsectors.1 j with h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩)
    have hsurj : Function.Surjective owner := InterfaceNeighborGeometry.hsurjAt823 C q cfg T
        cert x hsectors owner hown
    have hmemA (j : Fin 4) :
        LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ↔
          owner j = 0 ∨ owner j = 2 := InterfaceNeighborGeometry.hmemA C q cfg T cert hOA x
              owner hown j
    have hmemB (j : Fin 4) :
        LatticeVertexIncidentCell x j ∈ (cert.P 0 false).cells ↔
          owner j = 1 ∨ owner j = 2 := InterfaceNeighborGeometry.hmemB C q cfg T cert hOB x
              owner hown j
    have hcommon (j : Fin 4) :
        (∃ i s, LatticeVertexIncidentCell x j ∈ (cert.P i s).cells ∧
          LatticeVertexIncidentCell x (j + 1) ∈ (cert.P i s).cells) ↔
          owner j = owner (j + 1) ∨ owner j = 2 ∨ owner (j + 1) = 2 :=
              InterfaceNeighborGeometry.hcommonAt854 C q cfg T cert x common_parent_iff
              hcover owner hmemA hmemB j
    rw [neighbor_count]
    have hset : (Finset.univ.filter fun j : Fin 4 => ∃ i s,
        LatticeVertexIncidentCell x j ∈ (cert.P i s).cells ∧
        LatticeVertexIncidentCell x (j + 1) ∈ (cert.P i s).cells) =
        Finset.univ.filter (fun j : Fin 4 =>
          owner j = owner (j + 1) ∨ owner j = 2 ∨ owner (j + 1) = 2) :=
              InterfaceNeighborGeometry.hsetAt865 C q cfg T cert x owner hcommon
    rw [hset]
    have finite_count : ∀ owner : Fin 4 → Fin 3,
        (¬ (owner 0 = owner 2 ∧ owner 1 ≠ owner 0 ∧ owner 3 ≠ owner 0) ∧
         ¬ (owner 1 = owner 3 ∧ owner 0 ≠ owner 1 ∧ owner 2 ≠ owner 1)) →
        Function.Surjective owner →
        (Finset.univ.filter (fun j : Fin 4 =>
          owner j = owner (j + 1) ∨ owner j = 2 ∨ owner (j + 1) = 2)).card = 3 :=
              InterfaceNeighborGeometry.finite_countAt873
    exact finite_count owner (no_diagonal F hFlat owner hown) hsurj

end InterfaceNeighborConclusion

theorem P4250T2InterfaceNeighborCount :
    ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
        BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
        BandOrderedGeneralLayoutCertificate q cfg C T), (BandPrototile (q 0) T) → ((LatticeTile
        T) → (∀ (D : Finset GaussianInt), ∀ (P : Finset GaussianInt), (∀ x, x ∈ D ↔
      x ∈ FootprintVertices T ∧ x ∉ BoundaryFootprintVertices T) → ((∀ x, x ∈ P ↔ x ∈ D ∧ ∃ i s,
      x ∈ FootprintVertices (cert.P i s) ∧
        x ∉ BoundaryFootprintVertices (cert.P i s)) → ((∀ x ∈ D \ P,
      x ∈ FootprintVertices cert.O ↔
        x ∈ ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) → ((∀
            x ∈ D \ P,
      Nat.card {is : Fin 3 × Bool //
        x ∈ BoundaryFootprintVertices (cert.P is.1 is.2)} = 2 →
      GaussianRealPoint x = TileCentroid T →
        x ∈ ({cert.precursorBoundary.a, cert.precursorBoundary.b} : Finset GaussianInt)) → (
    let W := D \ P
    let R : Finset GaussianInt := {cert.precursorBoundary.a, cert.precursorBoundary.b}
    ∀ x ∈ W,
    let k := Nat.card {is : Fin 3 × Bool //
        x ∈ BoundaryFootprintVertices (cert.P is.1 is.2)}
      let n := (P.filter fun y => @decide (FourNeighborAdjacent y x)
        (Classical.propDecidable _)).card
      (x ∉ R → n + k = 4 ∧ (k = 2 ∨ k = 3) ∧
        GaussianRealPoint x ≠ TileCentroid T) ∧
      (x ∈ R → n = if cert.O.cells = ∅ then 2 else 3))))))) := by
  intro C q cfg T cert hT hlat D P hD hP hprecursor hcentral
-- BODY
  classical
  exact (by
    have incident_foot := InterfaceNeighborGeometry.incident_foot
    have foot_incident := fun (U : ProtoTile) (hne : U.cells.Nonempty) (z : GaussianInt) =>
      LatticeFootprintIncidence.incidentCell U z hne
    have full_iff := InterfaceNeighborGeometry.full_iff incident_foot foot_incident
    have boundary_foot := InterfaceNeighborGeometry.boundary_foot incident_foot
    have hOA := InterfaceNeighborGeometry.hOA C q cfg T cert
    have hOB := InterfaceNeighborGeometry.hOB C q cfg T cert
    have hsep := BandOriginalPairSeparation cert.P cert.O cert.u cert.v hOA hOB cert.partition
    have hAB := InterfaceNeighborGeometry.hAB C q cfg T cert hsep
    have parent_disjoint := InterfaceNeighborGeometry.parent_disjoint C q cfg T cert hsep
        (InterfaceNeighborGeometry.parentLabel_injective)
        (InterfaceNeighborGeometry.parentOccurrence C q cfg T cert)
    have hchildPos := InterfaceNeighborGeometry.hchildPos q cfg
    have parent_regular (i : Fin 3) (s : Bool) :
        ∀ a b, FourNeighborAdjacent a b →
          a ∈ BoundaryFootprintVertices (cert.P i s) →
          b ∈ BoundaryFootprintVertices (cert.P i s) →
          ¬ OpenLatticeEdge a b ⊆ interior (TileRealization (cert.P i s)) :=
      (LatticeEdgeRegularity
        (⟨⟨q i.succ, Or.inl (hchildPos i), q, cfg.proper.1, i.succ, rfl⟩,
          hchildPos i⟩ : BandCircle)
        (cert.P i s) (cert.outer_occurrence i s).1 (cert.parent_lattice i s)).1
    have prototile_disk := InterfaceNeighborGeometry.prototile_disk
    have retained_pos := InterfaceNeighborGeometry.retained_pos q cfg hchildPos
    have Q_lattice (i : Fin 3) (s : Bool) (hi : i = 1 ∨ i = 2) :
        LatticeTile (cert.Q i s) :=
      prototile_disk _ ⟨cfg.firstPredecessor, cfg.firstProper.1, i.succ, rfl⟩ _
        (cert.plus_occurrence i s).1 (Or.inl (retained_pos i hi))
    have S_lattice (i : Fin 3) (s : Bool) (hi : i = 1 ∨ i = 2) :
        LatticeTile (cert.S i s) :=
      prototile_disk _ ⟨cfg.firstPredecessor, cfg.firstProper.1, i.succ, rfl⟩ _
        (cert.minus_occurrence i s).1 (Or.inl (retained_pos i hi))
    dsimp only
    intro x hx
    have hxD := (Finset.mem_sdiff.mp hx).1
    have hxP := (Finset.mem_sdiff.mp hx).2
    have hxT := (hD x).mp hxD
    have hcells := (full_iff T x).mp hxT
    have no_parent_interior := InterfaceNeighborGeometry.no_parent_interior C q cfg T cert D P hP
        x hxD hxP
    have no_diagonal {α : Type} (F : α → ProtoTile) (hF : ∀ a, LatticeTile (F a))
        (owner : Fin 4 → α)
        (hown : ∀ j a, LatticeVertexIncidentCell x j ∈ (F a).cells ↔ owner j = a) :=
            InterfaceNeighborGeometry.no_diagonal x (α := α) F hF owner hown
    have label_sectors {α : Type} (F : α → ProtoTile)
        (hd : ∀ a b, a ≠ b → Disjoint (F a).cells (F b).cells)
        (hcover : ∀ j : Fin 4, ∃ a, LatticeVertexIncidentCell x j ∈ (F a).cells) :=
            InterfaceNeighborGeometry.label_sectors x (α := α) F hd hcover
    have common_parent_iff := InterfaceNeighborGeometry.common_parent_iff C q cfg T cert
        parent_disjoint x
    let neighbor : Fin 4 → GaussianInt := ![x + ⟨0, 1⟩, x - 1, x - ⟨0, 1⟩, x + 1]
    have shared_cells := InterfaceNeighborGeometry.shared_cells x
    -- Each edge is counted precisely when its two incident cells share a parent.
    have neighbor_bridge := InterfaceNeighborGeometry.neighbor_bridge C q cfg T cert D P hD hP
        incident_foot full_iff (InterfaceNeighborGeometry.edge_endpoint
        (AdjacentCellInterior.horizontal)
        (AdjacentCellInterior.vertical)) parent_regular x no_parent_interior
        shared_cells
    have neighbor_injective := InterfaceNeighborGeometry.neighbor_injective x
    have neighbor_adjacent (j : Fin 4) : FourNeighborAdjacent (neighbor j) x := by
      fin_cases j <;> simp [neighbor, FourNeighborAdjacent]
    have neighbor_count := InterfaceNeighborGeometry.neighbor_count C q cfg T cert P x
        neighbor_bridge
              neighbor_injective neighbor_adjacent ((show
                  ∀ (y : GaussianInt), (FourNeighborAdjacent y x) → (∃ j : Fin
                  4, neighbor j = y)
                from by
                  classical
                  intro y hy
                  rcases hy with rfl | rfl | rfl | rfl
                  · exact ⟨1, by simp [neighbor]⟩
                  · exact ⟨3, by simp [neighbor]⟩
                  · exact ⟨2, by simp [neighbor]⟩
                  · exact ⟨0, by simp [neighbor]⟩))
    constructor
    · intro hnotR
      have owner_exists := InterfaceNeighborGeometry.owner_exists C q cfg T cert x hcells
      let owner (j : Fin 4) : Fin 3 × Bool := Classical.choose (owner_exists j)
      have owner_spec (j : Fin 4) :
          LatticeVertexIncidentCell x j ∈ (cert.P (owner j).1 (owner j).2).cells :=
        Classical.choose_spec (owner_exists j)
      have owner_iff := InterfaceNeighborGeometry.owner_iff C q cfg T cert
          (InterfaceNeighborGeometry.parent_unique C q cfg T cert hAB parent_disjoint) x
          (InterfaceNeighborGeometry.hnoO C q cfg T cert D P hprecursor incident_foot x hx hnotR)
          owner_exists owner_spec
      have hdiag := no_diagonal (fun a : Fin 3 × Bool => cert.P a.1 a.2)
        (fun a => cert.parent_lattice a.1 a.2) owner owner_iff
      have hcard : Nat.card {a : Fin 3 × Bool //
          x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)} =
          (Finset.univ.image owner).card := InterfaceNeighborGeometry.hcard C q cfg T cert x
              owner_exists (InterfaceNeighborGeometry.hboundary C q cfg T cert incident_foot
              foot_incident boundary_foot x no_parent_interior owner_exists owner_spec owner_iff)
      have hnot_constant := InterfaceNeighborGeometry.hnot_constant C q cfg T cert D P hP
          full_iff x hxD hxP owner_exists owner_iff
      have hncount : (P.filter fun y => @decide (FourNeighborAdjacent y x)
          (Classical.propDecidable _)).card =
          (Finset.univ.filter (fun j : Fin 4 => owner j = owner (j + 1))).card :=
              InterfaceNeighborGeometry.hncount C q cfg T cert P x neighbor_count owner_exists
              owner_spec owner_iff
      have hclass := BandOrderedGeneralInteriorStarClassification q cfg C T cert hlat x hxT.1 hxT.2
      have hsum := (InterfaceNeighborGeometry.finite_countAt614) owner hdiag hnot_constant
      have hk23 := InterfaceNeighborGeometry.hk23 C q cfg T cert P x neighbor_count owner_exists
          hcard hncount hclass hsum (InterfaceNeighborGeometry.hlow C q cfg T cert x owner_exists
          hnot_constant)
      refine ⟨?_, hk23, ?_⟩
      · rw [hncount, hcard]
        exact hsum
      · intro hc
        rcases hk23 with hk | hk
        · exact hnotR (hcentral x hx hk hc)
        · exact (hclass.2.1 hk).2 hc
    · intro hxR
      exact (InterfaceNeighborConclusion.rootNeighborCount C q cfg T cert D P hprecursor
          incident_foot foot_incident boundary_foot hOA hOB hAB prototile_disk Q_lattice
          S_lattice x hx no_diagonal label_sectors common_parent_iff neighbor_count hxR))

end ApollonianSuperharmonic

end
