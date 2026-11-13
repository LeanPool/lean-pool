/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.InteriorFootprintIncidence

public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidenceZeroOppositeChord
public import LeanPool.ApollonianSuperharmonic.BandOriginalPairSeparation
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIntersectionClassification
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate

-- [TABLET NODE: P4120T1GeneralDescent]

/-!
# P4120T1GeneralDescent

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace GeneralDescentGeometry



private theorem hpos :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
          BandOrderedGeneralConfiguration q →
            ((0 : ℤ) < (q (0 : Fin (4 : ℕ))).1 ∧
                (∀ (i : Fin (3 : ℕ)), (0 : ℤ) ≤ (q i.succ).1) ∧
                  ∀ (i : Fin (3 : ℕ)),
                    ∀ (j : Fin (3 : ℕ)),
                      (q i.succ).1 = (0 : ℤ) → (q j.succ).1 = (0 : ℤ) → i = j) →
              ∀ i : Fin 3, 0 < (q i.succ).1
    ) := by
  classical
  intro q cfg hcurv i
  have hn := hcurv.2.1 i
  have hne0 := cfg.noLine i.succ
  by_contra h
  have hle : (q i.succ).1 ≤ 0 := le_of_not_gt h
  have heq : (q i.succ).1 = 0 := le_antisymm hle hn
  exact hne0 heq

private theorem hOsub :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), cert.O.cells ⊆ (cert.P 0 false).cells ) := by
  classical
  intro q cfg C T cert z hz
  rw [cert.precursor_cells] at hz
  exact (cert.minus_union z).mpr ⟨0, true, hz⟩

private theorem tile_zero :
    (by
      classical
      exact
        ∀ (U : ProtoTile), TileTranslation U 0 = U ) := by
  classical
  intro U
  cases U
  have hz : GaussianTranslation 0 = id := by
    funext z
    simp [GaussianTranslation]
  simp [TileTranslation, hz, Finset.image_id]

private theorem modified_cell_owner :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (cert.O.cells ⊆ (cert.P 0 false).cells) → (∀ (c : LatticeCell), (c ∈ T.cells) →
            (∃ a : PeriodicSubtileIndex, a.first = 0 ∧ a.second = 0 ∧ c ∈ (cert.modified.tile
            a).cells)) ) := by
  classical
  intro q cfg C T cert hOsub c hc
  obtain ⟨i, s, hP⟩ := (cert.outer_union c).mp hc
  cases i using Fin.cases with
  | zero =>
    cases s
    · refine ⟨⟨.B, 0, 0⟩, rfl, rfl, ?_⟩
      rw [cert.modified_tile]
      simpa [ModifiedSubtileOccurrenceInterpretation, TileTranslation,
        GaussianTranslation] using hP
    · by_cases hO : c ∈ cert.O.cells
      · refine ⟨⟨.B, 0, 0⟩, rfl, rfl, ?_⟩
        rw [cert.modified_tile]
        simpa [ModifiedSubtileOccurrenceInterpretation, TileTranslation,
          GaussianTranslation] using hOsub hO
      · refine ⟨⟨.A, 0, 0⟩, rfl, rfl, ?_⟩
        rw [cert.modified_tile]
        simpa [ModifiedSubtileOccurrenceInterpretation, TileTranslation,
          GaussianTranslation, TileCellComplement] using
            (Finset.mem_sdiff.mpr ⟨hP, hO⟩)
  | succ i =>
    cases i using Fin.cases with
    | zero =>
      cases s
      · refine ⟨⟨.D, 0, 0⟩, rfl, rfl, ?_⟩
        rw [cert.modified_tile]
        simpa [ModifiedSubtileOccurrenceInterpretation, TileTranslation,
          GaussianTranslation] using hP
      · refine ⟨⟨.C, 0, 0⟩, rfl, rfl, ?_⟩
        rw [cert.modified_tile]
        simpa [ModifiedSubtileOccurrenceInterpretation, TileTranslation,
          GaussianTranslation] using hP
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        cases s
        · refine ⟨⟨.F, 0, 0⟩, rfl, rfl, ?_⟩
          rw [cert.modified_tile]
          simpa [ModifiedSubtileOccurrenceInterpretation, TileTranslation,
            GaussianTranslation] using hP
        · refine ⟨⟨.E, 0, 0⟩, rfl, rfl, ?_⟩
          rw [cert.modified_tile]
          simpa [ModifiedSubtileOccurrenceInterpretation, TileTranslation,
            GaussianTranslation] using hP
      | succ i => exact Fin.elim0 i

private theorem incident_footprint :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (j : Fin 4), ∀ (U : ProtoTile), (LatticeVertexIncidentCell x j ∈
            U.cells) → (x ∈ FootprintVertices U) ) := by
  classical
  intro x j U hc
  have hn : U.cells.Nonempty := ⟨LatticeVertexIncidentCell x j, hc⟩
  rw [FootprintVertices, ite_eq_left hn]
  refine ⟨LatticeVertexIncidentCell x j, hc, ?_⟩
  fin_cases j <;> simp [LatticeVertexIncidentCell, sub_eq_add_neg,
    add_assoc, add_comm, add_left_comm]

private theorem cell_edge_vleft :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        ∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells) → ({z, z + I} ∈ FootprintEdges U) )
            := by
  classical
  intro I U z hz
  simp only [FootprintEdges, Set.mem_ofPred_eq]
  refine ⟨z, hz, ?_⟩
  exact Or.inr (Or.inl rfl)

private theorem cell_edge_vright :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        ∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells) → ({z + 1, z + 1 + I} ∈
            FootprintEdges U) ) := by
  classical
  intro I U z hz
  simp only [FootprintEdges, Set.mem_ofPred_eq]
  refine ⟨z, hz, ?_⟩
  exact Or.inr (Or.inr (Or.inl rfl))

private theorem cell_edge_hbottom :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells) → ({z, z + 1} ∈ FootprintEdges U) )
            := by
  classical
  intro U z hz
  simp only [FootprintEdges, Set.mem_ofPred_eq]
  exact ⟨z, hz, Or.inl rfl⟩

private theorem cell_edge_htop :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        ∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells) → ({z + I, z + 1 + I} ∈
            FootprintEdges U) ) := by
  classical
  intro I U z hz
  simp only [FootprintEdges, Set.mem_ofPred_eq]
  refine ⟨z, hz, ?_⟩
  exact Or.inr (Or.inr (Or.inr rfl))

private theorem edge_support :
    (by
      classical
      exact
        ∀ (x : GaussianInt),
        let I : GaussianInt := ⟨0, 1⟩
        ∀ (U : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ FootprintEdges U) → ((x ∈ e) → (∃ j :
            Fin 4, LatticeVertexIncidentCell x j ∈ U.cells ∧ ((e = {x, x + I} ∧ (j = 0 ∨ j = 1))
            ∨ (e = {x - 1, x} ∧ (j = 1 ∨ j = 2)) ∨ (e = {x - I, x} ∧ (j = 2 ∨ j = 3)) ∨ (e = {x,
            x + 1} ∧ (j = 3 ∨ j = 0))))) ) := by
  classical
  intro x I U e he hxedge
  simp only [FootprintEdges, Set.mem_ofPred_eq] at he
  rcases he with ⟨z, hz, hedge⟩
  rcases hedge with hedge | hedge | hedge | hedge
  · subst e
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxedge
    rcases hxedge with hxz | hxz
    · subst z
      refine ⟨0, ?_, ?_⟩
      · simpa [LatticeVertexIncidentCell] using hz
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩))
    · have hz' : z = x - 1 := by calc
        z = (z + 1) - 1 := by abel
        _ = x - 1 := by rw [hxz]
      subst z
      refine ⟨1, ?_, ?_⟩
      · simpa [LatticeVertexIncidentCell] using hz
      · refine Or.inr (Or.inl ⟨?_, Or.inl rfl⟩)
        simp
  · subst e
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxedge
    rcases hxedge with hxz | hxz
    · subst z
      refine ⟨0, ?_, ?_⟩
      · simpa [LatticeVertexIncidentCell] using hz
      · exact Or.inl ⟨rfl, Or.inl rfl⟩
    · have hz' : z = x - I := by calc
        z = (z + I) - I := by abel
        _ = x - I := by rw [hxz]
      subst z
      refine ⟨3, ?_, ?_⟩
      · simpa [LatticeVertexIncidentCell, I] using hz
      · refine Or.inr (Or.inr (Or.inl ⟨?_, Or.inr rfl⟩))
        simp [I, add_comm]
  · subst e
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxedge
    rcases hxedge with hxz | hxz
    · have hz' : z = x - 1 := by calc
        z = (z + 1) - 1 := by abel
        _ = x - 1 := by rw [hxz]
      subst z
      refine ⟨1, ?_, ?_⟩
      · simpa [LatticeVertexIncidentCell] using hz
      · refine Or.inl ⟨?_, Or.inr rfl⟩
        simp [I, add_comm]
    · have hz' : z = x - 1 - I := by calc
        z = (z + 1 + I) - 1 - I := by abel
        _ = x - 1 - I := by rw [hxz]
      subst z
      refine ⟨2, ?_, ?_⟩
      · simpa [LatticeVertexIncidentCell, I, sub_eq_add_neg, add_assoc,
          add_comm, add_left_comm] using hz
      · refine Or.inr (Or.inr (Or.inl ⟨?_, Or.inl rfl⟩))
        have h1 : (x - 1 - I) + 1 = x - I := by abel
        rw [h1]
        simp [I, sub_eq_add_neg, add_comm, add_left_comm]
  · subst e
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxedge
    rcases hxedge with hxz | hxz
    · have hz' : z = x - I := by calc
        z = (z + I) - I := by abel
        _ = x - I := by rw [hxz]
      subst z
      refine ⟨3, ?_, ?_⟩
      · simpa [LatticeVertexIncidentCell, I] using hz
      · refine Or.inr (Or.inr (Or.inr ⟨?_, Or.inl rfl⟩))
        simp [I, add_comm, add_left_comm]
    · have hz' : z = x - 1 - I := by calc
        z = (z + 1 + I) - 1 - I := by abel
        _ = x - 1 - I := by rw [hxz]
      subst z
      refine ⟨2, ?_, ?_⟩
      · simpa [LatticeVertexIncidentCell, I, sub_eq_add_neg, add_assoc,
          add_comm, add_left_comm] using hz
      · refine Or.inr (Or.inl ⟨?_, Or.inr rfl⟩)
        simp [I, add_comm, add_left_comm]

private theorem boundary_edge_is_footprint :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        (∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells) → ({z, z + I} ∈ FootprintEdges U))
            → ((∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells) → ({z + 1, z + 1 + I} ∈
            FootprintEdges U)) → ((∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells) → ({z,
            z + 1} ∈ FootprintEdges U)) → ((∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells)
            → ({z + I, z + 1 + I} ∈ FootprintEdges U)) → (∀ (U : ProtoTile), ∀ (e : Finset
            GaussianInt), (e ∈ BoundaryFootprintEdges U) → (e ∈ FootprintEdges U))))) ) := by
  classical
  intro I cell_edge_vleft cell_edge_vright cell_edge_hbottom cell_edge_htop U e he
  rcases he with ⟨z, ⟨rfl, hside⟩ | ⟨rfl, hside⟩⟩
  · rcases hside with ⟨hz, _⟩ | ⟨_, hz⟩
    · exact cell_edge_hbottom U z hz
    · have hz' := cell_edge_htop U (z - I) hz
      simpa [I, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz'
  · rcases hside with ⟨hz, _⟩ | ⟨_, hz⟩
    · exact cell_edge_vleft U z hz
    · have hz' := cell_edge_vright U (z - 1) hz
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz'

private theorem parent_boundary_incident_cell :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt),
        let I : GaussianInt := ⟨0, 1⟩
        (∀ (U : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ FootprintEdges U) → ((x ∈ e) → (∃ j
            : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells ∧ ((e = {x, x + I} ∧ (j = 0 ∨ j =
            1)) ∨ (e = {x - 1, x} ∧ (j = 1 ∨ j = 2)) ∨ (e = {x - I, x} ∧ (j = 2 ∨ j = 3)) ∨ (e =
            {x, x + 1} ∧ (j = 3 ∨ j = 0)))))) → ((∀ (U : ProtoTile), ∀ (e : Finset GaussianInt),
            (e ∈ BoundaryFootprintEdges U) → (e ∈ FootprintEdges U)) → ((∀ (i : Fin 3), ∀ (s :
            Bool), (cert.P i s).cells.Nonempty) → (∀ (i : Fin 3), ∀ (s : Bool), (x ∈
            BoundaryFootprintVertices (cert.P i s)) → (∃ j : Fin 4, LatticeVertexIncidentCell x j
            ∈ (cert.P i s).cells)))) ) := by
  classical
  intro q cfg C T cert x I edge_support boundary_edge_is_footprint parent_cells_nonempty i s hB
  simp only [BoundaryFootprintVertices, ite_eq_left (parent_cells_nonempty i s),
    Set.mem_ofPred_eq] at hB
  rcases hB with ⟨e, he, hxe⟩
  obtain ⟨j, hj, _⟩ := edge_support (cert.P i s) e
    (boundary_edge_is_footprint _ _ he) hxe
  exact ⟨j, hj⟩

private theorem all_incident_not_boundary :
    (by
      classical
      exact
        ∀ (x : GaussianInt),
        ∀ (U : ProtoTile), (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells) → ((x ∈
            BoundaryFootprintVertices U) → (False)) ) := by
  classical
  intro x U hall hB
  let I : GaussianInt := ⟨0, 1⟩
  have hne : U.cells.Nonempty := ⟨LatticeVertexIncidentCell x 0, hall 0⟩
  simp only [BoundaryFootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq] at hB
  rcases hB with ⟨e, he, hxe⟩
  rcases he with ⟨z, ⟨rfl, hs⟩ | ⟨rfl, hs⟩⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
    rcases hxe with hxz | hxz
    · subst z
      rcases hs with ⟨_, hmiss⟩ | ⟨hmiss, _⟩
      · exact hmiss (by simpa [LatticeVertexIncidentCell, I] using hall 3)
      · exact hmiss (by simpa [LatticeVertexIncidentCell] using hall 0)
    · have hz : z = x - 1 := by calc
        z = (z + 1) - 1 := by abel
        _ = x - 1 := by rw [hxz]
      subst z
      rcases hs with ⟨_, hmiss⟩ | ⟨hmiss, _⟩
      · exact hmiss (by simpa [LatticeVertexIncidentCell, I, sub_eq_add_neg,
          add_assoc, add_comm, add_left_comm] using hall 2)
      · exact hmiss (by simpa [LatticeVertexIncidentCell] using hall 1)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
    rcases hxe with hxz | hxz
    · subst z
      rcases hs with ⟨_, hmiss⟩ | ⟨hmiss, _⟩
      · exact hmiss (by simpa [LatticeVertexIncidentCell] using hall 1)
      · exact hmiss (by simpa [LatticeVertexIncidentCell] using hall 0)
    · have hz : z = x - I := by calc
        z = (z + I) - I := by abel
        _ = x - I := by rw [hxz]
      subst z
      rcases hs with ⟨_, hmiss⟩ | ⟨hmiss, _⟩
      · exact hmiss (by simpa [LatticeVertexIncidentCell, I, sub_eq_add_neg,
          add_assoc, add_comm, add_left_comm] using hall 2)
      · exact hmiss (by simpa [LatticeVertexIncidentCell, I] using hall 3)

private theorem pair_left_mem :
    (by
      classical
      exact
        ∀ {a : GaussianInt}, ∀ {b : GaussianInt}, ∀ {c : GaussianInt}, ∀ {d : GaussianInt}, (({a,
            b} : Finset GaussianInt) = {c, d}) → (a = c ∨ a = d) ) := by
  classical
  intro a b c d h
  have hm : a ∈ ({a, b} : Finset GaussianInt) := by simp
  rw [h] at hm
  simpa using hm

private theorem pair_right_mem :
    (by
      classical
      exact
        ∀ {a : GaussianInt}, ∀ {b : GaussianInt}, ∀ {c : GaussianInt}, ∀ {d : GaussianInt}, (({a,
            b} : Finset GaussianInt) = {c, d}) → (b = c ∨ b = d) ) := by
  classical
  intro a b c d h
  have hm : b ∈ ({a, b} : Finset GaussianInt) := by simp
  rw [h] at hm
  simpa using hm

private theorem star01_ne_12 :
    (by
      classical
      exact
        ∀ (x : GaussianInt),
        let I : GaussianInt := ⟨0, 1⟩
        (∀ {a : GaussianInt}, ∀ {b : GaussianInt}, ∀ {c : GaussianInt}, ∀ {d : GaussianInt},
            (({a, b} : Finset GaussianInt) = {c, d}) → (b = c ∨ b = d)) → (({x, x + I} : Finset
            GaussianInt) ≠ {x - 1, x}) ) := by
  classical
  intro x I pair_right_mem h
  rcases pair_right_mem h with h | h
  · have hs : I = -1 := by calc
      I = (x + I) - x := by abel
      _ = (x - 1) - x := by rw [h]
      _ = -1 := by abel
    norm_num [I, Zsqrtd.ext_iff] at hs
  · have hs : I = 0 := by calc
      I = (x + I) - x := by abel
      _ = x - x := by rw [h]
      _ = 0 := by abel
    norm_num [I, Zsqrtd.ext_iff] at hs

private theorem star01_ne_23 :
    (by
      classical
      exact
        ∀ (x : GaussianInt),
        let I : GaussianInt := ⟨0, 1⟩
        (∀ {a : GaussianInt}, ∀ {b : GaussianInt}, ∀ {c : GaussianInt}, ∀ {d : GaussianInt},
            (({a, b} : Finset GaussianInt) = {c, d}) → (b = c ∨ b = d)) → (({x, x + I} : Finset
            GaussianInt) ≠ {x - I, x}) ) := by
  classical
  intro x I pair_right_mem h
  rcases pair_right_mem h with h | h
  · have hs : I = -I := by calc
      I = (x + I) - x := by abel
      _ = (x - I) - x := by rw [h]
      _ = -I := by abel
    norm_num [I, Zsqrtd.ext_iff] at hs
  · have hs : I = 0 := by calc
      I = (x + I) - x := by abel
      _ = x - x := by rw [h]
      _ = 0 := by abel
    norm_num [I, Zsqrtd.ext_iff] at hs

private theorem star01_ne_30 :
    (by
      classical
      exact
        ∀ (x : GaussianInt),
        let I : GaussianInt := ⟨0, 1⟩
        (∀ {a : GaussianInt}, ∀ {b : GaussianInt}, ∀ {c : GaussianInt}, ∀ {d : GaussianInt},
            (({a, b} : Finset GaussianInt) = {c, d}) → (b = c ∨ b = d)) → (({x, x + I} : Finset
            GaussianInt) ≠ {x, x + 1}) ) := by
  classical
  intro x I pair_right_mem h
  rcases pair_right_mem h with h | h
  · have hs : I = 0 := by calc
      I = (x + I) - x := by abel
      _ = x - x := by rw [h]
      _ = 0 := by abel
    norm_num [I, Zsqrtd.ext_iff] at hs
  · have hs : I = 1 := by calc
      I = (x + I) - x := by abel
      _ = (x + 1) - x := by rw [h]
      _ = 1 := by abel
    norm_num [I, Zsqrtd.ext_iff] at hs

private theorem star12_ne_23 :
    (by
      classical
      exact
        ∀ (x : GaussianInt),
        let I : GaussianInt := ⟨0, 1⟩
        (∀ {a : GaussianInt}, ∀ {b : GaussianInt}, ∀ {c : GaussianInt}, ∀ {d : GaussianInt},
            (({a, b} : Finset GaussianInt) = {c, d}) → (a = c ∨ a = d)) → (({x - 1, x} : Finset
            GaussianInt) ≠ {x - I, x}) ) := by
  classical
  intro x I pair_left_mem h
  rcases pair_left_mem h with h | h
  · have hs : I = 1 := by calc
      I = x - (x - I) := by abel
      _ = x - (x - 1) := by rw [← h]
      _ = 1 := by abel
    norm_num [I, Zsqrtd.ext_iff] at hs
  · have hs : (1 : GaussianInt) = 0 := by calc
      1 = x - (x - 1) := by abel
      _ = x - x := by rw [h]
      _ = 0 := by abel
    norm_num [Zsqrtd.ext_iff] at hs

private theorem star12_ne_30 :
    (by
      classical
      exact
        ∀ (x : GaussianInt), (∀ {a : GaussianInt}, ∀ {b : GaussianInt}, ∀ {c : GaussianInt}, ∀
            {d : GaussianInt}, (({a, b} : Finset GaussianInt) = {c, d}) → (a = c ∨ a = d)) →
            (({x - 1, x} : Finset GaussianInt) ≠ {x, x + 1}) ) := by
  classical
  intro x pair_left_mem h
  rcases pair_left_mem h with h | h
  · have hs : (-1 : GaussianInt) = 0 := by calc
      -1 = (x - 1) - x := by abel
      _ = x - x := by rw [h]
      _ = 0 := by abel
    norm_num [Zsqrtd.ext_iff] at hs
  · have hs : (-1 : GaussianInt) = 1 := by calc
      -1 = (x - 1) - x := by abel
      _ = (x + 1) - x := by rw [h]
      _ = 1 := by abel
    norm_num [Zsqrtd.ext_iff] at hs

private theorem star23_ne_30 :
    (by
      classical
      exact
        ∀ (x : GaussianInt),
        let I : GaussianInt := ⟨0, 1⟩
        (∀ {a : GaussianInt}, ∀ {b : GaussianInt}, ∀ {c : GaussianInt}, ∀ {d : GaussianInt},
            (({a, b} : Finset GaussianInt) = {c, d}) → (a = c ∨ a = d)) → (({x - I, x} : Finset
            GaussianInt) ≠ {x, x + 1}) ) := by
  classical
  intro x I pair_left_mem h
  rcases pair_left_mem h with h | h
  · have hs : I = 0 := by calc
      I = x - (x - I) := by abel
      _ = x - x := by rw [h]
      _ = 0 := by abel
    norm_num [I, Zsqrtd.ext_iff] at hs
  · have hs : I = -1 := by calc
      I = x - (x - I) := by abel
      _ = x - (x + 1) := by rw [h]
      _ = -1 := by abel
    norm_num [I, Zsqrtd.ext_iff] at hs

private theorem adjacent_of_edge :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → (∀ (e :
            Finset GaussianInt), (e ∈ FootprintEdges (cert.modified.tile a)) → ((e ∈
            FootprintEdges (cert.modified.tile b)) → (cert.modified.plane.adjacent a b))) ) := by
  classical
  intro q cfg C T cert a b hne e ha hb
  have hclass := (PeriodicTileIntersectionClassification cert.modified).1 a b hne
  exact hclass.1.mp ⟨e, ha, hb⟩

private theorem adj01 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), ∀ (cells : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T.cells), ∀ (modified_cell_owner : ∀ (c : LatticeCell), (c ∈ T.cells) → (∃ a :
            PeriodicSubtileIndex, a.first = 0 ∧ a.second = 0 ∧ c ∈ (cert.modified.tile a).cells)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun j =>
          Classical.choose (modified_cell_owner (LatticeVertexIncidentCell x j) (cells j))
        let I : GaussianInt := ⟨0, 1⟩
        (∀ (j : Fin 4), (owner j).first = 0 ∧ (owner j).second = 0 ∧ LatticeVertexIncidentCell x
            j ∈ (cert.modified.tile (owner j)).cells) → ((∀ (U : ProtoTile), ∀ (z : GaussianInt),
            (z ∈ U.cells) → ({z, z + I} ∈ FootprintEdges U)) → ((∀ (U : ProtoTile), ∀ (z :
            GaussianInt), (z ∈ U.cells) → ({z + 1, z + 1 + I} ∈ FootprintEdges U)) → ((∀ (a :
            PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → (∀ (e : Finset
            GaussianInt), (e ∈ FootprintEdges (cert.modified.tile a)) → ((e ∈ FootprintEdges
            (cert.modified.tile b)) → (cert.modified.plane.adjacent a b)))) → ((owner 0 ≠ owner
            1) → (cert.modified.plane.adjacent (owner 0) (owner 1)))))) ) := by
  classical
  intro q cfg C T cert x cells modified_cell_owner owner I owner_spec cell_edge_vleft
      cell_edge_vright adjacent_of_edge hne
  apply adjacent_of_edge _ _ hne {x, x + I}
  · exact cell_edge_vleft _ x (by
      simpa [LatticeVertexIncidentCell] using owner_spec 0 |>.2.2)
  · have hbase : LatticeVertexIncidentCell x 1 + 1 = x := by
      simp [LatticeVertexIncidentCell]
    have hz := cell_edge_vright (cert.modified.tile (owner 1))
      (LatticeVertexIncidentCell x 1) (owner_spec 1 |>.2.2)
    simpa [I, hbase, add_assoc, add_comm, add_left_comm] using hz

private theorem adj12 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), ∀ (cells : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T.cells), ∀ (modified_cell_owner : ∀ (c : LatticeCell), (c ∈ T.cells) → (∃ a :
            PeriodicSubtileIndex, a.first = 0 ∧ a.second = 0 ∧ c ∈ (cert.modified.tile a).cells)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun j =>
          Classical.choose (modified_cell_owner (LatticeVertexIncidentCell x j) (cells j))
        let I : GaussianInt := ⟨0, 1⟩
        (∀ (j : Fin 4), (owner j).first = 0 ∧ (owner j).second = 0 ∧ LatticeVertexIncidentCell x
            j ∈ (cert.modified.tile (owner j)).cells) → ((∀ (U : ProtoTile), ∀ (z : GaussianInt),
            (z ∈ U.cells) → ({z, z + 1} ∈ FootprintEdges U)) → ((∀ (U : ProtoTile), ∀ (z :
            GaussianInt), (z ∈ U.cells) → ({z + I, z + 1 + I} ∈ FootprintEdges U)) → ((∀ (a :
            PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → (∀ (e : Finset
            GaussianInt), (e ∈ FootprintEdges (cert.modified.tile a)) → ((e ∈ FootprintEdges
            (cert.modified.tile b)) → (cert.modified.plane.adjacent a b)))) → ((owner 1 ≠ owner
            2) → (cert.modified.plane.adjacent (owner 1) (owner 2)))))) ) := by
  classical
  intro q cfg C T cert x cells modified_cell_owner owner I owner_spec cell_edge_hbottom
      cell_edge_htop adjacent_of_edge hne
  apply adjacent_of_edge _ _ hne {x - 1, x}
  · have hbase : LatticeVertexIncidentCell x 1 = x - 1 := by
      simp [LatticeVertexIncidentCell]
    simpa [hbase] using cell_edge_hbottom _ _ (owner_spec 1 |>.2.2)
  · have hbase : LatticeVertexIncidentCell x 2 + I = x - 1 := by
      simp [LatticeVertexIncidentCell, I, sub_eq_add_neg, add_assoc,
        add_comm, add_left_comm]
    have hz := cell_edge_htop (cert.modified.tile (owner 2))
      (LatticeVertexIncidentCell x 2) (owner_spec 2 |>.2.2)
    simpa [I, hbase, add_assoc, add_comm, add_left_comm] using hz

private theorem adj23 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), ∀ (cells : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T.cells), ∀ (modified_cell_owner : ∀ (c : LatticeCell), (c ∈ T.cells) → (∃ a :
            PeriodicSubtileIndex, a.first = 0 ∧ a.second = 0 ∧ c ∈ (cert.modified.tile a).cells)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun j =>
          Classical.choose (modified_cell_owner (LatticeVertexIncidentCell x j) (cells j))
        let I : GaussianInt := ⟨0, 1⟩
        (∀ (j : Fin 4), (owner j).first = 0 ∧ (owner j).second = 0 ∧ LatticeVertexIncidentCell x
            j ∈ (cert.modified.tile (owner j)).cells) → ((∀ (U : ProtoTile), ∀ (z : GaussianInt),
            (z ∈ U.cells) → ({z, z + I} ∈ FootprintEdges U)) → ((∀ (U : ProtoTile), ∀ (z :
            GaussianInt), (z ∈ U.cells) → ({z + 1, z + 1 + I} ∈ FootprintEdges U)) → ((∀ (a :
            PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → (∀ (e : Finset
            GaussianInt), (e ∈ FootprintEdges (cert.modified.tile a)) → ((e ∈ FootprintEdges
            (cert.modified.tile b)) → (cert.modified.plane.adjacent a b)))) → ((owner 2 ≠ owner
            3) → (cert.modified.plane.adjacent (owner 2) (owner 3)))))) ) := by
  classical
  intro q cfg C T cert x cells modified_cell_owner owner I owner_spec cell_edge_vleft
      cell_edge_vright adjacent_of_edge hne
  apply adjacent_of_edge _ _ hne {x - I, x}
  · have hbase : LatticeVertexIncidentCell x 2 + 1 = x - I := by
      simp [LatticeVertexIncidentCell, I, sub_eq_add_neg, add_assoc,
        add_comm, add_left_comm]
    have hz := cell_edge_vright (cert.modified.tile (owner 2))
      (LatticeVertexIncidentCell x 2) (owner_spec 2 |>.2.2)
    simpa [I, hbase, add_assoc, add_comm, add_left_comm] using hz
  · have hbase : LatticeVertexIncidentCell x 3 = x - I := by
      simp [LatticeVertexIncidentCell, I]
    simpa [hbase] using cell_edge_vleft _ _ (owner_spec 3 |>.2.2)

private theorem adj30 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), ∀ (cells : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T.cells), ∀ (modified_cell_owner : ∀ (c : LatticeCell), (c ∈ T.cells) → (∃ a :
            PeriodicSubtileIndex, a.first = 0 ∧ a.second = 0 ∧ c ∈ (cert.modified.tile a).cells)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun j =>
          Classical.choose (modified_cell_owner (LatticeVertexIncidentCell x j) (cells j))
        let I : GaussianInt := ⟨0, 1⟩
        (∀ (j : Fin 4), (owner j).first = 0 ∧ (owner j).second = 0 ∧ LatticeVertexIncidentCell x
            j ∈ (cert.modified.tile (owner j)).cells) → ((∀ (U : ProtoTile), ∀ (z : GaussianInt),
            (z ∈ U.cells) → ({z, z + 1} ∈ FootprintEdges U)) → ((∀ (U : ProtoTile), ∀ (z :
            GaussianInt), (z ∈ U.cells) → ({z + I, z + 1 + I} ∈ FootprintEdges U)) → ((∀ (a :
            PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → (∀ (e : Finset
            GaussianInt), (e ∈ FootprintEdges (cert.modified.tile a)) → ((e ∈ FootprintEdges
            (cert.modified.tile b)) → (cert.modified.plane.adjacent a b)))) → ((owner 3 ≠ owner
            0) → (cert.modified.plane.adjacent (owner 3) (owner 0)))))) ) := by
  classical
  intro q cfg C T cert x cells modified_cell_owner owner I owner_spec cell_edge_hbottom
      cell_edge_htop adjacent_of_edge hne
  apply adjacent_of_edge _ _ hne {x, x + 1}
  · have hbase : LatticeVertexIncidentCell x 3 + I = x := by
      simp [LatticeVertexIncidentCell, I]
    have hz := cell_edge_htop (cert.modified.tile (owner 3))
      (LatticeVertexIncidentCell x 3) (owner_spec 3 |>.2.2)
    simpa [I, hbase, add_assoc, add_comm, add_left_comm] using hz
  · exact cell_edge_hbottom _ x (by
      simpa [LatticeVertexIncidentCell] using owner_spec 0 |>.2.2)

private theorem chord_of_four_distinct :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), ∀ (cells : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T.cells), ∀ (modified_cell_owner : ∀ (c : LatticeCell), (c ∈ T.cells) → (∃ a :
            PeriodicSubtileIndex, a.first = 0 ∧ a.second = 0 ∧ c ∈ (cert.modified.tile a).cells)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun j =>
          Classical.choose (modified_cell_owner (LatticeVertexIncidentCell x j) (cells j))
        (∀ (j : Fin 4), (owner j).first = 0 ∧ (owner j).second = 0 ∧ LatticeVertexIncidentCell x
            j ∈ (cert.modified.tile (owner j)).cells) → (((owner 0 ≠ owner 1) →
            (cert.modified.plane.adjacent (owner 0) (owner 1))) → (((owner 1 ≠ owner 2) →
            (cert.modified.plane.adjacent (owner 1) (owner 2))) → (((owner 2 ≠ owner 3) →
            (cert.modified.plane.adjacent (owner 2) (owner 3))) → (((owner 3 ≠ owner 0) →
            (cert.modified.plane.adjacent (owner 3) (owner 0))) → ((Function.Injective owner) →
            (AllowedSubtileIncidence (owner 0) (owner 2) ∨ AllowedSubtileIncidence (owner 1)
            (owner 3))))))) ) := by
  classical
  intro q cfg C T cert x cells modified_cell_owner owner owner_spec adj01 adj12 adj23 adj30 hinj
  have own_ne {i j : Fin 4} (hij : i ≠ j) : owner i ≠ owner j := by
    intro he
    exact hij (hinj he)
  have hab := (cert.modified_adjacency (owner 0) (owner 1)).mp
    (adj01 (own_ne (by decide)))
  have hbc := (cert.modified_adjacency (owner 1) (owner 2)).mp
    (adj12 (own_ne (by decide)))
  have hcd := (cert.modified_adjacency (owner 2) (owner 3)).mp
    (adj23 (own_ne (by decide)))
  have hda := (cert.modified_adjacency (owner 3) (owner 0)).mp
    (adj30 (own_ne (by decide)))
  exact AllowedSubtileIncidenceZeroOppositeChord
    (owner 0) (owner 1) (owner 2) (owner 3)
    ⟨owner_spec 0 |>.1, owner_spec 0 |>.2.1⟩
    ⟨owner_spec 2 |>.1, owner_spec 2 |>.2.1⟩
    hab hbc hcd hda
    (own_ne (by decide)) (own_ne (by decide)) (own_ne (by decide))
    (own_ne (by decide)) (own_ne (by decide)) (own_ne (by decide))

private theorem four_distinct_impossible :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), ∀ (cells : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T.cells), ∀ (modified_cell_owner : ∀ (c : LatticeCell), (c ∈ T.cells) → (∃ a :
            PeriodicSubtileIndex, a.first = 0 ∧ a.second = 0 ∧ c ∈ (cert.modified.tile a).cells)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun j =>
          Classical.choose (modified_cell_owner (LatticeVertexIncidentCell x j) (cells j))
        let I : GaussianInt := ⟨0, 1⟩
        (∀ (j : Fin 4), (owner j).first = 0 ∧ (owner j).second = 0 ∧ LatticeVertexIncidentCell x
            j ∈ (cert.modified.tile (owner j)).cells) → ((∀ (j : Fin 4), ∀ (U : ProtoTile),
            (LatticeVertexIncidentCell x j ∈ U.cells) → (x ∈ FootprintVertices U)) → ((∀ (c :
            LatticeCell), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (c ∈
            (cert.modified.tile a).cells) → ((c ∈ (cert.modified.tile b).cells) → (a = b))) → ((∀
            (U : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ FootprintEdges U) → ((x ∈ e) → (∃ j
            : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells ∧ ((e = {x, x + I} ∧ (j = 0 ∨ j =
            1)) ∨ (e = {x - 1, x} ∧ (j = 1 ∨ j = 2)) ∨ (e = {x - I, x} ∧ (j = 2 ∨ j = 3)) ∨ (e =
            {x, x + 1} ∧ (j = 3 ∨ j = 0)))))) → ((({x, x + I} : Finset GaussianInt) ≠ {x - 1, x})
            → ((({x, x + I} : Finset GaussianInt) ≠ {x - I, x}) → ((({x, x + I} : Finset
            GaussianInt) ≠ {x, x + 1}) → ((({x - 1, x} : Finset GaussianInt) ≠ {x - I, x}) →
            ((({x - 1, x} : Finset GaussianInt) ≠ {x, x + 1}) → ((({x - I, x} : Finset
            GaussianInt) ≠ {x, x + 1}) → (((Function.Injective owner) → (AllowedSubtileIncidence
            (owner 0) (owner 2) ∨ AllowedSubtileIncidence (owner 1) (owner 3))) →
            ((Function.Injective owner) → (False)))))))))))) ) := by
  classical
  intro q cfg C T cert x cells modified_cell_owner owner I owner_spec incident_footprint
      owner_unique edge_support star01_ne_12 star01_ne_23 star01_ne_30 star12_ne_23 star12_ne_30
      star23_ne_30 chord_of_four_distinct hinj
  have own_ne {i j : Fin 4} (hij : i ≠ j) : owner i ≠ owner j := by
    intro he
    exact hij (hinj he)
  rcases chord_of_four_distinct hinj with hac | hbd
  · have hadj := (cert.modified_adjacency (owner 0) (owner 2)).mpr hac
    have hclass := (PeriodicTileIntersectionClassification cert.modified).1
      (owner 0) (owner 2) (own_ne (by decide))
    have hedge := hclass.1.mpr hadj
    have hvertices : x ∈ FootprintVertices (cert.modified.tile (owner 0)) ∩
        FootprintVertices (cert.modified.tile (owner 2)) :=
      ⟨incident_footprint 0 _ (owner_spec 0 |>.2.2),
        incident_footprint 2 _ (owner_spec 2 |>.2.2)⟩
    have hcommon : x ∈ CommonFootprintEdgeVertices
        (cert.modified.tile (owner 0)) (cert.modified.tile (owner 2)) := by
      have heq := (hclass.2.1 hedge).2
      rw [heq] at hvertices
      exact hvertices
    rcases hcommon with ⟨e, he, hxedge⟩
    rcases he with ⟨hea, hec⟩
    obtain ⟨j, hj, hkind⟩ := edge_support _ e hea hxedge
    have howner : owner j = owner 0 :=
      owner_unique (LatticeVertexIncidentCell x j) (owner j) (owner 0)
        (owner_spec j |>.2.2) (by simpa using hj)
    have hj0 : j = 0 := hinj howner
    subst j
    have hleft : e = {x, x + I} ∨ e = {x, x + 1} := by
      rcases hkind with h01 | h12 | h23 | h30
      · exact Or.inl h01.1
      · rcases h12.2 with h | h
        · exact False.elim ((by decide : (0 : Fin 4) ≠ 1) h)
        · exact False.elim ((by decide : (0 : Fin 4) ≠ 2) h)
      · rcases h23.2 with h | h
        · exact False.elim ((by decide : (0 : Fin 4) ≠ 2) h)
        · exact False.elim ((by decide : (0 : Fin 4) ≠ 3) h)
      · exact Or.inr h30.1
    obtain ⟨j, hj, hkind⟩ := edge_support _ e hec hxedge
    have howner : owner j = owner 2 :=
      owner_unique (LatticeVertexIncidentCell x j) (owner j) (owner 2)
        (owner_spec j |>.2.2) (by simpa using hj)
    have hj2 : j = 2 := hinj howner
    subst j
    have hright : e = {x - 1, x} ∨ e = {x - I, x} := by
      rcases hkind with h01 | h12 | h23 | h30
      · rcases h01.2 with h | h
        · exact False.elim ((by decide : (2 : Fin 4) ≠ 0) h)
        · exact False.elim ((by decide : (2 : Fin 4) ≠ 1) h)
      · exact Or.inl h12.1
      · exact Or.inr h23.1
      · rcases h30.2 with h | h
        · exact False.elim ((by decide : (2 : Fin 4) ≠ 3) h)
        · exact False.elim ((by decide : (2 : Fin 4) ≠ 0) h)
    rcases hleft with hl | hl <;> rcases hright with hr | hr
    · exact star01_ne_12 (hl.symm.trans hr)
    · exact star01_ne_23 (hl.symm.trans hr)
    · exact star12_ne_30 (hr.symm.trans hl)
    · exact star23_ne_30 (hr.symm.trans hl)
  · have hadj := (cert.modified_adjacency (owner 1) (owner 3)).mpr hbd
    have hclass := (PeriodicTileIntersectionClassification cert.modified).1
      (owner 1) (owner 3) (own_ne (by decide))
    have hedge := hclass.1.mpr hadj
    have hvertices : x ∈ FootprintVertices (cert.modified.tile (owner 1)) ∩
        FootprintVertices (cert.modified.tile (owner 3)) :=
      ⟨incident_footprint 1 _ (owner_spec 1 |>.2.2),
        incident_footprint 3 _ (owner_spec 3 |>.2.2)⟩
    have hcommon : x ∈ CommonFootprintEdgeVertices
        (cert.modified.tile (owner 1)) (cert.modified.tile (owner 3)) := by
      have heq := (hclass.2.1 hedge).2
      rw [heq] at hvertices
      exact hvertices
    rcases hcommon with ⟨e, he, hxedge⟩
    rcases he with ⟨hea, hec⟩
    obtain ⟨j, hj, hkind⟩ := edge_support _ e hea hxedge
    have howner : owner j = owner 1 :=
      owner_unique (LatticeVertexIncidentCell x j) (owner j) (owner 1)
        (owner_spec j |>.2.2) (by simpa using hj)
    have hj1 : j = 1 := hinj howner
    subst j
    have hleft : e = {x, x + I} ∨ e = {x - 1, x} := by
      rcases hkind with h01 | h12 | h23 | h30
      · exact Or.inl h01.1
      · exact Or.inr h12.1
      · rcases h23.2 with h | h
        · exact False.elim ((by decide : (1 : Fin 4) ≠ 2) h)
        · exact False.elim ((by decide : (1 : Fin 4) ≠ 3) h)
      · rcases h30.2 with h | h
        · exact False.elim ((by decide : (1 : Fin 4) ≠ 3) h)
        · exact False.elim ((by decide : (1 : Fin 4) ≠ 0) h)
    obtain ⟨j, hj, hkind⟩ := edge_support _ e hec hxedge
    have howner : owner j = owner 3 :=
      owner_unique (LatticeVertexIncidentCell x j) (owner j) (owner 3)
        (owner_spec j |>.2.2) (by simpa using hj)
    have hj3 : j = 3 := hinj howner
    subst j
    have hright : e = {x - I, x} ∨ e = {x, x + 1} := by
      rcases hkind with h01 | h12 | h23 | h30
      · rcases h01.2 with h | h
        · exact False.elim ((by decide : (3 : Fin 4) ≠ 0) h)
        · exact False.elim ((by decide : (3 : Fin 4) ≠ 1) h)
      · rcases h12.2 with h | h
        · exact False.elim ((by decide : (3 : Fin 4) ≠ 1) h)
        · exact False.elim ((by decide : (3 : Fin 4) ≠ 2) h)
      · exact Or.inl h23.1
      · exact Or.inr h30.1
    rcases hleft with hl | hl <;> rcases hright with hr | hr
    · exact star01_ne_23 (hl.symm.trans hr)
    · exact star01_ne_30 (hl.symm.trans hr)
    · exact star12_ne_23 (hl.symm.trans hr)
    · exact star12_ne_30 (hl.symm.trans hr)

private theorem modifiedOwnerCard :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), ∀ (cells : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T.cells), ∀ (modified_cell_owner : ∀ (c : LatticeCell), (c ∈ T.cells) → (∃ a :
            PeriodicSubtileIndex, a.first = 0 ∧ a.second = 0 ∧ c ∈ (cert.modified.tile a).cells)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun j =>
          Classical.choose (modified_cell_owner (LatticeVertexIncidentCell x j) (cells j))
        ((Function.Injective owner) → (False)) → (
        let modifiedOwners : Finset PeriodicSubtileIndex := Finset.univ.image owner
        modifiedOwners.card ≤ 3) ) := by
  classical
  intro q cfg C T cert x cells modified_cell_owner owner four_distinct_impossible modifiedOwners
  have hle : modifiedOwners.card ≤ 4 := by
    calc
      modifiedOwners.card ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
      _ = 4 := by simp
  have hneq : modifiedOwners.card ≠ 4 := by
    intro hcard
    have hinjOn : Set.InjOn owner (Finset.univ : Finset (Fin 4)) := by
      apply (Finset.card_image_iff).mp
      simpa [modifiedOwners] using hcard
    have hinj : Function.Injective owner := by
      intro i j hij
      exact hinjOn (by simp) (by simp) hij
    exact four_distinct_impossible hinj
  omega

private theorem hnoInterior :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), (∀ i : Fin 3, Bool → 0 < (q i.succ).1) → ((¬∃ (i : Fin
            (3 : ℕ)) (s : Bool), (0 : ℤ) < (q i.succ).1 ∧ x ∈ FootprintVertices (cert.P i s) ∧ x
            ∉ BoundaryFootprintVertices (cert.P i s)) → (∀ (i : Fin 3), ∀ (s : Bool), (x ∈
            FootprintVertices (cert.P i s)) → (x ∈ BoundaryFootprintVertices (cert.P i s)))) ) := by
  classical
  intro q cfg C T cert x hpos hnoWitness i s hfoot
  by_contra hnotbound
  exact hnoWitness ⟨i, s, hpos i s, hfoot, hnotbound⟩

private theorem another_parent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), (∀ (U : ProtoTile), (∀ j : Fin 4, LatticeVertexIncidentCell
            x j ∈ U.cells) → ((x ∈ BoundaryFootprintVertices U) → (False))) → (∀ (sourceParent :
            ∀ (j : Fin 4), ∃ i : Fin 3, ∃ s : Bool, LatticeVertexIncidentCell x j ∈ (cert.P i
            s).cells),
        let parentOwner : Fin 4 → Fin 3 × Bool := fun j =>
          (Classical.choose (sourceParent j),
            Classical.choose (Classical.choose_spec (sourceParent j)))
        (∀ (j : Fin 4), LatticeVertexIncidentCell x j ∈ (cert.P (parentOwner j).1 (parentOwner
            j).2).cells) → ((∀ (j : Fin 4), x ∈ BoundaryFootprintVertices (cert.P (parentOwner
            j).1 (parentOwner j).2)) → (∃ j : Fin 4, parentOwner j ≠ parentOwner 0))) ) := by
  classical
  intro q cfg C T cert x all_incident_not_boundary sourceParent parentOwner parentOwner_spec
      parentOwner_boundary
  by_contra h
  push Not at h
  have hall : ∀ j : Fin 4,
      LatticeVertexIncidentCell x j ∈
        (cert.P (parentOwner 0).1 (parentOwner 0).2).cells := by
    intro j
    simpa [h j] using parentOwner_spec j
  exact all_incident_not_boundary
    (cert.P (parentOwner 0).1 (parentOwner 0).2) hall (parentOwner_boundary 0)

private theorem hp0j :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), ∀ (sourceParent : ∀ (j : Fin 4), ∃ i : Fin 3, ∃ s : Bool,
            LatticeVertexIncidentCell x j ∈ (cert.P i s).cells),
        let parentOwner : Fin 4 → Fin 3 × Bool := fun j =>
          (Classical.choose (sourceParent j),
            Classical.choose (Classical.choose_spec (sourceParent j)))
        ∀ (parentOwner_boundary : ∀ (j : Fin 4), x ∈ BoundaryFootprintVertices (cert.P
            (parentOwner j).1 (parentOwner j).2)), ∀ (j : Fin (4 : ℕ)), (parentOwner j ≠
            parentOwner (0 : Fin (4 : ℕ))) → (
        let BoundaryParents := {a : Fin 3 × Bool //
          x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)}
        let p0 : BoundaryParents := ⟨parentOwner 0, parentOwner_boundary 0⟩
        let pj : BoundaryParents := ⟨parentOwner j, parentOwner_boundary j⟩
        p0 ≠ pj) ) := by
  classical
  intro q cfg C T cert x sourceParent parentOwner parentOwner_boundary j hj BoundaryParents p0 pj h
  exact hj (congrArg Subtype.val h).symm

private theorem chooseTwo_injective :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), ∀ (sourceParent : ∀ (j : Fin 4), ∃ i : Fin 3, ∃ s : Bool,
            LatticeVertexIncidentCell x j ∈ (cert.P i s).cells),
        let parentOwner : Fin 4 → Fin 3 × Bool := fun j =>
          (Classical.choose (sourceParent j),
            Classical.choose (Classical.choose_spec (sourceParent j)))
        ∀ (parentOwner_boundary : ∀ (j : Fin 4), x ∈ BoundaryFootprintVertices (cert.P
            (parentOwner j).1 (parentOwner j).2)), ∀ (j : Fin (4 : ℕ)),
        let BoundaryParents := {a : Fin 3 × Bool //
          x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)}
        let p0 : BoundaryParents := ⟨parentOwner 0, parentOwner_boundary 0⟩
        let pj : BoundaryParents := ⟨parentOwner j, parentOwner_boundary j⟩
        (p0 ≠ pj) → (
        let chooseTwo : Fin 2 → BoundaryParents := fun n => if n = 0 then p0 else pj
        Function.Injective chooseTwo) ) := by
  classical
  intro q cfg C T cert x sourceParent parentOwner parentOwner_boundary j BoundaryParents p0 pj
      hp0j chooseTwo m n h
  fin_cases m <;> fin_cases n
  · rfl
  · have heq : p0 = pj := by simpa [chooseTwo] using h
    exact (hp0j heq).elim
  · have heq : pj = p0 := by simpa [chooseTwo] using h
    exact (hp0j heq.symm).elim
  · rfl

private theorem two_le_card :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), ∀ (sourceParent : ∀ (j : Fin 4), ∃ i : Fin 3, ∃ s : Bool,
            LatticeVertexIncidentCell x j ∈ (cert.P i s).cells),
        let parentOwner : Fin 4 → Fin 3 × Bool := fun j =>
          (Classical.choose (sourceParent j),
            Classical.choose (Classical.choose_spec (sourceParent j)))
        ∀ (parentOwner_boundary : ∀ (j : Fin 4), x ∈ BoundaryFootprintVertices (cert.P
            (parentOwner j).1 (parentOwner j).2)), ∀ (j : Fin (4 : ℕ)),
        let BoundaryParents := {a : Fin 3 × Bool //
          x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)}
        let p0 : BoundaryParents := ⟨parentOwner 0, parentOwner_boundary 0⟩
        let pj : BoundaryParents := ⟨parentOwner j, parentOwner_boundary j⟩
        let chooseTwo : Fin 2 → BoundaryParents := fun n => if n = 0 then p0 else pj
        (Function.Injective chooseTwo) → (2 ≤ Nat.card BoundaryParents) ) := by
  classical
  intro q cfg C T cert x sourceParent parentOwner parentOwner_boundary j BoundaryParents p0 pj
      chooseTwo chooseTwo_injective
  have hcard := Fintype.card_le_of_injective chooseTwo chooseTwo_injective
  simpa [BoundaryParents] using hcard

private theorem hOA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), cert.O.cells ⊆ (cert.P 0 true).cells ) := by
  classical
  intro q cfg C T cert c hc
  rw [cert.precursor_eq] at hc
  exact (cert.plus_union c).mpr ⟨0, false, hc⟩

private theorem modified_cell_parent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let parentOfLabel : SixSubtileLabel → Fin 3 × Bool := fun
          | .A => (0, true)
          | .B => (0, false)
          | .C => (1, true)
          | .D => (1, false)
          | .E => (2, true)
          | .F => (2, false)
        ∀ (m : PeriodicSubtileIndex), (m.first = 0) → ((m.second = 0) → (∀ (c : GaussianInt), (c
            ∈ (cert.modified.tile m).cells) → (c ∈ (cert.P (parentOfLabel m.label).1
            (parentOfLabel m.label).2).cells ∧ (m.label = .A → c ∉ cert.O.cells)))) ) := by
  classical
  intro q cfg C T cert parentOfLabel m hm1 hm2 c hcell
  rcases m with ⟨l, r, t⟩
  have hr : r = 0 := hm1
  have ht : t = 0 := hm2
  subst r
  subst t
  rw [cert.modified_tile] at hcell
  cases l <;>
    simpa [parentOfLabel, ModifiedSubtileOccurrenceInterpretation,
      TileTranslation, GaussianTranslation, TileCellComplement] using hcell

private theorem parent_label_roundtrip :
    (by
      classical
      exact
        let parentOfLabel : SixSubtileLabel → Fin 3 × Bool := fun
          | .A => (0, true)
          | .B => (0, false)
          | .C => (1, true)
          | .D => (1, false)
          | .E => (2, true)
          | .F => (2, false)
        let labelFromParent : Fin 3 × Bool → SixSubtileLabel := fun
          | (0, true) => .A
          | (0, false) => .B
          | (1, true) => .C
          | (1, false) => .D
          | (2, true) => .E
          | (2, false) => .F
        ∀ (p : Fin 3 × Bool), parentOfLabel (labelFromParent p) = p ) := by
  classical
  intro parentOfLabel labelFromParent p
  rcases p with ⟨pi, ps⟩
  fin_cases pi <;> cases ps <;> rfl

private theorem labelFromParent_injective :
    (by
      classical
      exact
        let parentOfLabel : SixSubtileLabel → Fin 3 × Bool := fun
          | .A => (0, true)
          | .B => (0, false)
          | .C => (1, true)
          | .D => (1, false)
          | .E => (2, true)
          | .F => (2, false)
        let labelFromParent : Fin 3 × Bool → SixSubtileLabel := fun
          | (0, true) => .A
          | (0, false) => .B
          | (1, true) => .C
          | (1, false) => .D
          | (2, true) => .E
          | (2, false) => .F
        (∀ (p : Fin 3 × Bool), parentOfLabel (labelFromParent p) = p) → (Function.Injective
            labelFromParent) ) := by
  classical
  intro parentOfLabel labelFromParent parent_label_roundtrip p q hpq
  calc
    p = parentOfLabel (labelFromParent p) := (parent_label_roundtrip p).symm
    _ = parentOfLabel (labelFromParent q) := congrArg parentOfLabel hpq
    _ = q := parent_label_roundtrip q

private theorem originalIndex_parent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (∀ (U : ProtoTile), TileTranslation U 0 = U) → (
        let labelFromParent : Fin 3 × Bool → SixSubtileLabel := fun
          | (0, true) => .A
          | (0, false) => .B
          | (1, true) => .C
          | (1, false) => .D
          | (2, true) => .E
          | (2, false) => .F
        let originalIndex : Fin 3 × Bool → PeriodicSubtileIndex := fun p =>
          ⟨labelFromParent p, 0, 0⟩
        ∀ (p : Fin 3 × Bool), SubtileOccurrenceInterpretation cert.P cert.u cert.v (originalIndex
            p) = cert.P p.1 p.2) ) := by
  classical
  intro q cfg C T cert tile_zero labelFromParent originalIndex p
  rcases p with ⟨pi, ps⟩
  have hz := tile_zero (cert.P pi ps)
  fin_cases pi <;> cases ps <;>
    simpa [originalIndex, labelFromParent,
      SubtileOccurrenceInterpretation] using hz

private theorem original_disjoint :
    (by
      classical
      exact
        ∀ (quadruple : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration
            quadruple), ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀
            (cert : BandOrderedGeneralLayoutCertificate quadruple cfg C T), ((∀ (m : ℤ), ∀ (n : ℤ),
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v (⟨SixSubtileLabel.A, m, n⟩ :
            PeriodicSubtileIndex)).cells ∩ (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (⟨SixSubtileLabel.B, m, n⟩ : PeriodicSubtileIndex)).cells = (TileTranslation cert.O
            ((↑m : GaussianInt) * cert.u + (↑n : GaussianInt) * cert.v)).cells) ∧ ∀ (a :
            PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), a ≠ b → ¬((a.label =
            SixSubtileLabel.A ∧ b.label = SixSubtileLabel.B ∨ a.label = SixSubtileLabel.B ∧
            b.label = SixSubtileLabel.A) ∧ a.first = b.first ∧ a.second = b.second) → Disjoint
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v a).cells
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v b).cells) → (
        let parentOfLabel : SixSubtileLabel → Fin 3 × Bool := fun
          | .A => (0, true)
          | .B => (0, false)
          | .C => (1, true)
          | .D => (1, false)
          | .E => (2, true)
          | .F => (2, false)
        let labelFromParent : Fin 3 × Bool → SixSubtileLabel := fun
          | (0, true) => .A
          | (0, false) => .B
          | (1, true) => .C
          | (1, false) => .D
          | (2, true) => .E
          | (2, false) => .F
        let originalIndex : Fin 3 × Bool → PeriodicSubtileIndex := fun p =>
          ⟨labelFromParent p, 0, 0⟩
        (∀ (p : Fin 3 × Bool), parentOfLabel (labelFromParent p) = p) → ((Function.Injective
            labelFromParent) → ((∀ (p : Fin 3 × Bool), SubtileOccurrenceInterpretation cert.P
            cert.u cert.v (originalIndex p) = cert.P p.1 p.2) → (∀ (p : Fin 3 × Bool), ∀ (q : Fin
            3 × Bool), (p ≠ q) → ((¬ (p = (0, true) ∧ q = (0, false) ∨
            p = (0, false) ∧ q = (0, true))) → (Disjoint (cert.P p.1 p.2).cells (cert.P q.1
                q.2).cells)))))) ) := by
  classical
  intro quadruple cfg C T cert hseparation parentOfLabel labelFromParent originalIndex
      parent_label_roundtrip labelFromParent_injective originalIndex_parent p q hpq hexception
  have hidx : originalIndex p ≠ originalIndex q := by
    intro heq
    apply hpq
    apply labelFromParent_injective
    simpa [originalIndex] using congrArg PeriodicSubtileIndex.label heq
  have hnot : ¬(((originalIndex p).label = .A ∧
      (originalIndex q).label = .B ∨
    (originalIndex p).label = .B ∧ (originalIndex q).label = .A) ∧
      (originalIndex p).first = (originalIndex q).first ∧
      (originalIndex p).second = (originalIndex q).second) := by
    intro hbad
    apply hexception
    rcases hbad with ⟨hlabels, _, _⟩
    rcases hlabels with hbad | hbad
    · have hp : p = (0, true) := by
        calc
          p = parentOfLabel (labelFromParent p) := (parent_label_roundtrip p).symm
          _ = (0, true) := by simpa using congrArg parentOfLabel (by
            simpa [originalIndex] using hbad.1)
      have hq : q = (0, false) := by
        calc
          q = parentOfLabel (labelFromParent q) := (parent_label_roundtrip q).symm
          _ = (0, false) := by simpa using congrArg parentOfLabel (by
            simpa [originalIndex] using hbad.2)
      exact Or.inl ⟨hp, hq⟩
    · have hp : p = (0, false) := by
        calc
          p = parentOfLabel (labelFromParent p) := (parent_label_roundtrip p).symm
          _ = (0, false) := by simpa using congrArg parentOfLabel (by
            simpa [originalIndex] using hbad.1)
      have hq : q = (0, true) := by
        calc
          q = parentOfLabel (labelFromParent q) := (parent_label_roundtrip q).symm
          _ = (0, true) := by simpa using congrArg parentOfLabel (by
            simpa [originalIndex] using hbad.2)
      exact Or.inr ⟨hp, hq⟩
  have hdisj := hseparation.2 (originalIndex p) (originalIndex q) hidx
    hnot
  rw [originalIndex_parent p, originalIndex_parent q] at hdisj
  exact hdisj

private theorem htrans :
    (by
      classical
      exact
        GaussianTranslation 0 = id ) := by
  classical
  funext z
  simp [GaussianTranslation]

private theorem hAB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ((∀ (m : ℤ), ∀ (n : ℤ), (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (⟨SixSubtileLabel.A, m, n⟩ : PeriodicSubtileIndex)).cells ∩
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v (⟨SixSubtileLabel.B, m, n⟩ :
            PeriodicSubtileIndex)).cells = (TileTranslation cert.O ((↑m : GaussianInt) * cert.u +
            (↑n : GaussianInt) * cert.v)).cells) ∧ ∀ (a : PeriodicSubtileIndex), ∀ (b :
            PeriodicSubtileIndex), a ≠ b → ¬((a.label = SixSubtileLabel.A ∧ b.label =
            SixSubtileLabel.B ∨ a.label = SixSubtileLabel.B ∧ b.label = SixSubtileLabel.A) ∧
            a.first = b.first ∧ a.second = b.second) → Disjoint (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v a).cells (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            b).cells) → ((GaussianTranslation 0 = id) → ((cert.P 0 true).cells ∩ (cert.P 0
            false).cells = cert.O.cells)) ) := by
  classical
  intro q cfg C T cert hseparation htrans
  simpa [SubtileOccurrenceInterpretation, TileTranslation, htrans] using
    hseparation.1 (0 : ℤ) 0

private theorem parent_matches_owner :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), ∀ (cells : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T.cells), ∀ (modified_cell_owner : ∀ (c : LatticeCell), (c ∈ T.cells) → (∃ a :
            PeriodicSubtileIndex, a.first = 0 ∧ a.second = 0 ∧ c ∈ (cert.modified.tile a).cells)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun j =>
          Classical.choose (modified_cell_owner (LatticeVertexIncidentCell x j) (cells j))
        (∀ (j : Fin 4), (owner j).first = 0 ∧ (owner j).second = 0 ∧ LatticeVertexIncidentCell x
            j ∈ (cert.modified.tile (owner j)).cells) → (∀ (parent_boundary_incident_cell : ∀ (i
            : Fin 3), ∀ (s : Bool), (x ∈ BoundaryFootprintVertices (cert.P i s)) → (∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ (cert.P i s).cells)),
        let BoundaryParents := {a : Fin 3 × Bool //
          x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)}
        let parentOfLabel : SixSubtileLabel → Fin 3 × Bool := fun
          | .A => (0, true)
          | .B => (0, false)
          | .C => (1, true)
          | .D => (1, false)
          | .E => (2, true)
          | .F => (2, false)
        (∀ (m : PeriodicSubtileIndex), (m.first = 0) → ((m.second = 0) → (∀ (c : GaussianInt), (c
            ∈ (cert.modified.tile m).cells) → (c ∈ (cert.P (parentOfLabel m.label).1
            (parentOfLabel m.label).2).cells ∧ (m.label = .A → c ∉ cert.O.cells))))) → ((∀ (p :
            Fin 3 × Bool), ∀ (q : Fin 3 × Bool), (p ≠ q) → ((¬ (p = (0, true) ∧ q = (0, false) ∨
            p = (0, false) ∧ q = (0, true))) → (Disjoint (cert.P p.1 p.2).cells (cert.P q.1
            q.2).cells))) → (((cert.P 0 true).cells ∩ (cert.P 0 false).cells = cert.O.cells) → (
        let parentCellIndex : BoundaryParents → Fin 4 := fun p =>
          Classical.choose (parent_boundary_incident_cell p.1.1 p.1.2 p.2)
        (∀ (p : BoundaryParents), LatticeVertexIncidentCell x (parentCellIndex p) ∈ (cert.P p.1.1
            p.1.2).cells) → (∀ (p : BoundaryParents), (p.1 ≠ (0, true)) → (p.1 = parentOfLabel
            (owner (parentCellIndex p)).label)))))) ) := by
  classical
  intro q cfg C T cert x cells modified_cell_owner owner owner_spec parent_boundary_incident_cell
      BoundaryParents parentOfLabel modified_cell_parent original_disjoint hAB parentCellIndex
      parentCellIndex_spec p hp
  let j := parentCellIndex p
  let c := LatticeVertexIncidentCell x j
  have hcP : c ∈ (cert.P p.1.1 p.1.2).cells := parentCellIndex_spec p
  have hcM : c ∈ (cert.modified.tile (owner j)).cells := (owner_spec j).2.2
  have hm := modified_cell_parent (owner j) (owner_spec j).1
    (owner_spec j).2.1 c hcM
  let r := parentOfLabel (owner j).label
  by_cases hpr : p.1 = r
  · exact hpr
  · have hexception : ¬ (p.1 = (0, true) ∧ r = (0, false) ∨
        p.1 = (0, false) ∧ r = (0, true)) := by
      intro hbad
      rcases hbad with hbad | hbad
      · exact hp hbad.1
      · have hmlabel : (owner j).label = .A := by
          cases hl : (owner j).label <;>
            simp [r, parentOfLabel, hl] at hbad ⊢
        have hcO : c ∈ cert.O.cells := by
          have hcBoth : c ∈ (cert.P 0 true).cells ∩
              (cert.P 0 false).cells := by
            rw [Finset.mem_inter]
            constructor
            · have hr : parentOfLabel (owner j).label = (0, true) := hbad.2
              simpa [r, hr] using hm.1
            · simpa [hbad.1] using hcP
          rw [← hAB]
          exact hcBoth
        exact hm.2 hmlabel hcO
    have hdisj := original_disjoint p.1 r hpr hexception
    exact False.elim ((Finset.disjoint_left.mp hdisj) hcP hm.1)

private theorem parentMap_injective :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), ∀ (cells : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T.cells), ∀ (modified_cell_owner : ∀ (c : LatticeCell), (c ∈ T.cells) → (∃ a :
            PeriodicSubtileIndex, a.first = 0 ∧ a.second = 0 ∧ c ∈ (cert.modified.tile
                a).cells)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun j =>
          Classical.choose (modified_cell_owner (LatticeVertexIncidentCell x j) (cells j))
        ∀ (parent_boundary_incident_cell : ∀ (i : Fin 3), ∀ (s : Bool), (x ∈
            BoundaryFootprintVertices (cert.P i s)) → (∃ j : Fin 4, LatticeVertexIncidentCell x j
            ∈ (cert.P i s).cells)),
        let modifiedOwners : Finset PeriodicSubtileIndex :=
                Finset.univ.image owner
        (Fin (4 : ℕ)) → (
        let BoundaryParents := {a : Fin 3 × Bool //
          x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)}
        let parentOfLabel : SixSubtileLabel → Fin 3 × Bool := fun
          | .A => (0, true)
          | .B => (0, false)
          | .C => (1, true)
          | .D => (1, false)
          | .E => (2, true)
          | .F => (2, false)
        let parentCellIndex : BoundaryParents → Fin 4 := fun p =>
          Classical.choose (parent_boundary_incident_cell p.1.1 p.1.2 p.2)
        (∀ (p : BoundaryParents), (p.1 ≠ (0, true)) → (p.1 = parentOfLabel (owner
            (parentCellIndex p)).label)) → (
        let ModOwner := {m : PeriodicSubtileIndex // m ∈ modifiedOwners}
        let parentMap : BoundaryParents → Sum ModOwner Unit := fun p =>
          if p.1 = (0, true) then Sum.inr Unit.unit
          else
            let j := parentCellIndex p
            Sum.inl ⟨owner j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
        Function.Injective parentMap))) := by
  classical
  intro q cfg C T cert x cells modified_cell_owner owner parent_boundary_incident_cell
      modifiedOwners j BoundaryParents parentOfLabel parentCellIndex parent_matches_owner
      ModOwner parentMap p q hpq
  by_cases hp : p.1 = (0, true)
  · have hq : q.1 = (0, true) := by
      by_contra hq
      simp [parentMap, hp, hq] at hpq
    apply Subtype.ext
    exact hp.trans hq.symm
  · by_cases hq : q.1 = (0, true)
    · simp [parentMap, hp, hq] at hpq
    · have heq : owner (parentCellIndex p) =
          owner (parentCellIndex q) := by
        have hsub : (⟨owner (parentCellIndex p),
            Finset.mem_image.mpr ⟨parentCellIndex p, Finset.mem_univ _, rfl⟩⟩ : ModOwner) =
            ⟨owner (parentCellIndex q),
            Finset.mem_image.mpr ⟨parentCellIndex q, Finset.mem_univ _, rfl⟩⟩ := by
          have hsum := hpq
          simp only [Fin.isValue, hp, ↓reduceIte, hq, Sum.inl.injEq, parentMap] at hsum
          exact hsum
        exact congrArg Subtype.val hsub
      apply Subtype.ext
      calc
        p.1 = parentOfLabel (owner (parentCellIndex p)).label :=
          parent_matches_owner p hp
        _ = parentOfLabel (owner (parentCellIndex q)).label := by rw [heq]
        _ = q.1 := (parent_matches_owner q hq).symm

private theorem hupper :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), ∀ (cells : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T.cells), ∀ (modified_cell_owner : ∀ (c : LatticeCell), (c ∈ T.cells) → (∃ a :
            PeriodicSubtileIndex, a.first = 0 ∧ a.second = 0 ∧ c ∈ (cert.modified.tile
                a).cells)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun j =>
          Classical.choose (modified_cell_owner (LatticeVertexIncidentCell x j) (cells j));
        ∀ (parent_boundary_incident_cell : ∀ (i : Fin 3), ∀ (s : Bool), (x ∈
            BoundaryFootprintVertices (cert.P i s)) → (∃ j : Fin 4, LatticeVertexIncidentCell x j
            ∈ (cert.P i s).cells)),
        let modifiedOwners : Finset PeriodicSubtileIndex :=
                Finset.univ.image owner;
        (
        let BoundaryParents := {a : Fin 3 × Bool //
          x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)};
        let parentCellIndex : BoundaryParents → Fin 4 := fun p =>
          Classical.choose (parent_boundary_incident_cell p.1.1 p.1.2 p.2);
        let ModOwner := {m : PeriodicSubtileIndex // m ∈ modifiedOwners};
        let parentMap : BoundaryParents → Sum ModOwner Unit := fun p =>
          if p.1 = (0, true) then Sum.inr Unit.unit
          else
            let j := parentCellIndex p
            Sum.inl ⟨owner j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩;
        (Function.Injective parentMap) → (Nat.card BoundaryParents ≤ modifiedOwners.card + 1)))
            := by
  classical
  intro q cfg C T cert x cells modified_cell_owner owner parent_boundary_incident_cell
      modifiedOwners BoundaryParents parentCellIndex ModOwner parentMap parentMap_injective
  have hcard := Fintype.card_le_of_injective parentMap parentMap_injective
  simpa [BoundaryParents, ModOwner, Nat.card_eq_fintype_card,
    Fintype.card_sum] using hcard

private theorem hbound :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), ∀ (cells : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T.cells), ∀ (modified_cell_owner : ∀ (c : LatticeCell), (c ∈ T.cells) → (∃ a :
            PeriodicSubtileIndex, a.first = 0 ∧ a.second = 0 ∧ c ∈ (cert.modified.tile a).cells)),
        let owner : Fin 4 → PeriodicSubtileIndex := fun j =>
          Classical.choose (modified_cell_owner (LatticeVertexIncidentCell x j) (cells j))
        let modifiedOwners : Finset PeriodicSubtileIndex := Finset.univ.image owner
        (modifiedOwners.card ≤ 3) → (
        let BoundaryParents := {a : Fin 3 × Bool //
          x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)}
        (Nat.card BoundaryParents ≤ modifiedOwners.card + 1) → (Nat.card BoundaryParents ≤ 4)) )
            := by
  classical
  intro q cfg C T cert x cells modified_cell_owner owner modifiedOwners modifiedOwnerCard
      BoundaryParents hupper
  have hcard : modifiedOwners.card + 1 ≤ 4 := by omega
  omega

end GeneralDescentGeometry

theorem P4120T1GeneralDescent
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (x : GaussianInt) (hx : x ∈ FootprintVertices T)
    (hxb : x ∉ BoundaryFootprintVertices T) :
    let k := Nat.card {a : Fin 3 × Bool //
      x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)}
    (k = 2 ∨ k = 3 ∨ k = 4) ∨
      ∃ i : Fin 3, ∃ s : Bool,
        0 < (q i.succ).1 ∧ x ∈ FootprintVertices (cert.P i s) ∧
          x ∉ BoundaryFootprintVertices (cert.P i s) := by
-- BODY
  classical
  have cells := InteriorFootprintIncidence.allIncidentCells T x hxb
      (InteriorFootprintIncidence.someIncidentCell T x hx hxb
      (InteriorFootprintIncidence.nonempty T x hx hxb))
  have hcurv := ProperBandCurvatureStructure q cfg.proper
  have hOsub := GeneralDescentGeometry.hOsub q cfg C T cert
  have modified_cell_owner := GeneralDescentGeometry.modified_cell_owner q cfg C T cert hOsub
  let owner : Fin 4 → PeriodicSubtileIndex := fun j =>
    Classical.choose (modified_cell_owner (LatticeVertexIncidentCell x j) (cells j))
  let I : GaussianInt := ⟨0, 1⟩
  have owner_spec (j : Fin 4) : (owner j).first = 0 ∧ (owner j).second = 0 ∧
      LatticeVertexIncidentCell x j ∈ (cert.modified.tile (owner j)).cells :=
    Classical.choose_spec (modified_cell_owner (LatticeVertexIncidentCell x j) (cells j))
  have incident_footprint := GeneralDescentGeometry.incident_footprint x
  have owner_unique (c : LatticeCell) (a b : PeriodicSubtileIndex)
      (ha : c ∈ (cert.modified.tile a).cells) (hb : c ∈ (cert.modified.tile b).cells) :
      a = b := (cert.partition c).unique (by simpa [cert.modified_tile] using ha)
        (by simpa [cert.modified_tile] using hb)
  have cell_edge_vleft := GeneralDescentGeometry.cell_edge_vleft
  have cell_edge_vright := GeneralDescentGeometry.cell_edge_vright
  have cell_edge_hbottom := GeneralDescentGeometry.cell_edge_hbottom
  have cell_edge_htop := GeneralDescentGeometry.cell_edge_htop
  have edge_support := GeneralDescentGeometry.edge_support x
  have parent_cells_nonempty (i : Fin 3) (s : Bool) :
      (cert.P i s).cells.Nonempty :=
    (LatticeTileGridStructure _ (cert.parent_lattice i s)).1.1
  have parent_boundary_incident_cell := GeneralDescentGeometry.parent_boundary_incident_cell q
      cfg C T cert x edge_support (GeneralDescentGeometry.boundary_edge_is_footprint
      cell_edge_vleft cell_edge_vright cell_edge_hbottom cell_edge_htop) parent_cells_nonempty
  have pair_left_mem {a b c d : GaussianInt}
      (h : ({a, b} : Finset GaussianInt) = {c, d}) := GeneralDescentGeometry.pair_left_mem (a :=
          a) (b := b) (c := c) (d := d) h
  have pair_right_mem {a b c d : GaussianInt}
      (h : ({a, b} : Finset GaussianInt) = {c, d}) := GeneralDescentGeometry.pair_right_mem (a :=
          a) (b := b) (c := c) (d := d) h
  have adjacent_of_edge := GeneralDescentGeometry.adjacent_of_edge q cfg C T cert
  let modifiedOwners : Finset PeriodicSubtileIndex := Finset.univ.image owner
  change ((Nat.card {a : Fin 3 × Bool //
    x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)} = 2 ∨
      Nat.card {a : Fin 3 × Bool //
        x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)} = 3 ∨
      Nat.card {a : Fin 3 × Bool //
        x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)} = 4) ∨
    (∃ i : Fin 3, ∃ s : Bool,
      0 < (q i.succ).1 ∧ x ∈ FootprintVertices (cert.P i s) ∧
        x ∉ BoundaryFootprintVertices (cert.P i s)))
  by_cases hcount :
      Nat.card {a : Fin 3 × Bool //
        x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)} = 2 ∨
        Nat.card {a : Fin 3 × Bool //
          x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)} = 3 ∨
        Nat.card {a : Fin 3 × Bool //
          x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)} = 4
  · exact Or.inl hcount
  · right
    by_contra hnoWitness
    have sourceParent (j : Fin 4) :
        ∃ i : Fin 3, ∃ s : Bool,
          LatticeVertexIncidentCell x j ∈ (cert.P i s).cells :=
      (cert.outer_union (LatticeVertexIncidentCell x j)).mp (cells j)
    let parentOwner : Fin 4 → Fin 3 × Bool := fun j =>
      (Classical.choose (sourceParent j),
        Classical.choose (Classical.choose_spec (sourceParent j)))
    have parentOwner_spec (j : Fin 4) :
        LatticeVertexIncidentCell x j ∈
          (cert.P (parentOwner j).1 (parentOwner j).2).cells :=
      Classical.choose_spec (Classical.choose_spec (sourceParent j))
    have parentOwner_boundary (j : Fin 4) :
        x ∈ BoundaryFootprintVertices
          (cert.P (parentOwner j).1 (parentOwner j).2) :=
      (GeneralDescentGeometry.hnoInterior q cfg C T cert x ((show
          ∀ i : Fin 3, Bool → 0 < (q i.succ).1
        from by
          intro i s
          exact GeneralDescentGeometry.hpos q cfg hcurv i)) hnoWitness) _ _ (incident_footprint
              j _ (parentOwner_spec j))
    have another_parent := GeneralDescentGeometry.another_parent q cfg C T cert x
        (GeneralDescentGeometry.all_incident_not_boundary x) sourceParent parentOwner_spec
            parentOwner_boundary
    rcases another_parent with ⟨j, hj⟩
    let BoundaryParents := {a : Fin 3 × Bool //
      x ∈ BoundaryFootprintVertices (cert.P a.1 a.2)}
    let p0 : BoundaryParents := ⟨parentOwner 0, parentOwner_boundary 0⟩
    let pj : BoundaryParents := ⟨parentOwner j, parentOwner_boundary j⟩
    let chooseTwo : Fin 2 → BoundaryParents := fun n => if n = 0 then p0 else pj
    have two_le_card : 2 ≤ Nat.card BoundaryParents  := GeneralDescentGeometry.two_le_card q cfg C
        T cert x sourceParent parentOwner_boundary j (GeneralDescentGeometry.chooseTwo_injective
            q cfg C T cert x sourceParent parentOwner_boundary j (GeneralDescentGeometry.hp0j q
            cfg C T cert x sourceParent parentOwner_boundary j hj))
    have hseparation := BandOriginalPairSeparation cert.P cert.O cert.u cert.v
      (GeneralDescentGeometry.hOA q cfg C T cert) hOsub cert.partition
    let parentOfLabel : SixSubtileLabel → Fin 3 × Bool
      | .A => (0, true)
      | .B => (0, false)
      | .C => (1, true)
      | .D => (1, false)
      | .E => (2, true)
      | .F => (2, false)
    let labelFromParent : Fin 3 × Bool → SixSubtileLabel
      | (0, true) => .A
      | (0, false) => .B
      | (1, true) => .C
      | (1, false) => .D
      | (2, true) => .E
      | (2, false) => .F
    let originalIndex : Fin 3 × Bool → PeriodicSubtileIndex := fun p =>
      ⟨labelFromParent p, 0, 0⟩
    have parent_label_roundtrip := GeneralDescentGeometry.parent_label_roundtrip
    let parentCellIndex : BoundaryParents → Fin 4 := fun p =>
      Classical.choose (parent_boundary_incident_cell p.1.1 p.1.2 p.2)
    have parentCellIndex_spec (p : BoundaryParents) :
        LatticeVertexIncidentCell x (parentCellIndex p) ∈
          (cert.P p.1.1 p.1.2).cells :=
      Classical.choose_spec (parent_boundary_incident_cell p.1.1 p.1.2 p.2)
    let ModOwner := {m : PeriodicSubtileIndex // m ∈ modifiedOwners}
    let parentMap : BoundaryParents → Sum ModOwner Unit := fun p =>
      if p.1 = (0, true) then Sum.inr Unit.unit
      else
        let j := parentCellIndex p
        Sum.inl ⟨owner j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
    have hbound : Nat.card BoundaryParents ≤ 4  := GeneralDescentGeometry.hbound q cfg C T cert x
        cells modified_cell_owner
        (GeneralDescentGeometry.modifiedOwnerCard q cfg C T cert x cells modified_cell_owner
            (GeneralDescentGeometry.four_distinct_impossible q cfg C T cert x cells
            modified_cell_owner owner_spec incident_footprint owner_unique edge_support
            (GeneralDescentGeometry.star01_ne_12 x pair_right_mem)
            (GeneralDescentGeometry.star01_ne_23 x pair_right_mem)
            (GeneralDescentGeometry.star01_ne_30 x pair_right_mem)
            (GeneralDescentGeometry.star12_ne_23 x pair_left_mem)
            (GeneralDescentGeometry.star12_ne_30 x pair_left_mem)
            (GeneralDescentGeometry.star23_ne_30 x pair_left_mem)
            (GeneralDescentGeometry.chord_of_four_distinct q cfg C T cert x cells
            modified_cell_owner owner_spec (GeneralDescentGeometry.adj01 q cfg C T cert x cells
            modified_cell_owner owner_spec cell_edge_vleft cell_edge_vright adjacent_of_edge)
            (GeneralDescentGeometry.adj12 q cfg C T cert x cells modified_cell_owner owner_spec
            cell_edge_hbottom cell_edge_htop adjacent_of_edge) (GeneralDescentGeometry.adj23 q
            cfg C T cert x cells modified_cell_owner owner_spec cell_edge_vleft cell_edge_vright
            adjacent_of_edge) (GeneralDescentGeometry.adj30 q cfg C T cert x cells
            modified_cell_owner owner_spec cell_edge_hbottom cell_edge_htop adjacent_of_edge))))
            (GeneralDescentGeometry.hupper q cfg C T cert x cells modified_cell_owner
            parent_boundary_incident_cell (GeneralDescentGeometry.parentMap_injective q cfg C T
            cert x cells modified_cell_owner parent_boundary_incident_cell j
            (GeneralDescentGeometry.parent_matches_owner q cfg C T cert x cells
            modified_cell_owner owner_spec parent_boundary_incident_cell
            (GeneralDescentGeometry.modified_cell_parent q cfg C T cert)
            (GeneralDescentGeometry.original_disjoint q cfg C T cert hseparation
            parent_label_roundtrip (GeneralDescentGeometry.labelFromParent_injective
            parent_label_roundtrip) (GeneralDescentGeometry.originalIndex_parent q cfg C T cert
            (GeneralDescentGeometry.tile_zero))) (GeneralDescentGeometry.hAB q cfg C T cert
            hseparation (GeneralDescentGeometry.htrans)) parentCellIndex_spec)))
    have hlower : 2 ≤ Nat.card BoundaryParents := by
      simpa [BoundaryParents] using two_le_card
    have hk : Nat.card BoundaryParents = 2 ∨ Nat.card BoundaryParents = 3 ∨
        Nat.card BoundaryParents = 4 := by omega
    exact hcount (by simpa [BoundaryParents] using hk)

end ApollonianSuperharmonic

end
