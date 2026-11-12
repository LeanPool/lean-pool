/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.P4630T1RingIndex
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure
public import LeanPool.ApollonianSuperharmonic.P3102T2CommonEdgeSectorTransition
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIndexedMultiplicityOne
public import LeanPool.ApollonianSuperharmonic.TileDiskAreaCovariance
public import Mathlib.Data.List.Chain
public import Mathlib.Logic.Relation

-- [TABLET NODE: P4630T1CellRouteLift]

/-!
# P4630T1CellRouteLift

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CellRouteGeometry

private theorem op :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (x : LatticeCell), (x ∈ cert.O.cells) → (x ∈ (cert.P 0 true).cells) ) := by
  classical
  intro q cfg C₀ T cert x hx
  apply (cert.plus_union x).mpr
  exact ⟨0, false, by simpa only [← cert.precursor_eq] using hx⟩

private theorem om :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (x : LatticeCell), (x ∈ cert.O.cells) → (x ∈ (cert.P 0 false).cells) ) := by
  classical
  intro q cfg C₀ T cert x hx
  apply (cert.minus_union x).mpr
  exact ⟨0, true, by simpa only [← cert.precursor_cells] using hx⟩

private theorem original :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let shift := fun a : PeriodicSubtileIndex =>
          (a.first : GaussianInt) * cert.u + (a.second : GaussianInt) * cert.v
        let O := fun a : PeriodicSubtileIndex => TileTranslation cert.O (shift a)
        (∀ (x : LatticeCell), (x ∈ cert.O.cells) → (x ∈ (cert.P 0 false).cells)) → (∀ (a :
            PeriodicSubtileIndex), ∀ (x : LatticeCell), (x ∈ (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v a).cells) → (x ∈ (cert.modified.tile a).cells ∨ a.label = .A ∧ x
            ∈ (O a).cells ∧ x ∈ (cert.modified.tile ⟨.B, a.first, a.second⟩).cells)) ) := by
  classical
  intro q cfg C₀ T cert shift O om a x hx
  rcases a with ⟨l, m, n⟩
  cases l
  · simp only [SubtileOccurrenceInterpretation, TileTranslation] at hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    by_cases ho : y ∈ cert.O.cells
    · right
      refine ⟨rfl, Finset.mem_image.mpr ⟨y, ho, he⟩, ?_⟩
      rw [cert.modified_tile]
      exact Finset.mem_image.mpr ⟨y, om y ho, he⟩
    · left
      rw [cert.modified_tile]
      exact Finset.mem_image.mpr ⟨y, Finset.mem_sdiff.mpr ⟨hy, ho⟩, he⟩
  all_goals
    left
    simpa only [cert.modified_tile, ModifiedSubtileOccurrenceInterpretation,
      SubtileOccurrenceInterpretation, TileTranslation] using hx

private theorem dirty :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let safe := fun a : PeriodicSubtileIndex =>
          ¬ (a.first = 0 ∧ a.second = 0) ∧ ∀ i, ∀ k, a ≠ P4630T1RingIndex i k
        let shift := fun a : PeriodicSubtileIndex =>
          (a.first : GaussianInt) * cert.u + (a.second : GaussianInt) * cert.v
        let clean := fun x : LatticeCell => ∀ i, ∀ k, x ∉ (SubtileOccurrenceInterpretation cert.P
            cert.u cert.v (P4630T1RingIndex i k)).cells
        let O := fun a : PeriodicSubtileIndex => TileTranslation cert.O (shift a)
        (∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (cert.modified.tile a).cells) →
            ((∀ (a : PeriodicSubtileIndex), ∀ (x : LatticeCell), (x ∈
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v a).cells) → (x ∈
            (cert.modified.tile a).cells ∨ a.label = .A ∧ x ∈ (O a).cells ∧ x ∈
            (cert.modified.tile ⟨.B, a.first, a.second⟩).cells)) → (∀ (a : PeriodicSubtileIndex),
            (safe a) → (∀ (x : LatticeCell), (x ∈ (cert.modified.tile a).cells) → ((¬ clean x) →
            (∃ i k, (P4630T1RingIndex i k).label = .A ∧ a = ⟨.B, (P4630T1RingIndex i
            k).first, (P4630T1RingIndex i k).second⟩ ∧ x ∈ (O (P4630T1RingIndex i
            k)).cells))))) ) := by
  classical
  intro q cfg C₀ T cert safe shift clean O indexed original a ha x hx h
  obtain ⟨i, hi⟩ := not_forall.mp h
  obtain ⟨k, hk⟩ := not_forall.mp hi
  have hi' : x ∈ (SubtileOccurrenceInterpretation cert.P cert.u cert.v
      (P4630T1RingIndex i k)).cells := not_not.mp hk
  rcases original _ x hi' with hmod | ⟨hl, hO, hB⟩
  · exact False.elim (ha.2 i k ((indexed x).unique hx hmod))
  · exact ⟨i, k, hl, (indexed x).unique hx hB, hO⟩

private theorem clean_B :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let safe := fun a : PeriodicSubtileIndex =>
          ¬ (a.first = 0 ∧ a.second = 0) ∧ ∀ i, ∀ k, a ≠ P4630T1RingIndex i k
        let shift := fun a : PeriodicSubtileIndex =>
          (a.first : GaussianInt) * cert.u + (a.second : GaussianInt) * cert.v
        let clean := fun x : LatticeCell => ∀ i, ∀ k, x ∉ (SubtileOccurrenceInterpretation cert.P
            cert.u cert.v (P4630T1RingIndex i k)).cells
        let O := fun a : PeriodicSubtileIndex => TileTranslation cert.O (shift a)
        (∀ (x : LatticeCell), (x ∈ cert.O.cells) → (x ∈ (cert.P 0 true).cells)) → ((∀ (a :
            PeriodicSubtileIndex), (safe a) → (∀ (x : LatticeCell), (x ∈ (cert.modified.tile
            a).cells) → ((¬ clean x) → (∃ i k, (P4630T1RingIndex i k).label = .A ∧ a = ⟨.B,
            (P4630T1RingIndex i k).first, (P4630T1RingIndex i k).second⟩ ∧ x ∈ (O
            (P4630T1RingIndex i k)).cells)))) → (∀ (m : Int), ∀ (n : Int), (safe ⟨.B, m, n⟩) →
            ((∃ i k, P4630T1RingIndex i k = ⟨.A, m, n⟩) → (∀ (x : LatticeCell), (x ∈
            (cert.modified.tile ⟨.B, m, n⟩).cells) → (clean x ↔ x ∉ (TileTranslation cert.O ((m :
            GaussianInt) * cert.u + (n : GaussianInt) * cert.v)).cells))))) ) := by
  classical
  intro q cfg C₀ T cert safe shift clean O op dirty m n ha hA x hx
  constructor
  · intro hc hO
    obtain ⟨i, k, he⟩ := hA
    apply hc i k
    rw [he]
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hO
    exact Finset.mem_image.mpr ⟨y, op y hy, hxy⟩
  · intro hO
    by_contra hc
    obtain ⟨i, k, _, he, hmem⟩ := dirty _ ha x hx hc
    have hm := congrArg PeriodicSubtileIndex.first he
    have hn := congrArg PeriodicSubtileIndex.second he
    dsimp at hm hn
    apply hO
    simpa only [O, shift, ← hm, ← hn] using hmem

private theorem disk_B :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let safe := fun a : PeriodicSubtileIndex =>
          ¬ (a.first = 0 ∧ a.second = 0) ∧ ∀ i, ∀ k, a ≠ P4630T1RingIndex i k
        let clean := fun x : LatticeCell => ∀ i, ∀ k, x ∉ (SubtileOccurrenceInterpretation cert.P
            cert.u cert.v (P4630T1RingIndex i k)).cells
        let V := fun a : PeriodicSubtileIndex =>
          (⟨(cert.modified.tile a).cells.filter clean, (cert.modified.tile a).anchor⟩ : ProtoTile)
        (∀ (m : Int), ∀ (n : Int), (safe ⟨.B, m, n⟩) → ((∃ i k, P4630T1RingIndex i k = ⟨.A, m,
            n⟩) → (∀ (x : LatticeCell), (x ∈ (cert.modified.tile ⟨.B, m, n⟩).cells) → (clean x ↔
            x ∉ (TileTranslation cert.O ((m : GaussianInt) * cert.u + (n : GaussianInt) *
            cert.v)).cells)))) → (∀ (m : Int), ∀ (n : Int), (safe ⟨.B, m, n⟩) → ((∃ i k,
            P4630T1RingIndex i k = ⟨.A, m, n⟩) → (LatticeTile (V ⟨.B, m, n⟩)))) ) := by
  classical
  intro q cfg C₀ T cert safe clean V clean_B m n ha hA
  let D := TileTranslation (TileCellComplement (cert.P 0 false) cert.O)
    ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v)
  have cells : (V ⟨.B, m, n⟩).cells = D.cells := by
    ext x
    simp only [V, Finset.mem_filter]
    rw [and_congr_right (fun hx => clean_B m n ha hA x hx)]
    rw [cert.modified_tile]
    change x ∈ ((cert.P 0 false).cells.image (GaussianTranslation _)) ∧
      x ∉ (cert.O.cells.image (GaussianTranslation _)) ↔
        x ∈ (((cert.P 0 false).cells \ cert.O.cells).image (GaussianTranslation _))
    rw [Finset.image_sdiff _ _ (show Function.Injective (GaussianTranslation
      ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v)) from
      fun a b h => add_right_cancel h), Finset.mem_sdiff]
  have hd : LatticeTile D :=
    (TileDiskAreaCovariance _ _).1.mp cert.precursor_complement_lattice.2
  change TopologicalDisk (TileRealization (V ⟨.B, m, n⟩))
  simpa only [LatticeTile, TileRealization, cells] using hd

private theorem disk :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let safe := fun a : PeriodicSubtileIndex =>
          ¬ (a.first = 0 ∧ a.second = 0) ∧ ∀ i, ∀ k, a ≠ P4630T1RingIndex i k
        let shift := fun a : PeriodicSubtileIndex =>
          (a.first : GaussianInt) * cert.u + (a.second : GaussianInt) * cert.v
        let clean := fun x : LatticeCell => ∀ i, ∀ k, x ∉ (SubtileOccurrenceInterpretation cert.P
            cert.u cert.v (P4630T1RingIndex i k)).cells
        let O := fun a : PeriodicSubtileIndex => TileTranslation cert.O (shift a)
        let V := fun a : PeriodicSubtileIndex =>
          (⟨(cert.modified.tile a).cells.filter clean, (cert.modified.tile a).anchor⟩ : ProtoTile)
        (∀ (a : PeriodicSubtileIndex), (safe a) → (∀ (x : LatticeCell), (x ∈ (cert.modified.tile
            a).cells) → ((¬ clean x) → (∃ i k, (P4630T1RingIndex i k).label = .A ∧ a = ⟨.B,
            (P4630T1RingIndex i k).first, (P4630T1RingIndex i k).second⟩ ∧ x ∈ (O
            (P4630T1RingIndex i k)).cells)))) → ((∀ (m : Int), ∀ (n : Int), (safe ⟨.B, m, n⟩) →
            ((∃ i k, P4630T1RingIndex i k = ⟨.A, m, n⟩) → (LatticeTile (V ⟨.B, m, n⟩)))) → (∀
            (a : PeriodicSubtileIndex), (safe a) → (LatticeTile (V a)))) ) := by
  classical
  intro q cfg C₀ T cert safe shift clean O V dirty disk_B a ha
  by_cases h₁ : a = ⟨.B, -1, -1⟩
  · subst a
    exact disk_B (-1) (-1) ha ⟨0, 0, rfl⟩
  by_cases h₂ : a = ⟨.B, 0, -1⟩
  · subst a
    exact disk_B 0 (-1) ha ⟨0, 1, rfl⟩
  have cells : (V a).cells = (cert.modified.tile a).cells := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    by_contra hc
    obtain ⟨i, k, hl, he, _⟩ := dirty a ha x hx hc
    fin_cases i <;> fin_cases k <;>
      simp? [P4630T1RingIndex] at hl he
    · exact h₁ he
    · exact h₂ he
  change TopologicalDisk (TileRealization (V a))
  simpa only [LatticeTile, TileRealization, cells] using cert.modified.tiles_are_disks a

private theorem corner :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (p : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell p j ∈
            U.cells) → (p ∈ FootprintVertices U) ) := by
  classical
  intro U p j hx
  rw [FootprintVertices, ite_eq_left ⟨_, hx⟩]
  refine ⟨_, hx, ?_⟩
  fin_cases j <;> simp only [LatticeVertexIncidentCell,
    ]
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (by change p = (p - 1) + 1; abel))
  · exact Or.inr (Or.inr (Or.inr (by
      change p = (p - 1 - ⟨0, 1⟩) + 1 + ⟨0, 1⟩; abel)))
  · exact Or.inr (Or.inr (Or.inl (by change p = (p - ⟨0, 1⟩) + ⟨0, 1⟩; abel)))

private theorem crossing_clean :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let safe := fun a : PeriodicSubtileIndex =>
          ¬ (a.first = 0 ∧ a.second = 0) ∧ ∀ i, ∀ k, a ≠ P4630T1RingIndex i k
        let shift := fun a : PeriodicSubtileIndex =>
          (a.first : GaussianInt) * cert.u + (a.second : GaussianInt) * cert.v
        let clean := fun x : LatticeCell => ∀ i, ∀ k, x ∉ (SubtileOccurrenceInterpretation cert.P
            cert.u cert.v (P4630T1RingIndex i k)).cells
        let O := fun a : PeriodicSubtileIndex => TileTranslation cert.O (shift a)
        (∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (cert.modified.tile a).cells) →
            ((∀ (a : PeriodicSubtileIndex), ∀ (x : LatticeCell), (x ∈
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v a).cells) → (x ∈
            (cert.modified.tile a).cells ∨ a.label = .A ∧ x ∈ (O a).cells ∧ x ∈
            (cert.modified.tile ⟨.B, a.first, a.second⟩).cells)) → ((∀ (a :
            PeriodicSubtileIndex), (safe a) → (∀ (x : LatticeCell), (x ∈ (cert.modified.tile
            a).cells) → ((¬ clean x) → (∃ i k, (P4630T1RingIndex i k).label = .A ∧ a = ⟨.B,
            (P4630T1RingIndex i k).first, (P4630T1RingIndex i k).second⟩ ∧ x ∈ (O
            (P4630T1RingIndex i k)).cells)))) → ((∀ (U : ProtoTile), ∀ (p : GaussianInt), ∀ (j
            : Fin 4), (LatticeVertexIncidentCell p j ∈ U.cells) → (p ∈ FootprintVertices U)) → (∀
            (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (safe a) → ((safe b) → ((a
            ≠ b) → (∀ (p : GaussianInt), ∀ (j : Fin 4), ∀ (k : Fin 4), (LatticeVertexIncidentCell
            p j ∈ (cert.modified.tile a).cells) → ((LatticeVertexIncidentCell p k ∈
            (cert.modified.tile b).cells) → (clean (LatticeVertexIncidentCell p j)))))))))) ) := by
  classical
  intro q cfg C₀ T cert safe shift clean O indexed original dirty corner a b ha hb hab p j k hx hy
  by_contra hc
  obtain ⟨i, l, hlabel, he, hO⟩ := dirty a ha _ hx hc
  have hp := corner _ p j hO
  have hp' : p ∈ FootprintVertices
      (⟨{LatticeVertexIncidentCell p k}, LatticeVertexIncidentCell p k⟩ : ProtoTile) :=
    corner _ p k (by simp)
  have isolated := cert.precursor_isolated _ _ p hp _ hp'
  rcases isolated with hA | hB
  · rcases original _ _ hA with hmod | ⟨_, _, hmod⟩
    · have eq : b = P4630T1RingIndex i l := by
        have hidx : (⟨.A, (P4630T1RingIndex i l).first,
            (P4630T1RingIndex i l).second⟩ : PeriodicSubtileIndex) =
            P4630T1RingIndex i l := by
          cases hval : P4630T1RingIndex i l
          simp_all
        exact ((indexed _).unique hy hmod).trans hidx
      exact hb.2 i l eq
    · exact hab (he.trans ((indexed _).unique hy hmod).symm)
  · have hmod : LatticeVertexIncidentCell p k ∈
        (cert.modified.tile ⟨.B, (P4630T1RingIndex i l).first,
          (P4630T1RingIndex i l).second⟩).cells := by
      simpa only [cert.modified_tile, ModifiedSubtileOccurrenceInterpretation,
        SubtileOccurrenceInterpretation] using hB
    exact hab (he.trans ((indexed _).unique hy hmod).symm)

private theorem symmetry :
    (by
      classical
      exact
        ∀ {x : LatticeCell}, ∀ {y : LatticeCell}, FourNeighborAdjacent x y → FourNeighborAdjacent
            y x ) := by
  classical
  intro x y h
  rcases h with h | h | h | h
  all_goals subst y
  all_goals simp [FourNeighborAdjacent, Zsqrtd.ext_iff]

private theorem step :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let safe := fun a : PeriodicSubtileIndex =>
          ¬ (a.first = 0 ∧ a.second = 0) ∧ ∀ i, ∀ k, a ≠ P4630T1RingIndex i k
        let clean := fun x : LatticeCell => ∀ i, ∀ k, x ∉ (SubtileOccurrenceInterpretation cert.P
            cert.u cert.v (P4630T1RingIndex i k)).cells
        let V := fun a : PeriodicSubtileIndex =>
          (⟨(cert.modified.tile a).cells.filter clean, (cert.modified.tile a).anchor⟩ : ProtoTile)
        let E := fun c d => AllowedSubtileIncidence c d ∧ safe c ∧ safe d
        (∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (cert.modified.tile a).cells) →
            ((∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (safe a) → ((safe b) →
            ((a ≠ b) → (∀ (p : GaussianInt), ∀ (j : Fin 4), ∀ (k : Fin 4),
            (LatticeVertexIncidentCell p j ∈ (cert.modified.tile a).cells) →
            ((LatticeVertexIncidentCell p k ∈ (cert.modified.tile b).cells) → (clean
            (LatticeVertexIncidentCell p j))))))) → ((∀ {x : LatticeCell}, ∀ {y : LatticeCell},
            FourNeighborAdjacent x y → FourNeighborAdjacent y x) → (∀ {a : PeriodicSubtileIndex},
            ∀ {b : PeriodicSubtileIndex}, (E a b) → (∃ x ∈ (V a).cells, ∃ y ∈ (V b).cells,
            FourNeighborAdjacent x y)))) ) := by
  classical
  intro q cfg C₀ T cert safe clean V E indexed crossing_clean symmetry a b e
  have adj := (cert.modified_adjacency a b).mpr e.1
  have hab : a ≠ b := by rintro rfl; exact cert.modified.plane.adjacent_irreflexive _ adj
  obtain ⟨edge, h₁, h₂⟩ := cert.modified.adjacent_has_common_edge a b adj
  have hene : edge.Nonempty := by
    obtain ⟨x, _, h | h | h | h⟩ := h₁
    all_goals rw [h]; simp
  obtain ⟨p, hp⟩ := hene
  have disjoint : Disjoint (cert.modified.tile a).cells (cert.modified.tile b).cells :=
    Finset.disjoint_left.mpr (fun x hx hy => hab ((indexed x).unique hx hy))
  obtain ⟨j, _, hsector⟩ := P3102T2CommonEdgeSectorTransition _ _ p edge disjoint hp ⟨h₁, h₂⟩
  have adjacent (j : Fin 4) : FourNeighborAdjacent (LatticeVertexIncidentCell p j)
      (LatticeVertexIncidentCell p (j + 1)) := by
    fin_cases j <;> simp [FourNeighborAdjacent, LatticeVertexIncidentCell, Zsqrtd.ext_iff]
  rcases hsector with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · exact ⟨_, Finset.mem_filter.mpr ⟨hx, crossing_clean a b e.2.1 e.2.2 hab p _ _ hx hy⟩,
      _, Finset.mem_filter.mpr ⟨hy, crossing_clean b a e.2.2 e.2.1 hab.symm p _ _ hy hx⟩,
      adjacent j⟩
  · exact ⟨_, Finset.mem_filter.mpr ⟨hx, crossing_clean a b e.2.1 e.2.2 hab p _ _ hx hy⟩,
      _, Finset.mem_filter.mpr ⟨hy, crossing_clean b a e.2.2 e.2.1 hab.symm p _ _ hy hx⟩,
      symmetry (adjacent j)⟩

private theorem within :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let safe := fun a : PeriodicSubtileIndex =>
          ¬ (a.first = 0 ∧ a.second = 0) ∧ ∀ i, ∀ k, a ≠ P4630T1RingIndex i k
        let clean := fun x : LatticeCell => ∀ i, ∀ k, x ∉ (SubtileOccurrenceInterpretation cert.P
            cert.u cert.v (P4630T1RingIndex i k)).cells
        let V := fun a : PeriodicSubtileIndex =>
          (⟨(cert.modified.tile a).cells.filter clean, (cert.modified.tile a).anchor⟩ : ProtoTile)
        let H := fun z w => FourNeighborAdjacent z w ∧ clean z ∧ clean w
        (∀ (a : PeriodicSubtileIndex), (safe a) → (LatticeTile (V a))) → (∀ (a :
            PeriodicSubtileIndex), (safe a) → (∀ (x : LatticeCell), (x ∈ (V a).cells) → (∀ (y :
            LatticeCell), (y ∈ (V a).cells) → (Relation.ReflTransGen H x y)))) ) := by
  classical
  intro q cfg C₀ T cert safe clean V H disk a ha x hx y hy
  obtain ⟨p, hp, hl, hm, hs⟩ :=
    (LatticeTileGridStructure _ (disk a ha)).1.2 x hx y hy
  have hne : p ≠ [] := by rintro rfl; simp at hp
  have chain : p.IsChain H :=
    (List.isChain_iff_forall_rel_of_append_cons_cons.mpr hs).imp_of_mem_imp
      (fun u v hu hv h => ⟨h, (Finset.mem_filter.mp (hm u hu)).2,
        (Finset.mem_filter.mp (hm v hv)).2⟩)
  have h := List.relationReflTransGen_of_exists_isChain p chain hne
  rw [List.head?_eq_some_head hne] at hp
  rw [List.getLast?_eq_getLast_of_ne_nil hne] at hl
  simpa only [Option.some.inj hp, Option.some.inj hl] using h

end CellRouteGeometry

theorem P4630T1CellRouteLift
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T) :
    let safe := fun a : PeriodicSubtileIndex =>
      ¬ (a.first = 0 ∧ a.second = 0) ∧
        ∀ i k, a ≠ P4630T1RingIndex i k
    let clean := fun x : LatticeCell => ∀ i k,
      x ∉ (SubtileOccurrenceInterpretation cert.P cert.u cert.v
        (P4630T1RingIndex i k)).cells
    ∀ a b, safe a → safe b →
      Relation.ReflTransGen
        (fun c d => AllowedSubtileIncidence c d ∧ safe c ∧ safe d) a b →
      ∀ x ∈ (cert.modified.tile a).cells, clean x →
      ∀ y ∈ (cert.modified.tile b).cells, clean y →
      Relation.ReflTransGen
        (fun z w => FourNeighborAdjacent z w ∧ clean z ∧ clean w) x y := by
-- BODY
  classical
  let safe := fun a : PeriodicSubtileIndex =>
    ¬ (a.first = 0 ∧ a.second = 0) ∧ ∀ i k, a ≠ P4630T1RingIndex i k
  let shift := fun a : PeriodicSubtileIndex =>
    (a.first : GaussianInt) * cert.u + (a.second : GaussianInt) * cert.v
  let clean := fun x : LatticeCell => ∀ i k,
    x ∉ (SubtileOccurrenceInterpretation cert.P cert.u cert.v (P4630T1RingIndex i k)).cells
  let O := fun a : PeriodicSubtileIndex => TileTranslation cert.O (shift a)
  let V := fun a : PeriodicSubtileIndex =>
    (⟨(cert.modified.tile a).cells.filter clean, (cert.modified.tile a).anchor⟩ : ProtoTile)
  let E := fun c d => AllowedSubtileIncidence c d ∧ safe c ∧ safe d
  let H := fun z w => FourNeighborAdjacent z w ∧ clean z ∧ clean w
  change ∀ a b, safe a → safe b → Relation.ReflTransGen E a b →
    ∀ x ∈ (cert.modified.tile a).cells, clean x →
    ∀ y ∈ (cert.modified.tile b).cells, clean y → Relation.ReflTransGen H x y
  have indexed := PeriodicTileIndexedMultiplicityOne cert.modified
  have op (x : LatticeCell) (hx : x ∈ cert.O.cells) := CellRouteGeometry.op q cfg C₀ T cert x hx
  have om (x : LatticeCell) (hx : x ∈ cert.O.cells) := CellRouteGeometry.om q cfg C₀ T cert x hx
  have original (a : PeriodicSubtileIndex) (x : LatticeCell)
      (hx : x ∈ (SubtileOccurrenceInterpretation cert.P cert.u cert.v a).cells) :=
          CellRouteGeometry.original q cfg C₀ T cert om a x hx
  have dirty (a : PeriodicSubtileIndex) (ha : safe a) (x : LatticeCell)
      (hx : x ∈ (cert.modified.tile a).cells) (h : ¬ clean x) := CellRouteGeometry.dirty q cfg C₀
          T cert indexed original a ha x hx h
  have clean_B (m n : Int) (ha : safe ⟨.B, m, n⟩)
      (hA : ∃ i k, P4630T1RingIndex i k = ⟨.A, m, n⟩)
      (x : LatticeCell) (hx : x ∈ (cert.modified.tile ⟨.B, m, n⟩).cells) :=
          CellRouteGeometry.clean_B q cfg C₀ T cert op dirty m n ha hA x hx
  have disk_B (m n : Int) (ha : safe ⟨.B, m, n⟩)
      (hA : ∃ i k, P4630T1RingIndex i k = ⟨.A, m, n⟩) := CellRouteGeometry.disk_B q cfg C₀ T
          cert clean_B m n ha hA
  have disk (a : PeriodicSubtileIndex) (ha : safe a) := CellRouteGeometry.disk q cfg C₀ T cert
      dirty disk_B a ha
  have corner (U : ProtoTile) (p : GaussianInt) (j : Fin 4)
      (hx : LatticeVertexIncidentCell p j ∈ U.cells) := CellRouteGeometry.corner U p j hx
  have crossing_clean (a b : PeriodicSubtileIndex) (ha : safe a) (hb : safe b)
      (hab : a ≠ b) (p : GaussianInt) (j k : Fin 4)
      (hx : LatticeVertexIncidentCell p j ∈ (cert.modified.tile a).cells)
      (hy : LatticeVertexIncidentCell p k ∈ (cert.modified.tile b).cells) :=
          CellRouteGeometry.crossing_clean q cfg C₀ T cert indexed original dirty corner a b ha
          hb hab p j k hx hy
  have symmetry : ∀ {x y : LatticeCell},
      FourNeighborAdjacent x y → FourNeighborAdjacent y x := @CellRouteGeometry.symmetry
  have step {a b : PeriodicSubtileIndex} (e : E a b) := CellRouteGeometry.step q cfg C₀ T cert
      indexed crossing_clean symmetry (a := a) (b := b) e
  have within (a : PeriodicSubtileIndex) (ha : safe a)
      (x : LatticeCell) (hx : x ∈ (V a).cells)
      (y : LatticeCell) (hy : y ∈ (V a).cells) := CellRouteGeometry.within q cfg C₀ T cert disk a
          ha x hx y hy
  intro a b ha hb path
  clear hb
  induction path with
  | refl =>
    intro x hx hcx y hy hcy
    exact within a ha x (Finset.mem_filter.mpr ⟨hx, hcx⟩)
      y (Finset.mem_filter.mpr ⟨hy, hcy⟩)
  | @tail b c path e ih =>
    intro x hx hcx y hy hcy
    obtain ⟨u, hu, v, hv, huv⟩ := step e
    have hu' := Finset.mem_filter.mp hu
    have hv' := Finset.mem_filter.mp hv
    exact (ih x hx hcx u hu'.1 hu'.2).trans
      ((Relation.ReflTransGen.single ⟨huv, hu'.2, hv'.2⟩).trans
        (within c e.2.2 v hv y (Finset.mem_filter.mpr ⟨hy, hcy⟩)))

end ApollonianSuperharmonic

end
