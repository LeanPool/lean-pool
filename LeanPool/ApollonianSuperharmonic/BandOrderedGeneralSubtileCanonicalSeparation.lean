/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.TileTranslationProperties

public import LeanPool.ApollonianSuperharmonic.BandOriginalPairSeparation
public import LeanPool.ApollonianSuperharmonic.TileDiskAreaCovariance


-- [TABLET NODE: BandOrderedGeneralSubtileCanonicalSeparation]

/-!
# BandOrderedGeneralSubtileCanonicalSeparation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

private theorem rowSeparation
    (parentSlot : Fin 3)
    (turn : Fin 4)
    (uIndex : PeriodicSubtileIndex)
    (uBar : PeriodicSubtileIndex)
    (vIndex : PeriodicSubtileIndex)
    (vBar : PeriodicSubtileIndex)
    (wBlock : Int × Int)
    (hrow : (parentSlot = 0 ∧ turn = 0 ∧
        uIndex = ⟨.A, 0, -1⟩ ∧ uBar = ⟨.B, 1, 1⟩ ∧
        wBlock = (1, 0) ∧ vIndex = ⟨.C, 1, 0⟩ ∧ vBar = ⟨.C, 1, 1⟩) ∨
      (parentSlot = 0 ∧ turn = 1 ∧
        uIndex = ⟨.B, 1, 1⟩ ∧ uBar = ⟨.B, 0, 1⟩ ∧
        wBlock = (-1, 0) ∧ vIndex = ⟨.F, 1, 0⟩ ∧ vBar = ⟨.E, 0, 1⟩) ∨
      (parentSlot = 0 ∧ turn = 2 ∧
        uIndex = ⟨.B, 0, 1⟩ ∧ uBar = ⟨.A, -1, -1⟩ ∧
        wBlock = (-1, 0) ∧ vIndex = ⟨.D, -1, 0⟩ ∧ vBar = ⟨.D, -1, -1⟩) ∨
      (parentSlot = 0 ∧ turn = 3 ∧
        uIndex = ⟨.A, -1, -1⟩ ∧ uBar = ⟨.A, 0, -1⟩ ∧
        wBlock = (1, 0) ∧ vIndex = ⟨.E, -1, 0⟩ ∧ vBar = ⟨.F, 0, -1⟩) ∨
      (parentSlot = 1 ∧ turn = 0 ∧
        uIndex = ⟨.C, 1, 1⟩ ∧ uBar = ⟨.D, -1, 0⟩ ∧
        wBlock = (0, 1) ∧ vIndex = ⟨.E, 0, 1⟩ ∧ vBar = ⟨.E, -1, 0⟩) ∨
      (parentSlot = 1 ∧ turn = 1 ∧
        uIndex = ⟨.D, -1, 0⟩ ∧ uBar = ⟨.D, -1, -1⟩ ∧
        wBlock = (0, -1) ∧ vIndex = ⟨.B, 0, 1⟩ ∧ vBar = ⟨.A, -1, -1⟩) ∨
      (parentSlot = 1 ∧ turn = 2 ∧
        uIndex = ⟨.D, -1, -1⟩ ∧ uBar = ⟨.C, 1, 0⟩ ∧
        wBlock = (0, -1) ∧ vIndex = ⟨.F, 0, -1⟩ ∧ vBar = ⟨.F, 1, 0⟩) ∨
      (parentSlot = 1 ∧ turn = 3 ∧
        uIndex = ⟨.C, 1, 0⟩ ∧ uBar = ⟨.C, 1, 1⟩ ∧
        wBlock = (0, 1) ∧ vIndex = ⟨.A, 0, -1⟩ ∧ vBar = ⟨.B, 1, 1⟩) ∨
      (parentSlot = 2 ∧ turn = 0 ∧
        uIndex = ⟨.E, -1, 0⟩ ∧ uBar = ⟨.F, 0, -1⟩ ∧
        wBlock = (-1, -1) ∧ vIndex = ⟨.A, -1, -1⟩ ∧ vBar = ⟨.A, 0, -1⟩) ∨
      (parentSlot = 2 ∧ turn = 1 ∧
        uIndex = ⟨.F, 0, -1⟩ ∧ uBar = ⟨.F, 1, 0⟩ ∧
        wBlock = (1, 1) ∧ vIndex = ⟨.D, -1, -1⟩ ∧ vBar = ⟨.C, 1, 0⟩) ∨
      (parentSlot = 2 ∧ turn = 2 ∧
        uIndex = ⟨.F, 1, 0⟩ ∧ uBar = ⟨.E, 0, 1⟩ ∧
        wBlock = (1, 1) ∧ vIndex = ⟨.B, 1, 1⟩ ∧ vBar = ⟨.B, 0, 1⟩) ∨
      (parentSlot = 2 ∧ turn = 3 ∧
        uIndex = ⟨.E, 0, 1⟩ ∧ uBar = ⟨.E, -1, 0⟩ ∧
        wBlock = (-1, -1) ∧ vIndex = ⟨.C, 1, 1⟩ ∧ vBar = ⟨.D, -1, 0⟩)) :
    (0, 0) ≠ wBlock ∧
    (uIndex.first, uIndex.second) ≠ (0, 0) ∧
    (uBar.first, uBar.second) ≠ wBlock ∧
    (vIndex.first, vIndex.second) ≠ (0, 0) ∧
    uBar ≠ vBar ∧
    ¬ ((uBar.label = .A ∧ vBar.label = .B ∨
          uBar.label = .B ∧ vBar.label = .A) ∧
        uBar.first = vBar.first ∧ uBar.second = vBar.second) ∧
    wBlock ≠ (vBar.first, vBar.second) := by
  rcases hrow with h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    rcases h with ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩
    decide

namespace GeneralSeparationProof

private theorem occurrence_subset_block :
    ∀ (P : Fin 3 → Bool → ProtoTile), ∀ (O : ProtoTile), ∀ (T : ProtoTile), ∀ (u : GaussianInt),
        ∀ (v : GaussianInt), (O.cells ⊆ (P (0 : Fin (3 : ℕ)) false).cells) → ((∀ (m : ℤ), ∀ (n :
        ℤ), ∀ (z : LatticeCell), z ∈ (TileTranslation T ((↑m : GaussianInt) * u + (↑n :
        GaussianInt) * v)).cells ↔ ∃ (label : SixSubtileLabel), z ∈
        (ModifiedSubtileOccurrenceInterpretation P O u v ⟨label, m, n⟩).cells) → (∀ (o :
            PeriodicSubtileIndex), (SubtileOccurrenceInterpretation P u v o).cells ⊆
            (TileTranslation
        T ((↑o.first : GaussianInt) * u + (↑o.second : GaussianInt) * v)).cells)) := by
  classical
  intro P O T u v hOB hBlockCells o z hz
  apply (hBlockCells o.first o.second z).2
  cases o with
  | mk label m n =>
    cases label with
    | A =>
        change z ∈ (TileTranslation (P 0 true)
          ((m : GaussianInt) * u + (n : GaussianInt) * v)).cells at hz
        rw [(TileTranslationFormulas _ _).1] at hz
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
        by_cases hyO : y ∈ O.cells
        · refine ⟨.B, ?_⟩
          change GaussianTranslation _ y ∈
            (TileTranslation (P 0 false) _).cells
          rw [(TileTranslationFormulas _ _).1]
          exact Finset.mem_image.mpr ⟨y, hOB hyO, rfl⟩
        · refine ⟨.A, ?_⟩
          change GaussianTranslation _ y ∈
            (TileTranslation (TileCellComplement (P 0 true) O) _).cells
          rw [(TileTranslationFormulas _ _).1]
          exact Finset.mem_image.mpr ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyO⟩, rfl⟩
    | B =>
        refine ⟨.B, ?_⟩
        simpa [SubtileOccurrenceInterpretation,
          ModifiedSubtileOccurrenceInterpretation] using hz
    | C =>
        refine ⟨.C, ?_⟩
        simpa [SubtileOccurrenceInterpretation,
          ModifiedSubtileOccurrenceInterpretation] using hz
    | D =>
        refine ⟨.D, ?_⟩
        simpa [SubtileOccurrenceInterpretation,
          ModifiedSubtileOccurrenceInterpretation] using hz
    | E =>
        refine ⟨.E, ?_⟩
        simpa [SubtileOccurrenceInterpretation,
          ModifiedSubtileOccurrenceInterpretation] using hz
    | F =>
        refine ⟨.F, ?_⟩
        simpa [SubtileOccurrenceInterpretation,
          ModifiedSubtileOccurrenceInterpretation] using hz

private theorem root_occurrence_disjoint :
    ∀ (P : Fin 3 → Bool → ProtoTile),
      ∀ (T : ProtoTile),
        ∀ (u : GaussianInt),
          ∀ (v : GaussianInt),
            ((∀ (m : ℤ),
                ∀ (n : ℤ),
                  ∀ (r : ℤ),
                    ∀ (s : ℤ),
                      (m, n) ≠ (r, s) →
                        Disjoint
                          (TileTranslation T
                              ((↑m : GaussianInt) * u +
                                (↑n : GaussianInt) * v)).cells
                          (TileTranslation T
                              ((↑r : GaussianInt) * u +
                                (↑s : GaussianInt) * v)).cells) →
              ((∀ (o : PeriodicSubtileIndex),
                  (SubtileOccurrenceInterpretation P u v o).cells ⊆
                    (TileTranslation T
                        ((o.first : GaussianInt) * u +
                          (o.second : GaussianInt) * v)).cells) →
                (∀ (o : PeriodicSubtileIndex),
                  (o.first, o.second) ≠ ((0 : ℤ), (0 : ℤ)) →
                    Disjoint T.cells
                      (SubtileOccurrenceInterpretation P u v o).cells))) := by
  classical
  intro P T u v hblocks occurrence_subset_block o hnonzero
  have h := hblocks 0 0 o.first o.second (by
    intro heq
    exact hnonzero heq.symm)
  have hzero := congrArg ProtoTile.cells (TileTranslationProperties.zero T)
  rw [← hzero]
  simpa using h.mono_right (occurrence_subset_block o)

private theorem turn_map_injective :
    ∀ (g : GaussianInt), Function.Injective (fun z : LatticeCell => GaussianTranslation g
        (GaussianQuarterTurn z - 1)) := by
  classical
  intro g a b hab
  apply Zsqrtd.ext
  · have him := congrArg (fun z : GaussianInt => z.im) hab
    simp [GaussianTranslation, GaussianQuarterTurn] at him
    omega
  · have hre := congrArg (fun z : GaussianInt => z.re) hab
    simp [GaussianTranslation, GaussianQuarterTurn] at hre
    omega

end GeneralSeparationProof

theorem BandOrderedGeneralSubtileCanonicalSeparation
    (P : Fin 3 → Bool → ProtoTile) (O T U W V : ProtoTile)
    (u v g wShift : GaussianInt) (parentSlot : Fin 3) (turn : Fin 4)
    (uIndex uBar vIndex vBar : PeriodicSubtileIndex)
    (wBlock : Int × Int)
    (hrow :
      (parentSlot = 0 ∧ turn = 0 ∧
        uIndex = ⟨.A, 0, -1⟩ ∧ uBar = ⟨.B, 1, 1⟩ ∧
        wBlock = (1, 0) ∧ vIndex = ⟨.C, 1, 0⟩ ∧ vBar = ⟨.C, 1, 1⟩) ∨
      (parentSlot = 0 ∧ turn = 1 ∧
        uIndex = ⟨.B, 1, 1⟩ ∧ uBar = ⟨.B, 0, 1⟩ ∧
        wBlock = (-1, 0) ∧ vIndex = ⟨.F, 1, 0⟩ ∧ vBar = ⟨.E, 0, 1⟩) ∨
      (parentSlot = 0 ∧ turn = 2 ∧
        uIndex = ⟨.B, 0, 1⟩ ∧ uBar = ⟨.A, -1, -1⟩ ∧
        wBlock = (-1, 0) ∧ vIndex = ⟨.D, -1, 0⟩ ∧ vBar = ⟨.D, -1, -1⟩) ∨
      (parentSlot = 0 ∧ turn = 3 ∧
        uIndex = ⟨.A, -1, -1⟩ ∧ uBar = ⟨.A, 0, -1⟩ ∧
        wBlock = (1, 0) ∧ vIndex = ⟨.E, -1, 0⟩ ∧ vBar = ⟨.F, 0, -1⟩) ∨
      (parentSlot = 1 ∧ turn = 0 ∧
        uIndex = ⟨.C, 1, 1⟩ ∧ uBar = ⟨.D, -1, 0⟩ ∧
        wBlock = (0, 1) ∧ vIndex = ⟨.E, 0, 1⟩ ∧ vBar = ⟨.E, -1, 0⟩) ∨
      (parentSlot = 1 ∧ turn = 1 ∧
        uIndex = ⟨.D, -1, 0⟩ ∧ uBar = ⟨.D, -1, -1⟩ ∧
        wBlock = (0, -1) ∧ vIndex = ⟨.B, 0, 1⟩ ∧ vBar = ⟨.A, -1, -1⟩) ∨
      (parentSlot = 1 ∧ turn = 2 ∧
        uIndex = ⟨.D, -1, -1⟩ ∧ uBar = ⟨.C, 1, 0⟩ ∧
        wBlock = (0, -1) ∧ vIndex = ⟨.F, 0, -1⟩ ∧ vBar = ⟨.F, 1, 0⟩) ∨
      (parentSlot = 1 ∧ turn = 3 ∧
        uIndex = ⟨.C, 1, 0⟩ ∧ uBar = ⟨.C, 1, 1⟩ ∧
        wBlock = (0, 1) ∧ vIndex = ⟨.A, 0, -1⟩ ∧ vBar = ⟨.B, 1, 1⟩) ∨
      (parentSlot = 2 ∧ turn = 0 ∧
        uIndex = ⟨.E, -1, 0⟩ ∧ uBar = ⟨.F, 0, -1⟩ ∧
        wBlock = (-1, -1) ∧ vIndex = ⟨.A, -1, -1⟩ ∧ vBar = ⟨.A, 0, -1⟩) ∨
      (parentSlot = 2 ∧ turn = 1 ∧
        uIndex = ⟨.F, 0, -1⟩ ∧ uBar = ⟨.F, 1, 0⟩ ∧
        wBlock = (1, 1) ∧ vIndex = ⟨.D, -1, -1⟩ ∧ vBar = ⟨.C, 1, 0⟩) ∨
      (parentSlot = 2 ∧ turn = 2 ∧
        uIndex = ⟨.F, 1, 0⟩ ∧ uBar = ⟨.E, 0, 1⟩ ∧
        wBlock = (1, 1) ∧ vIndex = ⟨.B, 1, 1⟩ ∧ vBar = ⟨.B, 0, 1⟩) ∨
      (parentSlot = 2 ∧ turn = 3 ∧
        uIndex = ⟨.E, 0, 1⟩ ∧ uBar = ⟨.E, -1, 0⟩ ∧
        wBlock = (-1, -1) ∧ vIndex = ⟨.C, 1, 1⟩ ∧ vBar = ⟨.D, -1, 0⟩))
    (hRootLattice : LatticeTile T)
    (hParentLattice : ∀ j e, LatticeTile (P j e))
    (hOA : O.cells ⊆ (P 0 true).cells)
    (hOB : O.cells ⊆ (P 0 false).cells)
    (hpartition : ∀ z : LatticeCell, ∃! o : PeriodicSubtileIndex,
      z ∈ (ModifiedSubtileOccurrenceInterpretation P O u v o).cells)
    (hBlockCells : ∀ m n : Int, ∀ z : LatticeCell,
      (z ∈ (TileTranslation T
          ((m : GaussianInt) * u + (n : GaussianInt) * v)).cells ↔
        ∃ label : SixSubtileLabel,
          z ∈ (ModifiedSubtileOccurrenceInterpretation P O u v
            ⟨label, m, n⟩).cells))
    (hBlockDisjoint : ∀ m n r s : Int, (m, n) ≠ (r, s) →
      Disjoint
        (TileTranslation T
          ((m : GaussianInt) * u + (n : GaussianInt) * v)).cells
        (TileTranslation T
          ((r : GaussianInt) * u + (s : GaussianInt) * v)).cells)
    (hfixedSource : U.cells =
      (SubtileOccurrenceInterpretation P u v uIndex).cells)
    (hVSource : V.cells =
      (SubtileOccurrenceInterpretation P u v vIndex).cells)
    (hW : W = TileTranslation T wShift)
    (hrootBar : (TileTranslation (TileQuarterTurn T) g).cells = T.cells)
    (hfixedBar : (TileTranslation (TileQuarterTurn U) g).cells =
      (SubtileOccurrenceInterpretation P u v uBar).cells)
    (hWBar : (TileTranslation (TileQuarterTurn W) g).cells =
      (TileTranslation T
        ((wBlock.1 : GaussianInt) * u + (wBlock.2 : GaussianInt) * v)).cells)
    (hVBar : (TileTranslation (TileQuarterTurn V) g).cells =
      (SubtileOccurrenceInterpretation P u v vBar).cells) :
    LatticeTile T ∧ LatticeTile U ∧ LatticeTile W ∧ LatticeTile V ∧
      Disjoint T.cells U.cells ∧ Disjoint T.cells W.cells ∧
      Disjoint U.cells W.cells ∧ Disjoint T.cells V.cells ∧
      Disjoint U.cells V.cells ∧
      Disjoint W.cells V.cells := by
-- BODY
  classical
  have hTlattice : LatticeTile T := hRootLattice
  have occurrence_lattice (o : PeriodicSubtileIndex) :
      LatticeTile (SubtileOccurrenceInterpretation P u v o) := by
    cases o with
    | mk label m n =>
      cases label <;>
        exact (TileDiskAreaCovariance _
          ((m : GaussianInt) * u + (n : GaussianInt) * v)).1.mp
            (hParentLattice _ _)
  have lattice_of_cells_eq (A B : ProtoTile) (h : A.cells = B.cells)
      (hB : LatticeTile B) : LatticeTile A := by
    change TopologicalDisk (TileRealization A)
    rw [show TileRealization A = TileRealization B by
      simp only [TileRealization, h]]
    exact hB
  have hfixedLattice : LatticeTile U :=
    lattice_of_cells_eq _ _ hfixedSource (by
      simpa using occurrence_lattice uIndex)
  have hWLattice : LatticeTile W := by
    rw [hW]
    exact (TileDiskAreaCovariance T wShift).1.mp hTlattice
  have hVLattice : LatticeTile V :=
    lattice_of_cells_eq _ _ hVSource (by
      simpa using occurrence_lattice vIndex)
  have hblocks := hBlockDisjoint
  have horiginal := (BandOriginalPairSeparation P O u v
    hOA hOB hpartition).2
  have occurrence_subset_block (o : PeriodicSubtileIndex) :
      (SubtileOccurrenceInterpretation P u v o).cells ⊆
        (TileTranslation T
          ((o.first : GaussianInt) * u + (o.second : GaussianInt) * v)).cells :=
              GeneralSeparationProof.occurrence_subset_block P O T u v hOB hBlockCells o
  have root_occurrence_disjoint (o : PeriodicSubtileIndex)
      (hnonzero : (o.first, o.second) ≠ (0, 0)) :
      Disjoint T.cells (SubtileOccurrenceInterpretation P u v o).cells :=
          GeneralSeparationProof.root_occurrence_disjoint P T u v hblocks
          occurrence_subset_block o hnonzero
  have turn_mem (A : ProtoTile) (z : LatticeCell) (hz : z ∈ A.cells) :
      GaussianTranslation g (GaussianQuarterTurn z - 1) ∈
        (TileTranslation (TileQuarterTurn A) g).cells := by
    rw [(TileTranslationFormulas _ _).1, (TileQuarterTurnFormulas A).1]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨z, hz, rfl⟩, rfl⟩
  have pull_disjoint (A B : ProtoTile)
      (h : Disjoint (TileTranslation (TileQuarterTurn A) g).cells
        (TileTranslation (TileQuarterTurn B) g).cells) :
      Disjoint A.cells B.cells := by
    rw [Finset.disjoint_left] at h ⊢
    intro z hzA hzB
    exact h (turn_mem A z hzA) (turn_mem B z hzB)
  have hrootfixed : Disjoint T.cells U.cells := by
    rw [hfixedSource]
    simpa using root_occurrence_disjoint uIndex (by
      exact (rowSeparation parentSlot turn uIndex uBar vIndex vBar wBlock hrow).2.1)
  have hrootW : Disjoint T.cells W.cells := by
    apply pull_disjoint
    rw [hrootBar, hWBar]
    have h := hblocks 0 0 wBlock.1 wBlock.2
      (rowSeparation parentSlot turn uIndex uBar vIndex vBar wBlock hrow).1
    have hzero := congrArg ProtoTile.cells (TileTranslationProperties.zero T)
    simpa [hzero] using h
  have hfixedW : Disjoint U.cells W.cells := by
    apply pull_disjoint
    rw [hfixedBar, hWBar]
    exact (hblocks uBar.first uBar.second wBlock.1 wBlock.2 (by
      exact (rowSeparation parentSlot turn uIndex uBar vIndex vBar wBlock hrow).2.2.1)).mono
          (occurrence_subset_block uBar) (by intro z hz; exact hz)
  have hrootV : Disjoint T.cells V.cells := by
    rw [hVSource]
    simpa using root_occurrence_disjoint vIndex (by
      exact (rowSeparation parentSlot turn uIndex uBar vIndex vBar wBlock hrow).2.2.2.1)
  have hfixedV : Disjoint U.cells V.cells := by
    apply pull_disjoint
    rw [hfixedBar, hVBar]
    apply horiginal uBar vBar
    · exact (rowSeparation parentSlot turn uIndex uBar vIndex vBar wBlock hrow).2.2.2.2.1
    · exact (rowSeparation parentSlot turn uIndex uBar vIndex vBar wBlock hrow).2.2.2.2.2.1
  have hWV : Disjoint W.cells V.cells := by
    apply pull_disjoint
    rw [hWBar, hVBar]
    exact (hblocks wBlock.1 wBlock.2 vBar.first vBar.second (by
      exact (rowSeparation parentSlot turn uIndex uBar vIndex vBar wBlock
          hrow).2.2.2.2.2.2)).mono (by intro z hz; exact hz) (occurrence_subset_block vBar)
  exact ⟨hTlattice, hfixedLattice, hWLattice, hVLattice,
    hrootfixed, hrootW, hfixedW, hrootV, hfixedV, hWV⟩

end ApollonianSuperharmonic

end
