/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralFinitePatches
public import LeanPool.ApollonianSuperharmonic.BandSignedOccurrenceHalfTurn
public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrence
public import LeanPool.ApollonianSuperharmonic.FinitePatchTopology
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure
public import LeanPool.ApollonianSuperharmonic.ModifiedSubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIntersectionClassification
public import LeanPool.ApollonianSuperharmonic.PeriodicTileMultiplicityOne
public import LeanPool.ApollonianSuperharmonic.PeriodicTileComplex
public import LeanPool.ApollonianSuperharmonic.ProtoTile
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetric
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetricCenteredTransport
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.TileCellComplement
public import LeanPool.ApollonianSuperharmonic.TileCentroid
public import LeanPool.ApollonianSuperharmonic.TileDiskAreaCovariance
public import LeanPool.ApollonianSuperharmonic.TileTranslation
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.UniqueBoundedGridComplementComponent
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws
public import LeanPool.ApollonianSuperharmonic.IncomingSuperbasisRelation
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIndexedMultiplicityOne
public import LeanPool.ApollonianSuperharmonic.P4630T1AffineCellSymmetry
public import LeanPool.ApollonianSuperharmonic.P4630T1CellRouteLift
public import LeanPool.ApollonianSuperharmonic.P4630T1ExteriorNeighbors
public import LeanPool.ApollonianSuperharmonic.P4630T1ExteriorWalks
public import LeanPool.ApollonianSuperharmonic.P4630T1GridComplementCriterion
public import LeanPool.ApollonianSuperharmonic.P4630T1ParentRotation

-- [TABLET NODE: BandTwelveParentSurround]

/-!
# BandTwelveParentSurround

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TwelveParentGeometry

private theorem incoming :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (BandVectors.1
            (q 1) (q 0) + BandVectors.1 (q 2) (q 0) + BandVectors.1 (q 3) (q 0) = 0) ) := by
  classical
  intro q cfg
  simpa [Fin.sum_univ_succ, add_assoc] using
    (IncomingSuperbasisRelation q cfg.proper).1

private theorem outgoing :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandVectors.1 (q 1) (q 0) + BandVectors.1 (q 2) (q 0)
            + BandVectors.1 (q 3) (q 0) = 0) → ((∀ (j : Fin (3 : ℕ)), BandVectors.1 (q (0 : Fin
            (4 : ℕ))) (q j.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (q j.succ)
            (q (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (q (0 : Fin (4 : ℕ))) (q j.succ) = -(⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (q j.succ) (q (0 : Fin (4 : ℕ)))) →
            (BandVectors.1 (q 0) (q 1) + BandVectors.1 (q 0) (q 2) + BandVectors.1 (q 0) (q 3) =
            0)) ) := by
  classical
  intro q incoming flip
  have f₀ : BandVectors.1 (q 0) (q 1) =
      (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 1) (q 0) := (flip 0).1
  have f₁ : BandVectors.1 (q 0) (q 2) =
      (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 2) (q 0) := (flip 1).1
  have f₂ : BandVectors.1 (q 0) (q 3) =
      (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 3) (q 0) := (flip 2).1
  rw [f₀, f₁, f₂]
  calc
    _ = (⟨0, 1⟩ : GaussianInt) * (BandVectors.1 (q 1) (q 0) +
        BandVectors.1 (q 2) (q 0) + BandVectors.1 (q 3) (q 0)) := by ring
    _ = 0 := by rw [incoming]; simp

private theorem third :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (BandVectors.1 (q 0) (q 1) + BandVectors.1 (q 0) (q 2) + BandVectors.1 (q 0)
            (q 3) = 0) → (BandVectors.1 (q 0) (q 3) = -cert.u - cert.v) ) := by
  classical
  intro q cfg C₀ T cert outgoing
  rw [cert.period_u, cert.period_v]
  linear_combination outgoing

private theorem values :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let R := fun i k => SubtileOccurrenceInterpretation cert.P cert.u cert.v
          (P4630T1RingIndex i k)
        (BandVectors.1 (q 0) (q 3) = -cert.u - cert.v) → (R 0 0 = TileTranslation (cert.P 0 true)
            (BandVectors.1 (q 0) (q 3)) ∧ R 0 1 = TileTranslation (cert.P 0 true) (-BandVectors.1
            (q 0) (q 2)) ∧ R 0 2 = TileTranslation (cert.P 0 false) (-BandVectors.1 (q 0) (q 3))
            ∧ R 0 3 = TileTranslation (cert.P 0 false) (BandVectors.1 (q 0) (q 2)) ∧ R 1 0 =
            TileTranslation (cert.P 1 true) (BandVectors.1 (q 0) (q 1)) ∧ R 1 1 = TileTranslation
            (cert.P 1 true) (-BandVectors.1 (q 0) (q 3)) ∧ R 1 2 = TileTranslation (cert.P 1
            false) (-BandVectors.1 (q 0) (q 1)) ∧ R 1 3 = TileTranslation (cert.P 1 false)
            (BandVectors.1 (q 0) (q 3)) ∧ R 2 0 = TileTranslation (cert.P 2 true) (BandVectors.1
            (q 0) (q 2)) ∧ R 2 1 = TileTranslation (cert.P 2 true) (-BandVectors.1 (q 0) (q 1)) ∧
            R 2 2 = TileTranslation (cert.P 2 false) (-BandVectors.1 (q 0) (q 2)) ∧ R 2 3 =
            TileTranslation (cert.P 2 false) (BandVectors.1 (q 0) (q 1))) ) := by
  classical
  intro q cfg C₀ T cert R third
  simp [R, P4630T1RingIndex, SubtileOccurrenceInterpretation, third,
    ← cert.period_u, ← cert.period_v, sub_eq_add_neg, add_comm]

private theorem nonempty :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let R := fun i k => SubtileOccurrenceInterpretation cert.P cert.u cert.v
          (P4630T1RingIndex i k)
        let ring : ProtoTile :=
          ⟨Finset.univ.biUnion (fun i : Fin 3 =>
            Finset.univ.biUnion (fun k : Fin 4 => (R i k).cells)), 0⟩
        (∀ (x : LatticeCell), x ∈ ring.cells ↔ ∃ i k, x ∈ (R i k).cells) → ((R 0 0 =
            TileTranslation (cert.P 0 true) (BandVectors.1 (q 0) (q 3)) ∧ R 0 1 = TileTranslation
            (cert.P 0 true) (-BandVectors.1 (q 0) (q 2)) ∧ R 0 2 = TileTranslation (cert.P 0
            false) (-BandVectors.1 (q 0) (q 3)) ∧ R 0 3 = TileTranslation (cert.P 0 false)
            (BandVectors.1 (q 0) (q 2)) ∧ R 1 0 = TileTranslation (cert.P 1 true) (BandVectors.1
            (q 0) (q 1)) ∧ R 1 1 = TileTranslation (cert.P 1 true) (-BandVectors.1 (q 0) (q 3)) ∧
            R 1 2 = TileTranslation (cert.P 1 false) (-BandVectors.1 (q 0) (q 1)) ∧ R 1 3 =
            TileTranslation (cert.P 1 false) (BandVectors.1 (q 0) (q 3)) ∧ R 2 0 =
            TileTranslation (cert.P 2 true) (BandVectors.1 (q 0) (q 2)) ∧ R 2 1 = TileTranslation
            (cert.P 2 true) (-BandVectors.1 (q 0) (q 1)) ∧ R 2 2 = TileTranslation (cert.P 2
            false) (-BandVectors.1 (q 0) (q 2)) ∧ R 2 3 = TileTranslation (cert.P 2 false)
            (BandVectors.1 (q 0) (q 1))) → (ring.cells.Nonempty)) ) := by
  classical
  intro q cfg C₀ T cert R ring union values
  have lattice : LatticeTile (R 0 0) := by
    rw [values.1]
    exact (TileDiskAreaCovariance _ _).1.mp (cert.parent_lattice 0 true)
  obtain ⟨x, hx⟩ := (LatticeTileGridStructure _ lattice).1.1
  exact ⟨x, (union x).mpr ⟨0, 0, hx⟩⟩

private theorem rotation :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let R := fun i k => SubtileOccurrenceInterpretation cert.P cert.u cert.v
          (P4630T1RingIndex i k)
        let ring : ProtoTile :=
          ⟨Finset.univ.biUnion (fun i : Fin 3 =>
            Finset.univ.biUnion (fun k : Fin 4 => (R i k).cells)), 0⟩
        (∀ (x : LatticeCell), x ∈ ring.cells ↔ ∃ i k, x ∈ (R i k).cells) → (∀ (t : GaussianInt),
            (∀ (i : Fin (3 : ℕ)), ∀ (k : Fin (4 : ℕ)), Finset.image (fun (x : GaussianInt) =>
            GaussianQuarterTurn x - (1 : GaussianInt) + t) (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v (P4630T1RingIndex i k)).cells =
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v (P4630T1RingIndex i (k + (1 :
            Fin (4 : ℕ))))).cells) → (ring.cells.image (fun x => GaussianQuarterTurn x - 1 + t) =
            ring.cells)) ) := by
  classical
  intro q cfg C₀ T cert R ring union t rotate
  ext x
  constructor
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨i, k, hy⟩ := (union y).mp hy
    apply (union _).mpr
    refine ⟨i, k + 1, ?_⟩
    rw [← rotate i k]
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  · intro hx
    obtain ⟨i, k, hx⟩ := (union x).mp hx
    have hk : k - 1 + 1 = k := by omega
    rw [← hk, ← rotate i (k - 1)] at hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨y, (union y).mpr ⟨i, k - 1, hy⟩, he⟩

private theorem central :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (whole : FiniteInducedTilePatch cert.modified.plane cert.modified.tile),
            (whole.indices = {(⟨SixSubtileLabel.A, (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex),
            (⟨SixSubtileLabel.B, (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex), (⟨SixSubtileLabel.C,
            (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex), (⟨SixSubtileLabel.D, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex), (⟨SixSubtileLabel.E, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex), (⟨SixSubtileLabel.F, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex)}) → ((whole.unionTile = T) → (∀ (x : LatticeCell), x ∈ T.cells
            ↔ ∃ a : PeriodicSubtileIndex, (a.first = 0 ∧ a.second = 0) ∧ x ∈ (cert.modified.tile
            a).cells)) ) := by
  classical
  intro q cfg C₀ T cert whole whole_indices whole_tile x
  have h := whole.exact_union x
  rw [whole_tile] at h
  rw [h]
  apply exists_congr
  intro a
  rw [whole_indices]
  rcases a with ⟨l, m, n⟩
  cases l <;> simp [PeriodicSubtileIndex.mk.injEq]

private theorem latticeAt243 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (cert.modified.tile
            a).cells) → (∀ (whole : FiniteInducedTilePatch cert.modified.plane
            cert.modified.tile), (whole.unionTile = T) → (LatticeTile T)) ) := by
  classical
  intro q cfg C₀ T cert indexed whole whole_tile
  rw [← whole_tile]
  exact FinitePatchTopology cert.modified.plane cert.modified.tile
    (PeriodicTileMultiplicityOne cert.modified) indexed
    (fun a b _ h => cert.modified.adjacent_has_common_edge a b h) whole

private theorem modified_subset :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (a : PeriodicSubtileIndex), (cert.modified.tile a).cells ⊆
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v a).cells ) := by
  classical
  intro q cfg C₀ T cert a
  rw [cert.modified_tile]
  rcases a with ⟨l, m, n⟩
  cases l <;> intro x hx
  all_goals
    simp only [ModifiedSubtileOccurrenceInterpretation,
      SubtileOccurrenceInterpretation, TileTranslation] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_image.mpr
    refine ⟨y, ?_, rfl⟩
    first | exact (Finset.mem_sdiff.mp hy).1 | exact hy

private theorem original_owner :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (∀ (x : LatticeCell), (x ∈ cert.O.cells) → (x ∈ (cert.P 0 false).cells)) → (∀
            (a : PeriodicSubtileIndex), ∀ (x : LatticeCell), (x ∈
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v a).cells) → (x ∈
            (cert.modified.tile a).cells ∨ x ∈ (cert.modified.tile ⟨.B, a.first,
            a.second⟩).cells)) ) := by
  classical
  intro q cfg C₀ T cert precursor a x hx
  rcases a with ⟨l, m, n⟩
  cases l
  · simp only [SubtileOccurrenceInterpretation, TileTranslation] at hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    by_cases ho : y ∈ cert.O.cells
    · right
      rw [cert.modified_tile]
      exact Finset.mem_image.mpr ⟨y, precursor y ho, he⟩
    · left
      rw [cert.modified_tile]
      exact Finset.mem_image.mpr ⟨y, Finset.mem_sdiff.mpr ⟨hy, ho⟩, he⟩
  all_goals
    left
    simpa only [cert.modified_tile, ModifiedSubtileOccurrenceInterpretation,
      SubtileOccurrenceInterpretation, TileTranslation] using hx

private theorem external :
    (by
      classical
      exact
        ∀ (i k),
        ¬ ((P4630T1RingIndex i k).first = 0 ∧ (P4630T1RingIndex i k).second = 0) ) := by
  classical
  intro i k
  fin_cases i <;> fin_cases k <;> decide

private theorem outside :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (∀ (x : LatticeCell), ∃! a : PeriodicSubtileIndex, x ∈ (cert.modified.tile
            a).cells) → ((∀ (x : LatticeCell), x ∈ T.cells ↔ ∃ a : PeriodicSubtileIndex, (a.first
            = 0 ∧ a.second = 0) ∧ x ∈ (cert.modified.tile a).cells) → (∀ (a :
            PeriodicSubtileIndex), (¬ (a.first = 0 ∧ a.second = 0)) → (∀ (x : LatticeCell), (x ∈
            (cert.modified.tile a).cells) → (x ∉ T.cells)))) ) := by
  classical
  intro q cfg C₀ T cert indexed central a ha x hx ht
  obtain ⟨b, hb, hxb⟩ := (central x).mp ht
  have he := (indexed x).unique hx hxb
  exact ha (he.symm ▸ hb)

private theorem disjoint :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let R := fun i k => SubtileOccurrenceInterpretation cert.P cert.u cert.v
          (P4630T1RingIndex i k)
        let ring : ProtoTile :=
          ⟨Finset.univ.biUnion (fun i : Fin 3 =>
            Finset.univ.biUnion (fun k : Fin 4 => (R i k).cells)), 0⟩
        (∀ (x : LatticeCell), x ∈ ring.cells ↔ ∃ i k, x ∈ (R i k).cells) → ((∀ (a :
            PeriodicSubtileIndex), ∀ (x : LatticeCell), (x ∈ (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v a).cells) → (x ∈ (cert.modified.tile a).cells ∨ x ∈
            (cert.modified.tile ⟨.B, a.first, a.second⟩).cells)) → ((∀ (i k), ¬
            ((P4630T1RingIndex i k).first = 0 ∧ (P4630T1RingIndex i k).second = 0)) → ((∀ (a
            : PeriodicSubtileIndex), (¬ (a.first = 0 ∧ a.second = 0)) → (∀ (x : LatticeCell), (x
            ∈ (cert.modified.tile a).cells) → (x ∉ T.cells))) → ((T.cells : Set LatticeCell) ⊆
            (ring.cells : Set LatticeCell)ᶜ)))) ) := by
  classical
  intro q cfg C₀ T cert R ring union original_owner external outside x hx hr
  obtain ⟨i, k, hr⟩ := (union x).mp hr
  rcases original_owner _ x hr with h | h
  · exact outside _ (external i k) x h hx
  · exact outside ⟨.B, (P4630T1RingIndex i k).first,
      (P4630T1RingIndex i k).second⟩ (external i k) x h hx

private theorem common_edge :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (x : LatticeCell), ∀ (y : LatticeCell), (x ∈
            U.cells) → ((y ∈ V.cells) → ((FourNeighborAdjacent x y) → ((FootprintEdges U ∩
            FootprintEdges V).Nonempty))) ) := by
  classical
  intro U V x y hx hy h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨{x + 1, x + 1 + ⟨0, 1⟩},
      ⟨x, hx, Or.inr (Or.inr (Or.inl rfl))⟩,
      ⟨x + 1, hy, Or.inr (Or.inl rfl)⟩⟩
  · refine ⟨{x, x + ⟨0, 1⟩}, ⟨x, hx, Or.inr (Or.inl rfl)⟩,
      ⟨x - 1, hy, Or.inr (Or.inr (Or.inl ?_))⟩⟩
    simp
  · refine ⟨{x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩},
      ⟨x, hx, Or.inr (Or.inr (Or.inr rfl))⟩,
      ⟨x + ⟨0, 1⟩, hy, Or.inl ?_⟩⟩
    simp [add_comm, add_left_comm, add_assoc]
  · refine ⟨{x, x + 1}, ⟨x, hx, Or.inl rfl⟩,
      ⟨x - ⟨0, 1⟩, hy, Or.inr (Or.inr (Or.inr ?_))⟩⟩
    congr 1 <;> abel

private theorem boundary :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let R := fun i k => SubtileOccurrenceInterpretation cert.P cert.u cert.v
          (P4630T1RingIndex i k)
        let ring : ProtoTile :=
          ⟨Finset.univ.biUnion (fun i : Fin 3 =>
            Finset.univ.biUnion (fun k : Fin 4 => (R i k).cells)), 0⟩
        (∀ (x : LatticeCell), x ∈ ring.cells ↔ ∃ i k, x ∈ (R i k).cells) → ((∀ (x : LatticeCell),
            ∃! a : PeriodicSubtileIndex, x ∈ (cert.modified.tile a).cells) → ((∀ (x :
            LatticeCell), x ∈ T.cells ↔ ∃ a : PeriodicSubtileIndex, (a.first = 0 ∧ a.second = 0)
            ∧ x ∈ (cert.modified.tile a).cells) → ((∀ (a : PeriodicSubtileIndex),
            (cert.modified.tile a).cells ⊆ (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            a).cells) → ((∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (x : LatticeCell), ∀ (y :
            LatticeCell), (x ∈ U.cells) → ((y ∈ V.cells) → ((FourNeighborAdjacent x y) →
            ((FootprintEdges U ∩ FootprintEdges V).Nonempty)))) → (∀ x ∈ T.cells, ∀ y,
            FourNeighborAdjacent x y → y ∉ T.cells → y ∈ ring.cells))))) ) := by
  classical
  intro q cfg C₀ T cert R ring union indexed central modified_subset common_edge x hx y hxy hy
  obtain ⟨a, ha, hxa⟩ := (central x).mp hx
  obtain ⟨b, hyb, _⟩ := indexed y
  have hb : ¬ (b.first = 0 ∧ b.second = 0) :=
    fun hb => hy ((central y).mpr ⟨b, hb, hyb⟩)
  have hne : a ≠ b := fun h => hb (h ▸ ha)
  have adj := ((PeriodicTileIntersectionClassification cert.modified).1 a b hne).1.mp
    (common_edge _ _ x y hxa hyb hxy)
  obtain ⟨i, k, he⟩ := P4630T1ExteriorNeighbors
    ((cert.modified_adjacency a b).mp adj) ha hb
  apply (union y).mpr
  exact ⟨i, k, modified_subset _ (he ▸ hyb)⟩

private theorem escape :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let R := fun i k => SubtileOccurrenceInterpretation cert.P cert.u cert.v
          (P4630T1RingIndex i k)
        let ring : ProtoTile :=
          ⟨Finset.univ.biUnion (fun i : Fin 3 =>
            Finset.univ.biUnion (fun k : Fin 4 => (R i k).cells)), 0⟩
        (∀ (x : LatticeCell), x ∈ ring.cells ↔ ∃ i k, x ∈ (R i k).cells) → ((∀ (x : LatticeCell),
            ∃! a : PeriodicSubtileIndex, x ∈ (cert.modified.tile a).cells) → ((∀ (x :
            LatticeCell), x ∈ T.cells ↔ ∃ a : PeriodicSubtileIndex, (a.first = 0 ∧ a.second = 0)
            ∧ x ∈ (cert.modified.tile a).cells) → ((∀ (a : PeriodicSubtileIndex),
            (cert.modified.tile a).cells ⊆ (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            a).cells) → ((∀ (a : PeriodicSubtileIndex), ∀ (x : LatticeCell), (x ∈
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v a).cells) → (x ∈
            (cert.modified.tile a).cells ∨ x ∈ (cert.modified.tile ⟨.B, a.first,
            a.second⟩).cells)) → (∀ x, x ∉ T.cells → x ∉ ring.cells → ∃ f : Nat → LatticeCell,
            Function.Injective f ∧ ∀ n, Relation.ReflTransGen (fun a b => FourNeighborAdjacent a
            b ∧ a ∉ ring.cells ∧ b ∉ ring.cells) x (f n)))))) ) := by
  classical
  intro q cfg C₀ T cert R ring union indexed central modified_subset original_owner x hxT hxR
  let safe := fun a : PeriodicSubtileIndex =>
    ¬ (a.first = 0 ∧ a.second = 0) ∧ ∀ i k, a ≠ P4630T1RingIndex i k
  let clean := fun z : LatticeCell => ∀ i k, z ∉ (R i k).cells
  have clean_iff (z : LatticeCell) : clean z ↔ z ∉ ring.cells := by
    simp only [union, not_exists, clean]
  obtain ⟨a, hxa, _⟩ := indexed x
  have ha : safe a := by
    refine ⟨fun hz => hxT ((central x).mpr ⟨a, hz, hxa⟩), ?_⟩
    intro i k he
    exact hxR ((union x).mpr ⟨i, k, modified_subset _ (he ▸ hxa)⟩)
  obtain ⟨f, hf, hwalk⟩ := P4630T1ExteriorWalks a ha
  have cell (n : Nat) : (cert.modified.tile (f n)).cells.Nonempty :=
    (LatticeTileGridStructure _ (cert.modified.tiles_are_disks (f n))).1.1
  let g : Nat → LatticeCell := fun n => Classical.choose (cell n)
  have hg (n : Nat) : g n ∈ (cert.modified.tile (f n)).cells :=
    Classical.choose_spec (cell n)
  have hgclean (n : Nat) : clean (g n) := by
    intro i k hn
    rcases original_owner _ (g n) hn with h | h
    · exact (hwalk n).2.1.2 i k ((indexed _).unique (hg n) h)
    · have he := congrArg PeriodicSubtileIndex.label ((indexed _).unique (hg n) h)
      rw [(hwalk n).1] at he
      cases he
  refine ⟨g, ?_, ?_⟩
  · intro n m he
    apply hf
    exact (indexed (g n)).unique (hg n) (by rw [he]; exact hg m)
  · intro n
    have h := P4630T1CellRouteLift q cfg C₀ T cert a (f n) ha
      (hwalk n).2.1 (hwalk n).2.2 x hxa ((clean_iff x).mpr hxR)
      (g n) (hg n) (hgclean n)
    exact Relation.ReflTransGen.mono
      (fun z w e => ⟨e.1, (clean_iff z).mp e.2.1,
        (clean_iff w).mp e.2.2⟩) x (g n) h

end TwelveParentGeometry

theorem BandTwelveParentSurround
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T) :
    ∃ R : Fin 3 → Fin 4 → ProtoTile, ∃ ring : ProtoTile,
      R 0 0 = TileTranslation (cert.P 0 true) (BandVectors.1 (q 0) (q 3)) ∧
      R 0 1 = TileTranslation (cert.P 0 true) (-BandVectors.1 (q 0) (q 2)) ∧
      R 0 2 = TileTranslation (cert.P 0 false) (-BandVectors.1 (q 0) (q 3)) ∧
      R 0 3 = TileTranslation (cert.P 0 false) (BandVectors.1 (q 0) (q 2)) ∧
      R 1 0 = TileTranslation (cert.P 1 true) (BandVectors.1 (q 0) (q 1)) ∧
      R 1 1 = TileTranslation (cert.P 1 true) (-BandVectors.1 (q 0) (q 3)) ∧
      R 1 2 = TileTranslation (cert.P 1 false) (-BandVectors.1 (q 0) (q 1)) ∧
      R 1 3 = TileTranslation (cert.P 1 false) (BandVectors.1 (q 0) (q 3)) ∧
      R 2 0 = TileTranslation (cert.P 2 true) (BandVectors.1 (q 0) (q 2)) ∧
      R 2 1 = TileTranslation (cert.P 2 true) (-BandVectors.1 (q 0) (q 1)) ∧
      R 2 2 = TileTranslation (cert.P 2 false) (-BandVectors.1 (q 0) (q 2)) ∧
      R 2 3 = TileTranslation (cert.P 2 false) (BandVectors.1 (q 0) (q 1)) ∧
      (∀ x, x ∈ ring.cells ↔ ∃ i k, x ∈ (R i k).cells) ∧
      QuarterTurnSymmetric ring ∧
      UniqueBoundedGridComplementComponent
        (ring.cells : Set GaussianInt) (T.cells : Set GaussianInt) := by
-- BODY
  classical
  let R := fun i k => SubtileOccurrenceInterpretation cert.P cert.u cert.v
    (P4630T1RingIndex i k)
  let ring : ProtoTile :=
    ⟨Finset.univ.biUnion (fun i : Fin 3 =>
      Finset.univ.biUnion (fun k : Fin 4 => (R i k).cells)), 0⟩
  have union (x : LatticeCell) : x ∈ ring.cells ↔ ∃ i k, x ∈ (R i k).cells := by
    simp [ring]
  have incoming := TwelveParentGeometry.incoming q cfg
  have flip := (VectorRecursionLaws q cfg.proper.1).2.2.2.2 cfg.proper
  have outgoing := TwelveParentGeometry.outgoing q incoming flip
  have third := TwelveParentGeometry.third q cfg C₀ T cert outgoing
  have values := TwelveParentGeometry.values q cfg C₀ T cert third
  have nonempty := TwelveParentGeometry.nonempty q cfg C₀ T cert union values
  obtain ⟨t, _, rotate⟩ := P4630T1ParentRotation q cfg C₀ T cert
  have rotation := TwelveParentGeometry.rotation q cfg C₀ T cert union t rotate
  have symmetric := P4630T1AffineCellSymmetry ring t nonempty rotation
  have indexed := PeriodicTileIndexedMultiplicityOne cert.modified
  obtain ⟨whole, whole_indices, whole_tile, _⟩ :=
    BandOrderedGeneralFinitePatches q cfg C₀ T cert
  have central (x : LatticeCell) := TwelveParentGeometry.central q cfg C₀ T cert whole
      whole_indices whole_tile x
  have lattice := TwelveParentGeometry.latticeAt243 q cfg C₀ T cert indexed whole whole_tile
  have precursor (x : LatticeCell) (hx : x ∈ cert.O.cells) :
      x ∈ (cert.P 0 false).cells :=
    (cert.minus_union x).mpr ⟨0, true, by simpa only [← cert.precursor_cells] using hx⟩
  have modified_subset (a : PeriodicSubtileIndex) := TwelveParentGeometry.modified_subset q cfg
      C₀ T cert a
  have original_owner (a : PeriodicSubtileIndex) (x : LatticeCell)
      (hx : x ∈ (SubtileOccurrenceInterpretation cert.P cert.u cert.v a).cells) :=
          TwelveParentGeometry.original_owner q cfg C₀ T cert precursor a x hx
  have external (i : Fin 3) (k : Fin 4) := TwelveParentGeometry.external i k
  have outside (a : PeriodicSubtileIndex) (ha : ¬ (a.first = 0 ∧ a.second = 0))
      (x : LatticeCell) (hx : x ∈ (cert.modified.tile a).cells) := TwelveParentGeometry.outside q
          cfg C₀ T cert indexed central a ha x hx
  have disjoint := TwelveParentGeometry.disjoint q cfg C₀ T cert union original_owner external
      outside
  have common_edge (U V : ProtoTile) (x y : LatticeCell)
      (hx : x ∈ U.cells) (hy : y ∈ V.cells) (h : FourNeighborAdjacent x y) :=
          TwelveParentGeometry.common_edge U V x y hx hy h
  have boundary := TwelveParentGeometry.boundary q cfg C₀ T cert union indexed central
      modified_subset common_edge
  have escape := TwelveParentGeometry.escape q cfg C₀ T cert union indexed central
      modified_subset original_owner
  refine ⟨R, ring, values.1, values.2.1, values.2.2.1, values.2.2.2.1,
    values.2.2.2.2.1, values.2.2.2.2.2.1, values.2.2.2.2.2.2.1,
    values.2.2.2.2.2.2.2.1, values.2.2.2.2.2.2.2.2.1,
    values.2.2.2.2.2.2.2.2.2.1, values.2.2.2.2.2.2.2.2.2.2.1,
    values.2.2.2.2.2.2.2.2.2.2.2, union, symmetric, ?_⟩
  exact P4630T1GridComplementCriterion _ _ T.cells.finite_toSet
    (LatticeTileGridStructure T lattice).1 disjoint boundary escape

end ApollonianSuperharmonic

end
