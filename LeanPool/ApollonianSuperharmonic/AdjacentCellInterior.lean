/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.OpenLatticeEdge
public import LeanPool.ApollonianSuperharmonic.TileRealization
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Interiors of adjacent lattice cells

Shared open-rectangle arguments adapted from Wesley Pegden's Apache-2.0
Trellis formalization of Levine–Pegden–Smart. No disk or circle hypotheses are needed.
-/

@[expose] public section

namespace ApollonianSuperharmonic.AdjacentCellInterior

/-- The common horizontal edge of two cells lies inside their tile realization. -/
theorem horizontal (U : ProtoTile) (z : GaussianInt)
    (hu : z ∈ U.cells) (hl : z - ⟨0, 1⟩ ∈ U.cells) :
    OpenLatticeEdge z (z + 1) ⊆ interior (TileRealization U) := by
  classical
  as_aux_lemma =>
  let R := Set.Ioo (z.re : ℝ) ((z.re : ℝ) + 1) ×ˢ
    Set.Ioo ((z.im : ℝ) - 1) ((z.im : ℝ) + 1)
  have hopen : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hsub : R ⊆ TileRealization U := by
    intro p hp
    rcases hp with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
    by_cases hside : p.2 ≤ (z.im : ℝ)
    · apply Set.mem_iUnion.mpr
      refine ⟨z - ⟨0, 1⟩, Set.mem_iUnion.mpr ⟨hl, ?_⟩⟩
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
      norm_num
      rw [GaussianInt.toComplex_def₂]
      change ((z.re : ℝ) ≤ p.1 ∧ (z.im : ℝ) ≤ p.2 + 1) ∧
        (p.1 ≤ (z.re : ℝ) + 1 ∧ p.2 ≤ (z.im : ℝ))
      constructor <;> constructor <;> linarith
    · apply Set.mem_iUnion.mpr
      refine ⟨z, Set.mem_iUnion.mpr ⟨hu, ?_⟩⟩
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
      constructor <;> constructor <;> linarith
  intro p hp
  apply hopen.subset_interior_iff.mpr hsub
  rcases hp with ⟨t, ht0, ht1, rfl⟩
  norm_num [R, GaussianRealPoint, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor <;> constructor <;> nlinarith

/-- The common vertical edge of two cells lies inside their tile realization. -/
theorem vertical (U : ProtoTile) (z : GaussianInt)
    (hr : z ∈ U.cells) (hl : z - 1 ∈ U.cells) :
    OpenLatticeEdge z (z + ⟨0, 1⟩) ⊆ interior (TileRealization U) := by
  classical
  as_aux_lemma =>
  let R := Set.Ioo ((z.re : ℝ) - 1) ((z.re : ℝ) + 1) ×ˢ
    Set.Ioo (z.im : ℝ) ((z.im : ℝ) + 1)
  have hopen : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hsub : R ⊆ TileRealization U := by
    intro p hp
    rcases hp with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
    by_cases hside : p.1 ≤ (z.re : ℝ)
    · apply Set.mem_iUnion.mpr
      refine ⟨z - 1, Set.mem_iUnion.mpr ⟨hl, ?_⟩⟩
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
      norm_num
      rw [GaussianInt.toComplex_def₂]
      change ((z.re : ℝ) ≤ p.1 + 1 ∧ (z.im : ℝ) ≤ p.2) ∧
        (p.1 ≤ (z.re : ℝ) ∧ p.2 ≤ (z.im : ℝ) + 1)
      constructor <;> constructor <;> linarith
    · apply Set.mem_iUnion.mpr
      refine ⟨z, Set.mem_iUnion.mpr ⟨hr, ?_⟩⟩
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
      constructor <;> constructor <;> linarith
  intro p hp
  apply hopen.subset_interior_iff.mpr hsub
  rcases hp with ⟨t, ht0, ht1, rfl⟩
  norm_num [R, GaussianRealPoint, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor <;> constructor <;> nlinarith

end ApollonianSuperharmonic.AdjacentCellInterior

end
