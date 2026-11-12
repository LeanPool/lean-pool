/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintEdges
public import LeanPool.ApollonianSuperharmonic.FourNeighborConnected
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import LeanPool.ApollonianSuperharmonic.P3381T1PolygonBoundary
public import LeanPool.ApollonianSuperharmonic.P3475T1UnitSegmentIntersection
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import LeanPool.ApollonianSuperharmonic.TileRealization

-- [TABLET NODE: P3475T1SquareUnionIdentification]

/-!
# P3475T1SquareUnionIdentification

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SquareUnionProof

private theorem edge_support :
    ∀ (T : ProtoTile), ∀ e ∈ BoundaryFootprintEdges T, ∃ z ∈ T.cells, e = {z,
        z + (1 : GaussianInt)} ∨ e = {z, z + ⟨(0 : ℤ), (1 : ℤ)⟩} ∨ e = {z + ⟨(0 : ℤ), (1 : ℤ)⟩,
        z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩} ∨ e = {z + (1 : GaussianInt),
        z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩} := by
  classical
  intro T e he
  rcases he with ⟨z, h | h⟩
  · rcases h.2 with hstatus | hstatus
    · exact ⟨z, hstatus.1, Or.inl h.1⟩
    · refine ⟨z - ⟨0, 1⟩, hstatus.2, Or.inr (Or.inr (Or.inl ?_))⟩
      rw [show z - ⟨0, 1⟩ + ⟨0, 1⟩ = z by abel,
        show z - ⟨0, 1⟩ + 1 + ⟨0, 1⟩ = z + 1 by abel]
      exact h.1
  · rcases h.2 with hstatus | hstatus
    · exact ⟨z, hstatus.1, Or.inr (Or.inl h.1)⟩
    · refine ⟨z - 1, hstatus.2, Or.inr (Or.inr (Or.inr ?_))⟩
      rw [show z - 1 + 1 = z by abel]
      exact h.1

private theorem edge_endpoint_square :
    ∀ (z : GaussianInt), ∀ (e : Finset GaussianInt), e = {z, z + (1 : GaussianInt)} ∨ e = {z,
        z + ⟨(0 : ℤ), (1 : ℤ)⟩} ∨ e = {z + ⟨(0 : ℤ), (1 : ℤ)⟩, z + (1 : GaussianInt) + ⟨(0 : ℤ),
        (1 : ℤ)⟩} ∨ e = {z + (1 : GaussianInt), z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩} → ∀ w
        ∈ e, GaussianRealPoint w ∈ ClosedSquareRealization z := by
  classical
  intro z e he w hw
  rcases he with h | h | h | h <;> rw [h] at hw
  all_goals simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  all_goals rcases hw with rfl | rfl
  all_goals simp [GaussianRealPoint, ClosedSquareRealization, Prod.le_def]

private theorem boundary_carrier_in_tile :
    ∀ (T : ProtoTile), ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (v : Fin (n + 3) →
        GaussianInt), (∀ (i : Fin (n + (3 : ℕ))), p.vertex i = GaussianRealPoint (v i)) →
        ((BoundaryFootprintEdges T = {e : Finset GaussianInt | ∃ (i : Fin (n + (3 : ℕ))), e =
        {v i, v (i + (1 : Fin (n + (3 : ℕ))))}}) → (
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
    (∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges T) → (∃ z : GaussianInt, z ∈ T.cells
        ∧ (e = {z, z + 1} ∨ e = {z, z + ⟨0, 1⟩} ∨ e = {z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩} ∨ e = {z + 1,
        z + 1 + ⟨0, 1⟩}))) → ((∀ (z : GaussianInt), ∀ (e : Finset GaussianInt), (e = {z, z + 1} ∨
        e = {z, z + ⟨0, 1⟩} ∨ e = {z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩} ∨ e = {z + 1, z + 1 + ⟨0, 1⟩}) →
        (∀ (w : GaussianInt), (w ∈ e) → (GaussianRealPoint w ∈ ClosedSquareRealization z))) → (C
        ⊆ TileRealization T)))) := by
  classical
  intro T n p v hvertex hedges C edge_support edge_endpoint_square q hq
  change q ∈ ⋃ i, segment ℝ (p.vertex i) (p.vertex (i + 1)) at hq
  obtain ⟨i, hq⟩ := Set.mem_iUnion.mp hq
  have he : ({v i, v (i + 1)} : Finset GaussianInt) ∈ BoundaryFootprintEdges T := by
    rw [hedges]
    exact ⟨i, rfl⟩
  obtain ⟨z, hz, hside⟩ := edge_support _ he
  have hvi : v i ∈ ({v i, v (i + 1)} : Finset GaussianInt) := by simp
  have hvi1 : v (i + 1) ∈ ({v i, v (i + 1)} : Finset GaussianInt) := by simp
  have hpvi : p.vertex i ∈ ClosedSquareRealization z := by
    rw [hvertex]
    exact edge_endpoint_square z _ hside (v i) hvi
  have hpvi1 : p.vertex (i + 1) ∈ ClosedSquareRealization z := by
    rw [hvertex]
    exact edge_endpoint_square z _ hside (v (i + 1)) hvi1
  have hseg : segment ℝ (p.vertex i) (p.vertex (i + 1)) ⊆
      ClosedSquareRealization z := by
    rw [segment_eq_image]
    rintro q ⟨t, ht, rfl⟩
    simp only [Set.mem_Icc] at ht
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hpvi hpvi1 ⊢
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      smul_eq_mul]
    constructor <;> constructor <;> nlinarith [ht.1, ht.2]
  rw [TileRealization]
  exact Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨hz, hseg hq⟩⟩

private theorem segment_stays_on_one_side :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (U : Set (Real × Real)), ∀ (V : Set (Real
        × Real)), (IsOpen U) → ((IsOpen V) → ((Disjoint U V) → ((U ∪ V = (⋃ (i : Fin (n + (3 :
        ℕ))), segment ℝ (p.vertex i) (p.vertex (i + (1 : Fin (n + (3 : ℕ))))))ᶜ) → (
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
    ∀ (a : ℝ × ℝ), ∀ (b : ℝ × ℝ), segment ℝ a b ⊆ Cᶜ → segment ℝ a b ⊆ U ∨ segment ℝ a b ⊆ V))))
        := by
  classical
  intro n p U V hUopen hVopen hdisjoint hcover C a b havoid
  have hpre : IsPreconnected (segment ℝ a b) := by
    exact (convex_segment (𝕜 := ℝ) a b).isPreconnected
  apply hpre.subset_or_subset hUopen hVopen hdisjoint
  intro q hq
  have hq' : q ∈ Cᶜ := havoid hq
  rw [← hcover] at hq'
  exact hq'

private theorem east_center_segment_outside :
    ∀ (T : ProtoTile),
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    ∀ a ∉ T.cells, a + (1 : GaussianInt) ∉ T.cells → segment ℝ (cellCenter a) (cellCenter (a + (1
        : GaussianInt))) ⊆ (TileRealization T)ᶜ := by
  classical
  intro T cellCenter a ha hb q hq htile
  rw [segment_eq_image] at hq
  rcases hq with ⟨t, ht, rfl⟩
  simp only [Set.mem_Icc] at ht
  simp only [TileRealization, Set.mem_iUnion] at htile
  rcases htile with ⟨c, hc, hq⟩
  simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hq
  simp? [cellCenter,
    add_zero,
    smul_eq_mul] at hq
  simp only [GaussianInt.toComplex_def] at hq
  norm_num [Complex.mul_re, Complex.mul_im] at hq
  have hreC : (GaussianInt.toComplex c).re = (c.re : Real) := by
    exact (GaussianInt.intCast_re c).symm
  have himC : (GaussianInt.toComplex c).im = (c.im : Real) := by
    exact (GaussianInt.intCast_im c).symm
  have hreA : (GaussianInt.toComplex a).re = (a.re : Real) := by
    exact (GaussianInt.intCast_re a).symm
  have himA : (GaussianInt.toComplex a).im = (a.im : Real) := by
    exact (GaussianInt.intCast_im a).symm
  rw [hreC, himC, hreA, himA] at hq
  rcases hq with ⟨⟨hxr, hxi⟩, ⟨hxr', hxi'⟩⟩
  have hrlo : a.re ≤ c.re := by
    have hlt : (a.re : Real) < (c.re : Real) + 1 := by linarith
    have hlt' : a.re < c.re + 1 := by exact_mod_cast hlt
    omega
  have hrhi : c.re ≤ a.re + 1 := by
    have hlt : (c.re : Real) < (a.re : Real) + 2 := by linarith
    have hlt' : c.re < a.re + 2 := by exact_mod_cast hlt
    omega
  have himlo : c.im ≤ a.im := by
    have hlt : (c.im : Real) < (a.im : Real) + 1 := by linarith
    have hlt' : c.im < a.im + 1 := by exact_mod_cast hlt
    omega
  have himhi : a.im ≤ c.im := by
    have hlt : (a.im : Real) < (c.im : Real) + 1 := by linarith
    have hlt' : a.im < c.im + 1 := by exact_mod_cast hlt
    omega
  have hIm : c.im = a.im := by omega
  have hRe : c.re = a.re ∨ c.re = a.re + 1 := by omega
  rcases hRe with hRe | hRe
  · have hcEq : c = a := by
      apply Zsqrtd.ext <;> simp [hRe, hIm]
    exact ha (hcEq ▸ hc)
  · have hcEq : c = a + 1 := by
      apply Zsqrtd.ext <;> simp [hRe, hIm]
    exact hb (hcEq ▸ hc)

private theorem north_center_segment_outside :
    ∀ (T : ProtoTile),
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    ∀ a ∉ T.cells, a + ⟨(0 : ℤ), (1 : ℤ)⟩ ∉ T.cells → segment ℝ (cellCenter a) (cellCenter (a +
        ⟨(0 : ℤ), (1 : ℤ)⟩)) ⊆ (TileRealization T)ᶜ := by
  classical
  intro T cellCenter a ha hb q hq htile
  rw [segment_eq_image] at hq
  rcases hq with ⟨t, ht, rfl⟩
  simp only [Set.mem_Icc] at ht
  simp only [TileRealization, Set.mem_iUnion] at htile
  rcases htile with ⟨c, hc, hq⟩
  simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hq
  simp? [cellCenter,
    Int.cast_zero, Int.cast_one, add_zero,
    smul_eq_mul] at hq
  simp only [GaussianInt.toComplex_def] at hq
  norm_num [Complex.mul_re, Complex.mul_im] at hq
  have hreC : (GaussianInt.toComplex c).re = (c.re : Real) :=
    (GaussianInt.intCast_re c).symm
  have himC : (GaussianInt.toComplex c).im = (c.im : Real) :=
    (GaussianInt.intCast_im c).symm
  have hreA : (GaussianInt.toComplex a).re = (a.re : Real) :=
    (GaussianInt.intCast_re a).symm
  have himA : (GaussianInt.toComplex a).im = (a.im : Real) :=
    (GaussianInt.intCast_im a).symm
  rw [hreC, himC, hreA, himA] at hq
  rcases hq with ⟨⟨hxr, hxi⟩, ⟨hxr', hxi'⟩⟩
  have hrlo : a.re ≤ c.re := by
    have hlt : (a.re : Real) < (c.re : Real) + 1 := by linarith
    have hlt' : a.re < c.re + 1 := by exact_mod_cast hlt
    omega
  have hrhi : c.re ≤ a.re := by
    have hlt : (c.re : Real) < (a.re : Real) + 1 := by linarith
    have hlt' : c.re < a.re + 1 := by exact_mod_cast hlt
    omega
  have himlo : a.im ≤ c.im := by
    have hlt : (a.im : Real) < (c.im : Real) + 1 := by linarith
    have hlt' : a.im < c.im + 1 := by exact_mod_cast hlt
    omega
  have himhi : c.im ≤ a.im + 1 := by
    have hlt : (c.im : Real) < (a.im : Real) + 2 := by linarith
    have hlt' : c.im < a.im + 2 := by exact_mod_cast hlt
    omega
  have hRe : c.re = a.re := by omega
  have hIm : c.im = a.im ∨ c.im = a.im + 1 := by omega
  rcases hIm with hIm | hIm
  · have hcEq : c = a := by
      apply Zsqrtd.ext <;> simp [hRe, hIm]
    exact ha (hcEq ▸ hc)
  · have hcEq : c = a + ⟨0, 1⟩ := by
      apply Zsqrtd.ext <;> simp [hRe, hIm]
    exact hb (hcEq ▸ hc)

private theorem complement_adjacent_segment_avoid :
    ∀ (T : ProtoTile), ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
    (C ⊆ TileRealization T) → (
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    (∀ (a : GaussianInt), (a ∉ T.cells) → ((a + 1 ∉ T.cells) → (segment ℝ (cellCenter a)
        (cellCenter (a + 1)) ⊆ (TileRealization T)ᶜ))) → ((∀ (a : GaussianInt), (a ∉ T.cells) →
        ((a + ⟨0, 1⟩ ∉ T.cells) → (segment ℝ (cellCenter a) (cellCenter (a + ⟨0, 1⟩)) ⊆
        (TileRealization T)ᶜ))) → (∀ (a : GaussianInt), ∀ (b : GaussianInt), FourNeighborAdjacent
        a b → a ∉ T.cells → b ∉ T.cells → segment ℝ (cellCenter a) (cellCenter b) ⊆ Cᶜ))) := by
  classical
  intro T n p C boundary_carrier_in_tile cellCenter east_center_segment_outside
      north_center_segment_outside a b hab ha hb
  have houtTile : segment ℝ (cellCenter a) (cellCenter b) ⊆
      (TileRealization T)ᶜ := by
    rcases hab with h | h | h | h
    · simpa [h] using east_center_segment_outside a ha (by simpa [h] using hb)
    · have he : b + 1 = a := by rw [h]; simp
      have hrev := east_center_segment_outside b hb (by simpa [he] using ha)
      simpa [segment_symm, he] using hrev
    · simpa [h] using north_center_segment_outside a ha (by simpa [h] using hb)
    · have he : b + ⟨0, 1⟩ = a := by rw [h]; simp
      have hrev := north_center_segment_outside b hb (by simpa [he] using ha)
      simpa [segment_symm, he] using hrev
  intro q hq hqC
  exact houtTile hq (boundary_carrier_in_tile hqC)

private theorem center_not_tile :
    ∀ (T : ProtoTile),
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    ∀ a ∉ T.cells, cellCenter a ∉ TileRealization T := by
  classical
  intro T cellCenter a ha htile
  simp only [TileRealization, Set.mem_iUnion] at htile
  obtain ⟨c, hc, hq⟩ := htile
  simp? [ClosedSquareRealization, cellCenter, Prod.le_def] at hq
  have hreC : (GaussianInt.toComplex c).re = (c.re : Real) :=
    (GaussianInt.intCast_re c).symm
  have himC : (GaussianInt.toComplex c).im = (c.im : Real) :=
    (GaussianInt.intCast_im c).symm
  have hreA : (GaussianInt.toComplex a).re = (a.re : Real) :=
    (GaussianInt.intCast_re a).symm
  have himA : (GaussianInt.toComplex a).im = (a.im : Real) :=
    (GaussianInt.intCast_im a).symm
  rw [hreC, himC, hreA, himA] at hq
  rcases hq with ⟨⟨hxr, hxi⟩, ⟨hxr', hxi'⟩⟩
  have hrlo : a.re ≤ c.re := by
    have hlt : (a.re : Real) < (c.re : Real) + 1 := by linarith
    have hlt' : a.re < c.re + 1 := by exact_mod_cast hlt
    omega
  have hrhi : c.re ≤ a.re := by
    have hlt : (c.re : Real) < (a.re : Real) + 1 := by linarith
    have hlt' : c.re < a.re + 1 := by exact_mod_cast hlt
    omega
  have himlo : a.im ≤ c.im := by
    have hlt : (a.im : Real) < (c.im : Real) + 1 := by linarith
    have hlt' : a.im < c.im + 1 := by exact_mod_cast hlt
    omega
  have himhi : c.im ≤ a.im := by
    have hlt : (c.im : Real) < (a.im : Real) + 1 := by linarith
    have hlt' : c.im < a.im + 1 := by exact_mod_cast hlt
    omega
  have hcEq : c = a := by
    apply Zsqrtd.ext <;> omega
  exact ha (hcEq ▸ hc)

private theorem center_in_domain :
    ∀ (T : ProtoTile), ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (U : Set (Real ×
        Real)), ∀ (V : Set (Real × Real)), (U ∪ V = (⋃ (i : Fin (n + (3 : ℕ))), segment ℝ
        (p.vertex i) (p.vertex (i + (1 : Fin (n + (3 : ℕ))))))ᶜ) → (
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
    (C ⊆ TileRealization T) → (
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    (∀ (a : GaussianInt), (a ∉ T.cells) → (cellCenter a ∉ TileRealization T)) → (∀ a ∉ T.cells,
        cellCenter a ∈ U ∨ cellCenter a ∈ V))) := by
  classical
  intro T n p U V hcover C boundary_carrier_in_tile cellCenter center_not_tile a ha
  have hnotTile := center_not_tile a ha
  have hnotC : cellCenter a ∉ C := by
    intro hC
    exact hnotTile (boundary_carrier_in_tile hC)
  have hCcompl : cellCenter a ∈ Cᶜ := hnotC
  have hUV : cellCenter a ∈ U ∪ V := by
    rw [← hcover] at hCcompl
    exact hCcompl
  exact hUV

private theorem complement_adjacent_same_domain :
    ∀ (T : ProtoTile), ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (U : Set (Real ×
        Real)), ∀ (V : Set (Real × Real)), (Disjoint U V) → (
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
    (∀ (a : Real × Real), ∀ (b : Real × Real), (segment ℝ a b ⊆ Cᶜ) → (segment ℝ a b ⊆ U ∨
        segment ℝ a b ⊆ V)) → (
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    (∀ (a : GaussianInt), ∀ (b : GaussianInt), (FourNeighborAdjacent a b) → ((a ∉ T.cells) → ((b
        ∉ T.cells) → (segment ℝ (cellCenter a) (cellCenter b) ⊆ Cᶜ)))) → (∀ (a : GaussianInt), ∀
        (b : GaussianInt), FourNeighborAdjacent a b → a ∉ T.cells → b ∉ T.cells → (cellCenter a ∈
        U ↔ cellCenter b ∈ U)))) := by
  classical
  intro T n p U V hdisjoint C segment_stays_on_one_side cellCenter
      complement_adjacent_segment_avoid a b hab ha hb
  have havoid := complement_adjacent_segment_avoid a b hab ha hb
  rcases segment_stays_on_one_side _ _ havoid with hU | hV
  · constructor <;> intro _
    · exact hU (right_mem_segment ℝ _ _)
    · exact hU (left_mem_segment ℝ _ _)
  · constructor
    · intro haU
      have haV : cellCenter a ∈ V := hV (left_mem_segment ℝ _ _)
      have hbV : cellCenter b ∈ V := hV (right_mem_segment ℝ _ _)
      exact False.elim ((Set.disjoint_left.mp hdisjoint) haU haV)
    · intro hbU
      have hbV : cellCenter b ∈ V := hV (right_mem_segment ℝ _ _)
      have haV : cellCenter a ∈ V := hV (left_mem_segment ℝ _ _)
      exact False.elim ((Set.disjoint_left.mp hdisjoint) hbU hbV)

private theorem list_center_transport :
    ∀ (T : ProtoTile), ∀ (U : Set (Real × Real)),
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    (∀ (a : GaussianInt), ∀ (b : GaussianInt), (FourNeighborAdjacent a b) → ((a ∉ T.cells) → ((b
        ∉ T.cells) → ((cellCenter a ∈ U ↔ cellCenter b ∈ U))))) → (∀ (l : List GaussianInt), ∀ (x
        : GaussianInt), ∀ (y : GaussianInt), l.head? = some x → l.getLast? = some y → (∀ z ∈ l, z
        ∉ T.cells) → (∀ a, ∀ b, ∀ l₁, ∀ l₂, l = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a b) →
        (cellCenter x ∈ U ↔ cellCenter y ∈ U)) := by
  classical
  intro T U cellCenter complement_adjacent_same_domain l x y
  induction l using List.twoStepInduction generalizing x y with
  | nil =>
      intro hx hy _ _
      simp at hx
  | singleton a =>
      intro hx hy _ _
      simp? at hx hy
      subst x
      subst y
      exact Iff.rfl
  | cons_cons a b tail ihTail ihCons =>
      intro hx hy hnodes hsteps
      have hxA : x = a := by simpa using hx.symm
      subst x
      have hy' : (b :: tail).getLast? = some y := by simpa using hy
      have hab : FourNeighborAdjacent a b := by
        apply hsteps a b [] tail
        simp
      have ha : a ∉ T.cells := hnodes a (by simp)
      have hb : b ∉ T.cells := hnodes b (by simp)
      have hfirst := complement_adjacent_same_domain a b hab ha hb
      have hnodes' : ∀ z ∈ b :: tail, z ∉ T.cells := by
        intro z hz
        exact hnodes z (by simp [hz])
      have hsteps' : ∀ a' b' l₁ l₂,
          b :: tail = l₁ ++ a' :: b' :: l₂ → FourNeighborAdjacent a' b' := by
        intro a' b' l₁ l₂ hEq
        apply hsteps a' b' (a :: l₁) l₂
        simpa using congrArg (fun q => a :: q) hEq
      have htail := ihCons b b y (by simp) hy' hnodes' hsteps'
      exact hfirst.trans htail

private theorem farComplementCell :
    ∀ (T : ProtoTile), (FourNeighborConnected (↑T.cells : Set LatticeCell)) → (∀ (U : Set (Real ×
        Real)), (Bornology.IsBounded U) → (
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    ∃ z : GaussianInt, z ∉ T.cells ∧ cellCenter z ∉ U)) := by
  classical
  intro T hinside U hUbounded cellCenter
  obtain ⟨z₀, hz₀, hmax⟩ := T.cells.exists_max_image (fun z => z.re) hinside.1
  obtain ⟨R, hR⟩ := (LipschitzWith.prod_fst.isBounded_image hUbounded).subset_closedBall
    (0 : Real)
  let k : Int := max z₀.re (Int.floor R) + 2
  let z : GaussianInt := ⟨k, 0⟩
  have hzk : z.re > z₀.re := by
    have hm : z₀.re ≤ max z₀.re (Int.floor R) := le_max_left _ _
    simp [z, k]
    omega
  have hnot : z ∉ T.cells := by
    intro hz
    have hle := hmax z hz
    exact (not_lt_of_ge hle) hzk
  have hfloor : Int.floor R < k := by
    have hm : Int.floor R ≤ max z₀.re (Int.floor R) := le_max_right _ _
    simp [k]
    omega
  have hcoord : R < (cellCenter z).1 := by
    dsimp [cellCenter, z]
    have hfloorK : ((Int.floor R + 1 : Int) : Real) ≤ (k : Real) := by
      have : Int.floor R + 1 ≤ k := by omega
      exact_mod_cast this
    calc
      R < (Int.floor R : Real) + 1 := Int.lt_floor_add_one R
      _ ≤ (k : Real) := by
        simpa only [Int.cast_add, Int.cast_one] using hfloorK
      _ < (k : Real) + (1 / 2 : Real) := by norm_num
  have hnotU : cellCenter z ∉ U := by
    intro hzU
    have hmem : (cellCenter z).1 ∈ Prod.fst '' U :=
      ⟨cellCenter z, hzU, rfl⟩
    have hball := hR hmem
    have hdist : dist ((cellCenter z).1) 0 ≤ R := by
      simpa [Metric.mem_closedBall] using hball
    have hle : (cellCenter z).1 ≤ R := by
      have habs : |(cellCenter z).1| ≤ R := by simpa [Real.dist_eq] using hdist
      exact (abs_le.mp habs).2
    exact (not_lt_of_ge hle) hcoord
  exact ⟨z, hnot, hnotU⟩

private theorem pair_eq_cases :
    ∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (c : GaussianInt), ∀ (d : GaussianInt), c ≠ d →
        ({a, b} : Finset GaussianInt) = {c, d} → a = c ∧ b = d ∨ a = d ∧ b = c := by
  classical
  intro a b c d hcd hpair
  have ha : a = c ∨ a = d := by
    have hm : a ∈ ({c, d} : Finset GaussianInt) := by
      rw [← hpair]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases ha with hac | had
  · have hd : d ∈ ({a, b} : Finset GaussianInt) := by
      rw [hpair]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with hda | hdb
    · exact False.elim (hcd (hac ▸ hda).symm)
    · exact Or.inl ⟨hac, hdb.symm⟩
  · have hc : c ∈ ({a, b} : Finset GaussianInt) := by
      rw [hpair]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with hca | hcb
    · exact False.elim (hcd (hca.trans had))
    · exact Or.inr ⟨had, hcb.symm⟩

private theorem boundary_side_segment_in_C :
    ∀ (T : ProtoTile), ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (v : Fin (n + 3) →
        GaussianInt), (∀ (i : Fin (n + (3 : ℕ))), p.vertex i = GaussianRealPoint (v i)) →
        ((BoundaryFootprintEdges T = {e : Finset GaussianInt | ∃ (i : Fin (n + (3 : ℕ))), e =
        {v i, v (i + (1 : Fin (n + (3 : ℕ))))}}) → (
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
    (∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (c : GaussianInt), ∀ (d : GaussianInt), (c ≠ d)
        → ((({a, b} : Finset GaussianInt) = {c, d}) → ((a = c ∧ b = d) ∨ (a = d ∧ b = c)))) → (∀
        e ∈ BoundaryFootprintEdges T, ∀ (a : GaussianInt), ∀ (b : GaussianInt), e = {a, b} → a ≠
        b → ∀ q ∈ segment ℝ (GaussianRealPoint a) (GaussianRealPoint b), q ∈ C))) := by
  classical
  intro T n p v hvertex hedges C pair_eq_cases e he a b hab habne q hq
  rw [hedges] at he
  obtain ⟨i, hi⟩ := he
  have hneq : v i ≠ v (i + 1) := by
    intro h
    have heq : ({v i, v (i + 1)} : Finset GaussianInt) = {a, b} := hi.symm.trans hab
    rw [h] at heq
    have hcard : ({a, b} : Finset GaussianInt).card = 2 := by simp [habne]
    rw [← heq] at hcard
    simp at hcard
  have hp := pair_eq_cases (v i) (v (i + 1)) a b habne (hi.symm.trans hab)
  rcases hp with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · subst a; subst b
    exact Set.mem_iUnion.mpr ⟨i, by simpa [hvertex] using hq⟩
  · subst a; subst b
    rw [segment_symm] at hq
    exact Set.mem_iUnion.mpr ⟨i, by simpa [hvertex] using hq⟩

private theorem east_side_not_boundary :
    ∀ (T : ProtoTile), (∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (c : GaussianInt), ∀ (d :
        GaussianInt), (c ≠ d) → ((({a, b} : Finset GaussianInt) = {c, d}) → ((a = c ∧ b = d) ∨ (a
        = d ∧ b = c)))) → (∀ (a : GaussianInt), (a ∈ T.cells ↔ a + (1 : GaussianInt) ∈ T.cells) →
        {a + (1 : GaussianInt), a + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩} ∉
        BoundaryFootprintEdges T) := by
  classical
  intro T pair_eq_cases a hsame he
  rcases he with ⟨z, hside | hside⟩
  · have hp := pair_eq_cases z (z + 1) (a + 1) (a + 1 + ⟨0, 1⟩)
      (by intro h; have := congrArg (fun x : GaussianInt => x.im) h; simp at this)
      hside.1.symm
    rcases hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have hr₁ := congrArg (fun x : GaussianInt => x.re) h₁
      have hr₂ := congrArg (fun x : GaussianInt => x.re) h₂
      simp at hr₁ hr₂
      omega
    · have hr₁ := congrArg (fun x : GaussianInt => x.re) h₁
      have hr₂ := congrArg (fun x : GaussianInt => x.re) h₂
      simp at hr₁ hr₂
      omega
  · have hp := pair_eq_cases z (z + ⟨0, 1⟩) (a + 1) (a + 1 + ⟨0, 1⟩)
      (by intro h; have := congrArg (fun x : GaussianInt => x.im) h; simp at this)
      hside.1.symm
    rcases hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have hz : z = a + 1 := by
        exact h₁
      subst z
      rcases hside.2 with hstatus | hstatus
      · have ha : a ∈ T.cells := hsame.mpr hstatus.1
        have hna : a ∉ T.cells := by simpa using hstatus.2
        exact hna ha
      · have ha : a ∈ T.cells := by simpa using hstatus.2
        exact hstatus.1 (hsame.mp ha)
    · have hi₁ := congrArg (fun x : GaussianInt => x.im) h₁
      have hi₂ := congrArg (fun x : GaussianInt => x.im) h₂
      simp at hi₁ hi₂
      omega

private theorem north_side_not_boundary :
    ∀ (T : ProtoTile), (∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (c : GaussianInt), ∀ (d :
        GaussianInt), (c ≠ d) → ((({a, b} : Finset GaussianInt) = {c, d}) → ((a = c ∧ b = d) ∨ (a
        = d ∧ b = c)))) → (∀ (a : GaussianInt), (a ∈ T.cells ↔ a + ⟨(0 : ℤ), (1 : ℤ)⟩ ∈ T.cells)
        → {a + ⟨(0 : ℤ), (1 : ℤ)⟩, a + ⟨(0 : ℤ), (1 : ℤ)⟩ + (1 : GaussianInt)} ∉
        BoundaryFootprintEdges T) := by
  classical
  intro T pair_eq_cases a hsame he
  rcases he with ⟨z, hside | hside⟩
  · have hp := pair_eq_cases z (z + 1) (a + ⟨0, 1⟩) (a + ⟨0, 1⟩ + 1)
      (by intro h; have := congrArg (fun x : GaussianInt => x.re) h; simp at this)
      hside.1.symm
    rcases hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have hz : z = a + ⟨0, 1⟩ := h₁
      subst z
      rcases hside.2 with hstatus | hstatus
      · have ha : a ∈ T.cells := hsame.mpr hstatus.1
        have hna : a ∉ T.cells := by simpa using hstatus.2
        exact hna ha
      · have ha : a ∈ T.cells := by simpa using hstatus.2
        exact hstatus.1 (hsame.mp ha)
    · have hr₁ := congrArg (fun x : GaussianInt => x.re) h₁
      have hr₂ := congrArg (fun x : GaussianInt => x.re) h₂
      simp at hr₁ hr₂
      omega
  · have hp := pair_eq_cases z (z + ⟨0, 1⟩) (a + ⟨0, 1⟩) (a + ⟨0, 1⟩ + 1)
      (by intro h; have := congrArg (fun x : GaussianInt => x.re) h; simp at this)
      hside.1.symm
    rcases hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have hi₁ := congrArg (fun x : GaussianInt => x.im) h₁
      have hi₂ := congrArg (fun x : GaussianInt => x.im) h₂
      simp at hi₁ hi₂
      omega
    · have hr₁ := congrArg (fun x : GaussianInt => x.re) h₁
      have hr₂ := congrArg (fun x : GaussianInt => x.re) h₂
      simp at hr₁ hr₂
      omega

private theorem boundary_edge_adjacent :
    ∀ (T : ProtoTile), ∀ (n : Nat), ∀ (v : Fin (n + 3) → GaussianInt), (∀ (e : Finset
        GaussianInt), (e ∈ BoundaryFootprintEdges T) → (∃ z : GaussianInt, z ∈ T.cells ∧ (e = {z,
        z + 1} ∨ e = {z, z + ⟨0, 1⟩} ∨ e = {z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩} ∨ e = {z + 1, z + 1 + ⟨0,
        1⟩}))) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (c : GaussianInt), ∀ (d :
        GaussianInt), (c ≠ d) → ((({a, b} : Finset GaussianInt) = {c, d}) → ((a = c ∧ b = d) ∨ (a
        = d ∧ b = c)))) → (∀ (i : Fin (n + (3 : ℕ))), {v i, v (i + (1 : Fin (n + (3 : ℕ))))} ∈
        BoundaryFootprintEdges T → FourNeighborAdjacent (v i) (v (i + (1 : Fin (n + (3 : ℕ)))))))
        := by
  classical
  intro T n v edge_support pair_eq_cases i he
  obtain ⟨z, _, hside⟩ := edge_support _ he
  rcases hside with hside | hside | hside | hside
  · have hp := pair_eq_cases (v i) (v (i + 1)) z (z + 1)
      (by intro h; have := congrArg (fun x : GaussianInt => x.re) h; simp at this)
      hside
    rcases hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
      simp [FourNeighborAdjacent, h₁, h₂]
  · have hp := pair_eq_cases (v i) (v (i + 1)) z (z + ⟨0, 1⟩)
      (by intro h; have := congrArg (fun x : GaussianInt => x.im) h; simp at this)
      hside
    rcases hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
      simp [FourNeighborAdjacent, h₁, h₂]
  · let w := z + ⟨0, 1⟩
    have hp := pair_eq_cases (v i) (v (i + 1)) w (w + 1)
      (by intro h; have := congrArg (fun x : GaussianInt => x.re) h; simp at this)
      (by simpa [w, add_assoc, add_comm, add_left_comm] using hside)
    rcases hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
      simp [FourNeighborAdjacent, h₁, h₂]
  · let w := z + 1
    have hp := pair_eq_cases (v i) (v (i + 1)) w (w + ⟨0, 1⟩)
      (by intro h; have := congrArg (fun x : GaussianInt => x.im) h; simp at this)
      (by simpa [w, add_assoc, add_comm, add_left_comm] using hside)
    rcases hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
      simp [FourNeighborAdjacent, h₁, h₂]

private theorem boundary_carrier_has_integer_coordinate :
    ∀ (T : ProtoTile), ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (v : Fin (n + 3) →
        GaussianInt), (∀ (i : Fin (n + (3 : ℕ))), p.vertex i = GaussianRealPoint (v i)) →
        ((BoundaryFootprintEdges T = {e : Finset GaussianInt | ∃ (i : Fin (n + (3 : ℕ))), e =
        {v i, v (i + (1 : Fin (n + (3 : ℕ))))}}) → (
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
    (∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges T) → (∃ z : GaussianInt, z ∈ T.cells
        ∧ (e = {z, z + 1} ∨ e = {z, z + ⟨0, 1⟩} ∨ e = {z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩} ∨ e = {z + 1,
        z + 1 + ⟨0, 1⟩}))) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (c : GaussianInt), ∀
        (d : GaussianInt), (c ≠ d) → ((({a, b} : Finset GaussianInt) = {c, d}) → ((a = c ∧ b = d)
        ∨ (a = d ∧ b = c)))) → ((∀ (z : GaussianInt), ∀ (q : Real × Real), (q ∈ segment ℝ
        (GaussianRealPoint z) (GaussianRealPoint (z + 1))) → (q.2 = (z.im : Real))) → ((∀ (z :
        GaussianInt), ∀ (q : Real × Real), (q ∈ segment ℝ (GaussianRealPoint z)
        (GaussianRealPoint (z + ⟨0, 1⟩))) → (q.1 = (z.re : Real))) → (∀ q ∈ C, (∃ (m : ℤ), q.1 =
        (↑m : ℝ)) ∨ ∃ (m : ℤ), q.2 = (↑m : ℝ))))))) := by
  classical
  intro T n p v hvertex hedges C edge_support pair_eq_cases horizontal_segment_y
      vertical_segment_x q hq
  change q ∈ ⋃ i, segment ℝ (p.vertex i) (p.vertex (i + 1)) at hq
  obtain ⟨i, hq⟩ := Set.mem_iUnion.mp hq
  have he : ({v i, v (i + 1)} : Finset GaussianInt) ∈ BoundaryFootprintEdges T := by
    rw [hedges]
    exact ⟨i, rfl⟩
  obtain ⟨z, _, hside⟩ := edge_support _ he
  rw [hvertex i, hvertex (i + 1)] at hq
  rcases hside with hside | hside | hside | hside
  · have hpair := pair_eq_cases (v i) (v (i + 1)) z (z + 1)
      (by intro h; have := congrArg (fun x : GaussianInt => x.re) h; simp at this)
      hside
    rcases hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂] at hq
      exact Or.inr ⟨z.im, horizontal_segment_y z q hq⟩
    · rw [h₁, h₂] at hq
      rw [segment_symm] at hq
      exact Or.inr ⟨z.im, horizontal_segment_y z q hq⟩
  · have hpair := pair_eq_cases (v i) (v (i + 1)) z (z + ⟨0, 1⟩)
      (by intro h; have := congrArg (fun x : GaussianInt => x.im) h; simp at this)
      hside
    rcases hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂] at hq
      exact Or.inl ⟨z.re, vertical_segment_x z q hq⟩
    · rw [h₁, h₂] at hq
      rw [segment_symm] at hq
      exact Or.inl ⟨z.re, vertical_segment_x z q hq⟩
  · let w : GaussianInt := z + ⟨0, 1⟩
    have hpair := pair_eq_cases (v i) (v (i + 1)) w (w + 1)
      (by intro h; have := congrArg (fun x : GaussianInt => x.re) h; simp at this)
      (by simpa [w, add_assoc, add_comm, add_left_comm] using hside)
    rcases hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂] at hq
      exact Or.inr ⟨z.im + 1, by
        simpa [w, Zsqrtd.im_add, Zsqrtd.im_one, add_zero] using
          (horizontal_segment_y w q hq)⟩
    · rw [h₁, h₂] at hq
      rw [segment_symm] at hq
      exact Or.inr ⟨z.im + 1, by
        simpa [w, Zsqrtd.im_add, Zsqrtd.im_one, add_zero] using
          (horizontal_segment_y w q hq)⟩
  · let w : GaussianInt := z + 1
    have hpair := pair_eq_cases (v i) (v (i + 1)) w (w + ⟨0, 1⟩)
      (by intro h; have := congrArg (fun x : GaussianInt => x.im) h; simp at this)
      (by simpa [w, add_assoc, add_comm, add_left_comm] using hside)
    rcases hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂] at hq
      exact Or.inl ⟨z.re + 1, by simpa [w, Zsqrtd.re_add, Zsqrtd.re_one, Int.cast_add,
          Int.cast_one] using vertical_segment_x w q hq⟩
    · rw [h₁, h₂] at hq
      rw [segment_symm] at hq
      exact Or.inl ⟨z.re + 1, by simpa [w, Zsqrtd.re_add, Zsqrtd.re_one, Int.cast_add,
          Int.cast_one] using vertical_segment_x w q hq⟩

private theorem east_same_center_segment_avoids :
    ∀ (T : ProtoTile), ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (v : Fin (n + 3) →
        GaussianInt), (∀ (i : Fin (n + (3 : ℕ))), p.vertex i = GaussianRealPoint (v i)) →
        ((BoundaryFootprintEdges T = {e : Finset GaussianInt | ∃ (i : Fin (n + (3 : ℕ))), e =
        {v i, v (i + (1 : Fin (n + (3 : ℕ))))}}) → (
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    (∀ (a : GaussianInt), ((a ∈ T.cells ↔ a + 1 ∈ T.cells)) → (({a + 1, a + 1 + ⟨0, 1⟩} : Finset
        GaussianInt) ∉ BoundaryFootprintEdges T)) → ((∀ (i : Fin (n + 3)), (({v i, v (i + 1)} :
        Finset GaussianInt) ∈ BoundaryFootprintEdges T) → (FourNeighborAdjacent (v i) (v (i +
        1)))) → ((∀ (q : Real × Real), (q ∈ C) → ((∃ m : Int, q.1 = (m : Real)) ∨ (∃ m : Int, q.2
        = (m : Real)))) → (∀ (a : GaussianInt), (a ∈ T.cells ↔ a + (1 : GaussianInt) ∈ T.cells) →
        segment ℝ (cellCenter a) (cellCenter (a + (1 : GaussianInt))) ⊆ Cᶜ))))) := by
  classical
  intro T n p v hvertex hedges C cellCenter east_side_not_boundary boundary_edge_adjacent
      boundary_carrier_has_integer_coordinate a hsame q hq hC
  rw [segment_eq_image] at hq
  rcases hq with ⟨t, ht, hqt⟩
  have hqx : q.1 = (a.re : Real) + 1 / 2 + t := by
    rw [← hqt]
    simp [cellCenter,
      smul_eq_mul]
    ring
  have hqy : q.2 = (a.im : Real) + 1 / 2 := by
    rw [← hqt]
    simp [cellCenter, add_zero,
      smul_eq_mul]
    ring
  have hxlo : (a.re : Real) + 1 / 2 ≤ q.1 := by rw [hqx]; linarith [ht.1]
  have hxhi : q.1 ≤ (a.re : Real) + 3 / 2 := by rw [hqx]; linarith [ht.2]
  have hylo : (a.im : Real) ≤ q.2 := by rw [hqy]; norm_num
  have hyhi : q.2 ≤ (a.im : Real) + 1 := by rw [hqy]; norm_num
  rcases boundary_carrier_has_integer_coordinate q hC with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hlow2R : 2 * (a.re : Real) + 1 ≤ 2 * (m : Real) := by
      rw [← hm]
      linarith [hxlo]
    have hlow2 : 2 * a.re + 1 ≤ 2 * m := by exact_mod_cast hlow2R
    have hlow : a.re + 1 ≤ m := by omega
    have hhighR : (m : Real) < (a.re : Real) + 2 := by rw [← hm]; linarith
    have hhigh : m < a.re + 2 := by exact_mod_cast hhighR
    have hmEq : m = a.re + 1 := by omega
    have hqxMid : q.1 = (a.re : Real) + 1 := by rw [hm, hmEq]; norm_num
    have hcommon : q ∈ segment ℝ (GaussianRealPoint (a + 1))
        (GaussianRealPoint (a + 1 + ⟨0, 1⟩)) := by
      rw [segment_eq_image]
      refine ⟨q.2 - (a.im : Real), ⟨by linarith [hylo], by linarith [hyhi]⟩, ?_⟩
      apply Prod.ext
      · simp? [GaussianRealPoint, Zsqrtd.re_add, Zsqrtd.re_one,
          Int.cast_add, Int.cast_one, smul_eq_mul]
        rw [(GaussianInt.intCast_re a).symm, hqxMid]
        ring
      · simp [GaussianRealPoint, Zsqrtd.im_add, Zsqrtd.im_one,
          Int.cast_add, Int.cast_one, smul_eq_mul]
        ring
    change q ∈ ⋃ i, segment ℝ (p.vertex i) (p.vertex (i + 1)) at hC
    obtain ⟨i, hpoly⟩ := Set.mem_iUnion.mp hC
    have he : ({v i, v (i + 1)} : Finset GaussianInt) ∈ BoundaryFootprintEdges T := by
      rw [hedges]
      exact ⟨i, rfl⟩
    have hboundary : q ∈ segment ℝ (GaussianRealPoint (v i))
        (GaussianRealPoint (v (i + 1))) := by
      simpa [hvertex] using hpoly
    have hpair : ({v i, v (i + 1)} : Finset GaussianInt) =
        {a + 1, a + 1 + ⟨0, 1⟩} := by
      by_contra hne
      have hinter := P3475T1UnitSegmentIntersection (v i) (v (i + 1))
        (a + 1) (a + 1 + ⟨0, 1⟩) (boundary_edge_adjacent i he)
        (by simp [FourNeighborAdjacent]) hne
      have hmem : q ∈ segment ℝ (GaussianRealPoint (v i))
            (GaussianRealPoint (v (i + 1))) ∩
          segment ℝ (GaussianRealPoint (a + 1))
            (GaussianRealPoint (a + 1 + ⟨0, 1⟩)) := ⟨hboundary, hcommon⟩
      rw [hinter] at hmem
      simp only [Set.mem_ofPred_eq] at hmem
      rcases hmem.2 with hqend | hqend
      · have him := congrArg Prod.snd hqend
        have hpoint : (GaussianRealPoint (a + 1)).2 = (a.im : Real) := by
          simp [GaussianRealPoint, Zsqrtd.im_add, Zsqrtd.im_one,
            GaussianInt.intCast_im]
        rw [hpoint] at him
        linarith [hqy]
      · have him := congrArg Prod.snd hqend
        have hpoint : (GaussianRealPoint (a + 1 + ⟨0, 1⟩)).2 = (a.im : Real) + 1 := by
          simp [GaussianRealPoint, Zsqrtd.im_add, Zsqrtd.im_one,
            GaussianInt.intCast_im, add_assoc]
        rw [hpoint] at him
        linarith [hqy]
    rw [hpair] at he
    exact east_side_not_boundary a hsame he
  · have hEq : (m : Real) = (a.im : Real) + 1 / 2 := by
      calc
        (m : Real) = q.2 := hm.symm
        _ = (a.im : Real) + 1 / 2 := hqy
    have hcast : (2 * m : Int) = 2 * a.im + 1 := by
      have hcastR : (2 : Real) * (m : Real) =
          (2 : Real) * (a.im : Real) + 1 := by rw [hEq]; ring
      exact_mod_cast hcastR
    omega

private theorem north_same_center_segment_avoids :
    ∀ (T : ProtoTile), ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (v : Fin (n + 3) →
        GaussianInt), (∀ (i : Fin (n + (3 : ℕ))), p.vertex i = GaussianRealPoint (v i)) →
        ((BoundaryFootprintEdges T = {e : Finset GaussianInt | ∃ (i : Fin (n + (3 : ℕ))), e =
        {v i, v (i + (1 : Fin (n + (3 : ℕ))))}}) → (
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    (∀ (a : GaussianInt), ((a ∈ T.cells ↔ a + ⟨0, 1⟩ ∈ T.cells)) → (({a + ⟨0, 1⟩, a + ⟨0, 1⟩ + 1}
        : Finset GaussianInt) ∉ BoundaryFootprintEdges T)) → ((∀ (i : Fin (n + 3)), (({v i,
        v (i + 1)} : Finset GaussianInt) ∈ BoundaryFootprintEdges T) → (FourNeighborAdjacent (v
        i) (v (i + 1)))) → ((∀ (q : Real × Real), (q ∈ C) → ((∃ m : Int, q.1 = (m : Real)) ∨ (∃ m
        : Int, q.2 = (m : Real)))) → (∀ (a : GaussianInt), (a ∈ T.cells ↔ a + ⟨(0 : ℤ), (1 : ℤ)⟩
        ∈ T.cells) → segment ℝ (cellCenter a) (cellCenter (a + ⟨(0 : ℤ), (1 : ℤ)⟩)) ⊆ Cᶜ))))) := by
  classical
  intro T n p v hvertex hedges C cellCenter north_side_not_boundary boundary_edge_adjacent
      boundary_carrier_has_integer_coordinate a hsame q hq hC
  rw [segment_eq_image] at hq
  rcases hq with ⟨t, ht, hqt⟩
  have hqx : q.1 = (a.re : Real) + 1 / 2 := by
    rw [← hqt]
    simp [cellCenter, Int.cast_zero,
      add_zero, smul_eq_mul]
    ring
  have hqy : q.2 = (a.im : Real) + 1 / 2 + t := by
    rw [← hqt]
    simp [cellCenter,
      Int.cast_one, smul_eq_mul]
    ring
  have hylo : (a.im : Real) + 1 / 2 ≤ q.2 := by rw [hqy]; linarith [ht.1]
  have hyhi : q.2 ≤ (a.im : Real) + 3 / 2 := by rw [hqy]; linarith [ht.2]
  have hxlo : (a.re : Real) ≤ q.1 := by rw [hqx]; norm_num
  have hxhi : q.1 ≤ (a.re : Real) + 1 := by rw [hqx]; norm_num
  rcases boundary_carrier_has_integer_coordinate q hC with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hEq : (m : Real) = (a.re : Real) + 1 / 2 := by
      calc
        (m : Real) = q.1 := hm.symm
        _ = (a.re : Real) + 1 / 2 := hqx
    have hcastR : (2 : Real) * (m : Real) =
        (2 : Real) * (a.re : Real) + 1 := by rw [hEq]; ring
    have hcast : (2 * m : Int) = 2 * a.re + 1 := by exact_mod_cast hcastR
    omega
  · have hlow2R : 2 * (a.im : Real) + 1 ≤ 2 * (m : Real) := by
      rw [← hm]
      linarith [hylo]
    have hlow2 : 2 * a.im + 1 ≤ 2 * m := by exact_mod_cast hlow2R
    have hlow : a.im + 1 ≤ m := by omega
    have hhighR : (m : Real) < (a.im : Real) + 2 := by rw [← hm]; linarith [hyhi]
    have hhigh : m < a.im + 2 := by exact_mod_cast hhighR
    have hmEq : m = a.im + 1 := by omega
    have hqyMid : q.2 = (a.im : Real) + 1 := by rw [hm, hmEq]; norm_num
    have hcommon : q ∈ segment ℝ (GaussianRealPoint (a + ⟨0, 1⟩))
        (GaussianRealPoint (a + ⟨0, 1⟩ + 1)) := by
      rw [segment_eq_image]
      refine ⟨q.1 - (a.re : Real), ⟨by linarith [hxlo], by linarith [hxhi]⟩, ?_⟩
      apply Prod.ext
      · simp? [GaussianRealPoint, Zsqrtd.re_add, Zsqrtd.re_one,
          Int.cast_add, Int.cast_one, smul_eq_mul]
        ring
      · simp? [GaussianRealPoint, Zsqrtd.im_add, Zsqrtd.im_one,
          Int.cast_add, Int.cast_one, smul_eq_mul]
        rw [(GaussianInt.intCast_im a).symm, hqyMid]
        ring
    change q ∈ ⋃ i, segment ℝ (p.vertex i) (p.vertex (i + 1)) at hC
    obtain ⟨i, hpoly⟩ := Set.mem_iUnion.mp hC
    have he : ({v i, v (i + 1)} : Finset GaussianInt) ∈ BoundaryFootprintEdges T := by
      rw [hedges]
      exact ⟨i, rfl⟩
    have hboundary : q ∈ segment ℝ (GaussianRealPoint (v i))
        (GaussianRealPoint (v (i + 1))) := by simpa [hvertex] using hpoly
    have hpair : ({v i, v (i + 1)} : Finset GaussianInt) =
        {a + ⟨0, 1⟩, a + ⟨0, 1⟩ + 1} := by
      by_contra hne
      have hinter := P3475T1UnitSegmentIntersection (v i) (v (i + 1))
        (a + ⟨0, 1⟩) (a + ⟨0, 1⟩ + 1) (boundary_edge_adjacent i he)
        (by simp [FourNeighborAdjacent]) hne
      have hmem : q ∈ segment ℝ (GaussianRealPoint (v i))
            (GaussianRealPoint (v (i + 1))) ∩
          segment ℝ (GaussianRealPoint (a + ⟨0, 1⟩))
            (GaussianRealPoint (a + ⟨0, 1⟩ + 1)) := ⟨hboundary, hcommon⟩
      rw [hinter] at hmem
      simp only [Set.mem_ofPred_eq] at hmem
      rcases hmem.2 with hqend | hqend
      · have hpoint : (GaussianRealPoint (a + ⟨0, 1⟩)).1 = (a.re : Real) := by
          simp [GaussianRealPoint, Zsqrtd.re_add, Int.cast_add,
            GaussianInt.intCast_re]
        have hx := congrArg Prod.fst hqend
        rw [hpoint] at hx
        linarith [hqx]
      · have hpoint : (GaussianRealPoint (a + ⟨0, 1⟩ + 1)).1 = (a.re : Real) + 1 := by
          simp? [GaussianRealPoint, Zsqrtd.re_add, Zsqrtd.re_one,
            Int.cast_add, Int.cast_one, GaussianInt.intCast_re, add_assoc]
        have hx := congrArg Prod.fst hqend
        rw [hpoint] at hx
        linarith [hqx]
    rw [hpair] at he
    exact north_side_not_boundary a hsame he

private theorem occupied_same_adjacent_avoid :
    ∀ (T : ProtoTile), ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    (∀ (a : GaussianInt), ((a ∈ T.cells ↔ a + 1 ∈ T.cells)) → (segment ℝ (cellCenter a)
        (cellCenter (a + 1)) ⊆ Cᶜ)) → ((∀ (a : GaussianInt), ((a ∈ T.cells ↔ a + ⟨0, 1⟩ ∈
        T.cells)) → (segment ℝ (cellCenter a) (cellCenter (a + ⟨0, 1⟩)) ⊆ Cᶜ)) → (∀ (a :
        GaussianInt), ∀ (b : GaussianInt), FourNeighborAdjacent a b → a ∈ T.cells → b ∈ T.cells →
        segment ℝ (cellCenter a) (cellCenter b) ⊆ Cᶜ)) := by
  classical
  intro T n p C cellCenter east_same_center_segment_avoids north_same_center_segment_avoids a b
      hab ha hb
  rcases hab with h | h | h | h
  · subst b
    exact east_same_center_segment_avoids a ⟨fun _ => hb, fun _ => ha⟩
  · have he : b + 1 = a := by rw [h]; simp
    have hs : (b ∈ T.cells ↔ b + 1 ∈ T.cells) := by
      constructor
      · intro _
        rw [he]
        exact ha
      · intro _
        exact hb
    have havoid := east_same_center_segment_avoids b hs
    simpa [segment_symm, he] using havoid
  · subst b
    exact north_same_center_segment_avoids a ⟨fun _ => hb, fun _ => ha⟩
  · have he : b + ⟨0, 1⟩ = a := by rw [h]; simp
    have hs : (b ∈ T.cells ↔ b + ⟨0, 1⟩ ∈ T.cells) := by
      constructor
      · intro _
        rw [he]
        exact ha
      · intro _
        exact hb
    have havoid := north_same_center_segment_avoids b hs
    simpa [segment_symm, he] using havoid

private theorem occupied_adjacent_same_domain :
    ∀ (T : ProtoTile), ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (U : Set (Real ×
        Real)), ∀ (V : Set (Real × Real)), (Disjoint U V) → (
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
    (∀ (a : Real × Real), ∀ (b : Real × Real), (segment ℝ a b ⊆ Cᶜ) → (segment ℝ a b ⊆ U ∨
        segment ℝ a b ⊆ V)) → (
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    (∀ (a : GaussianInt), ∀ (b : GaussianInt), (FourNeighborAdjacent a b) → ((a ∈ T.cells) → ((b
        ∈ T.cells) → (segment ℝ (cellCenter a) (cellCenter b) ⊆ Cᶜ)))) → (∀ (a : GaussianInt), ∀
        (b : GaussianInt), FourNeighborAdjacent a b → a ∈ T.cells → b ∈ T.cells → (cellCenter a ∈
        U ↔ cellCenter b ∈ U)))) := by
  classical
  intro T n p U V hdisjoint C segment_stays_on_one_side cellCenter occupied_same_adjacent_avoid a
      b hab ha hb
  have havoid := occupied_same_adjacent_avoid a b hab ha hb
  rcases segment_stays_on_one_side _ _ havoid with hU | hV
  · constructor <;> intro _
    · exact hU (right_mem_segment ℝ _ _)
    · exact hU (left_mem_segment ℝ _ _)
  · constructor
    · intro haU
      have haV := hV (left_mem_segment ℝ _ _)
      exact False.elim ((Set.disjoint_left.mp hdisjoint) haU haV)
    · intro hbU
      have hbV := hV (right_mem_segment ℝ _ _)
      exact False.elim ((Set.disjoint_left.mp hdisjoint) hbU hbV)

private theorem list_occupied_center_transport :
    ∀ (T : ProtoTile), ∀ (U : Set (Real × Real)),
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    (∀ (a : GaussianInt), ∀ (b : GaussianInt), (FourNeighborAdjacent a b) → ((a ∈ T.cells) → ((b
        ∈ T.cells) → ((cellCenter a ∈ U ↔ cellCenter b ∈ U))))) → (∀ (l : List GaussianInt), ∀ (x
        : GaussianInt), ∀ (y : GaussianInt), l.head? = some x → l.getLast? = some y → (∀ z ∈ l, z
        ∈ T.cells) → (∀ a, ∀ b, ∀ l₁, ∀ l₂, l = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a b) →
        (cellCenter x ∈ U ↔ cellCenter y ∈ U)) := by
  classical
  intro T U cellCenter occupied_adjacent_same_domain l x y
  induction l using List.twoStepInduction generalizing x y with
  | nil =>
      intro hx hy _ _
      simp at hx
  | singleton a =>
      intro hx hy _ _
      simp? at hx hy
      subst x
      subst y
      exact Iff.rfl
  | cons_cons a b tail ihTail ihCons =>
      intro hx hy hnodes hsteps
      have hxA : x = a := by simpa using hx.symm
      subst x
      have hy' : (b :: tail).getLast? = some y := by simpa using hy
      have hab : FourNeighborAdjacent a b := by
        apply hsteps a b [] tail
        simp
      have ha : a ∈ T.cells := hnodes a (by simp)
      have hb : b ∈ T.cells := hnodes b (by simp)
      have hfirst := occupied_adjacent_same_domain a b hab ha hb
      have hnodes' : ∀ z ∈ b :: tail, z ∈ T.cells := by
        intro z hz
        exact hnodes z (by simp [hz])
      have hsteps' : ∀ a' b' l₁ l₂,
          b :: tail = l₁ ++ a' :: b' :: l₂ → FourNeighborAdjacent a' b' := by
        intro a' b' l₁ l₂ hEq
        apply hsteps a' b' (a :: l₁) l₂
        simpa using congrArg (fun q => a :: q) hEq
      have htail := ihCons b b y (by simp) hy' hnodes' hsteps'
      exact hfirst.trans htail

private theorem boundary_disjoint_open_cell :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
    (∀ (q : Real × Real), (q ∈ C) → ((∃ m : Int, q.1 = (m : Real)) ∨ (∃ m : Int, q.2 = (m :
        Real)))) → (
    let inOpenCell : GaussianInt → (Real × Real) → Prop := fun c q =>
      (c.re : Real) < q.1 ∧ q.1 < (c.re : Real) + 1 ∧
        (c.im : Real) < q.2 ∧ q.2 < (c.im : Real) + 1
    ∀ (c : GaussianInt), ∀ q ∈ C, inOpenCell c q → False) := by
  classical
  intro n p C boundary_carrier_has_integer_coordinate inOpenCell c q hq hcell
  change (c.re : Real) < q.1 ∧ q.1 < (c.re : Real) + 1 ∧
    (c.im : Real) < q.2 ∧ q.2 < (c.im : Real) + 1 at hcell
  rcases boundary_carrier_has_integer_coordinate q hq with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [hm] at hcell
    have hlo : c.re < m := by exact_mod_cast hcell.1
    have hhi : m < c.re + 1 := by exact_mod_cast hcell.2.1
    omega
  · rw [hm] at hcell
    have hlo : c.im < m := by exact_mod_cast hcell.2.2.1
    have hhi : m < c.im + 1 := by exact_mod_cast hcell.2.2.2
    omega

private theorem open_cell_segment_subset :
    let inOpenCell : GaussianInt → (Real × Real) → Prop := fun c q =>
      (c.re : Real) < q.1 ∧ q.1 < (c.re : Real) + 1 ∧
        (c.im : Real) < q.2 ∧ q.2 < (c.im : Real) + 1
    ∀ (c : GaussianInt), ∀ (x : ℝ × ℝ), ∀ (y : ℝ × ℝ), inOpenCell c x → inOpenCell c y → segment
        ℝ x y ⊆ {q : ℝ × ℝ | inOpenCell c q} := by
  classical
  intro inOpenCell c x y hx hy
  change (c.re : Real) < x.1 ∧ x.1 < (c.re : Real) + 1 ∧
    (c.im : Real) < x.2 ∧ x.2 < (c.im : Real) + 1 at hx
  change (c.re : Real) < y.1 ∧ y.1 < (c.re : Real) + 1 ∧
    (c.im : Real) < y.2 ∧ y.2 < (c.im : Real) + 1 at hy
  have weighted_lower (a x y t : Real) (hx : a < x) (hy : a < y)
      (ht : 0 ≤ t) (ht' : t ≤ 1) : a < (1 - t) * x + t * y := by
    by_cases ht0 : t = 0
    · simpa [ht0] using hx
    by_cases ht1 : t = 1
    · simpa [ht1] using hy
    have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have htlt : t < 1 := lt_of_le_of_ne ht' ht1
    have htq : 0 < 1 - t := sub_pos.mpr htlt
    have h1 : 0 < (1 - t) * (x - a) := mul_pos htq (sub_pos.mpr hx)
    have h2 : 0 < t * (y - a) := mul_pos htp (sub_pos.mpr hy)
    nlinarith
  have weighted_upper (b x y t : Real) (hx : x < b) (hy : y < b)
      (ht : 0 ≤ t) (ht' : t ≤ 1) : (1 - t) * x + t * y < b := by
    by_cases ht0 : t = 0
    · simpa [ht0] using hx
    by_cases ht1 : t = 1
    · simpa [ht1] using hy
    have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have htlt : t < 1 := lt_of_le_of_ne ht' ht1
    have htq : 0 < 1 - t := sub_pos.mpr htlt
    have h1 : 0 < (1 - t) * (b - x) := mul_pos htq (sub_pos.mpr hx)
    have h2 : 0 < t * (b - y) := mul_pos htp (sub_pos.mpr hy)
    nlinarith
  rw [segment_eq_image]
  rintro q ⟨t, ht, rfl⟩
  change (c.re : Real) < ((1 - t) • x + t • y).1 ∧
    ((1 - t) • x + t • y).1 < (c.re : Real) + 1 ∧
    (c.im : Real) < ((1 - t) • x + t • y).2 ∧
    ((1 - t) • x + t • y).2 < (c.im : Real) + 1
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
    smul_eq_mul]
  rcases hx with ⟨hxl, hxu, hyl, hyu⟩
  rcases hy with ⟨hxl', hxu', hyl', hyu'⟩
  exact ⟨weighted_lower _ _ _ _ hxl hxl' ht.1 ht.2,
    weighted_upper _ _ _ _ hxu hxu' ht.1 ht.2,
    weighted_lower _ _ _ _ hyl hyl' ht.1 ht.2,
    weighted_upper _ _ _ _ hyu hyu' ht.1 ht.2⟩

private theorem center_to_square_point_avoid :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    let inOpenCell : GaussianInt → (Real × Real) → Prop := fun c q =>
      (c.re : Real) < q.1 ∧ q.1 < (c.re : Real) + 1 ∧
        (c.im : Real) < q.2 ∧ q.2 < (c.im : Real) + 1
    (∀ (c : GaussianInt), ∀ (q : Real × Real), (q ∈ C) → ((inOpenCell c q) → (False))) → (∀ (c :
        GaussianInt), ∀ q ∈ ClosedSquareRealization c, q ∉ C → segment ℝ (cellCenter c) q ⊆ Cᶜ)
        := by
  classical
  intro n p C cellCenter inOpenCell boundary_disjoint_open_cell c q hq hqC x hx hxC
  rw [segment_eq_image] at hx
  rcases hx with ⟨t, ht, rfl⟩
  by_cases ht1 : t = 1
  · apply hqC
    simpa [ht1] using hxC
  · have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
    have hq' : q ∈ ClosedSquareRealization c := hq
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hq'
    rcases hq' with ⟨⟨hxl, hyl⟩, ⟨hxu, hyu⟩⟩
    have hcenter : inOpenCell c (cellCenter c) := by
      change (c.re : Real) < (cellCenter c).1 ∧
        (cellCenter c).1 < (c.re : Real) + 1 ∧
        (c.im : Real) < (cellCenter c).2 ∧
        (cellCenter c).2 < (c.im : Real) + 1
      simp [cellCenter]
      norm_num
    change (c.re : Real) < (cellCenter c).1 ∧
      (cellCenter c).1 < (c.re : Real) + 1 ∧
      (c.im : Real) < (cellCenter c).2 ∧
      (cellCenter c).2 < (c.im : Real) + 1 at hcenter
    have hleft : 0 < 1 - t := sub_pos.mpr htlt
    have hxlo : (c.re : Real) < ((1 - t) • cellCenter c + t • q).1 := by
      simp only [Prod.smul_fst, Prod.fst_add, smul_eq_mul]
      have h1 : 0 < (1 - t) * ((cellCenter c).1 - (c.re : Real)) :=
        mul_pos hleft (sub_pos.mpr hcenter.1)
      have h2 : 0 ≤ t * (q.1 - (c.re : Real)) :=
        mul_nonneg ht.1 (sub_nonneg.mpr (by linarith))
      nlinarith
    have hxhi : ((1 - t) • cellCenter c + t • q).1 < (c.re : Real) + 1 := by
      simp only [Prod.smul_fst, Prod.fst_add, smul_eq_mul]
      have h1 : 0 < (1 - t) * ((c.re : Real) + 1 - (cellCenter c).1) :=
        mul_pos hleft (sub_pos.mpr hcenter.2.1)
      have h2 : 0 ≤ t * ((c.re : Real) + 1 - q.1) :=
        mul_nonneg ht.1 (sub_nonneg.mpr (by linarith))
      nlinarith
    have hylo : (c.im : Real) < ((1 - t) • cellCenter c + t • q).2 := by
      simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul]
      have h1 : 0 < (1 - t) * ((cellCenter c).2 - (c.im : Real)) :=
        mul_pos hleft (sub_pos.mpr hcenter.2.2.1)
      have h2 : 0 ≤ t * (q.2 - (c.im : Real)) :=
        mul_nonneg ht.1 (sub_nonneg.mpr (by linarith))
      nlinarith
    have hyhi : ((1 - t) • cellCenter c + t • q).2 < (c.im : Real) + 1 := by
      simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul]
      have h1 : 0 < (1 - t) * ((c.im : Real) + 1 - (cellCenter c).2) :=
        mul_pos hleft (sub_pos.mpr hcenter.2.2.2)
      have h2 : 0 ≤ t * ((c.im : Real) + 1 - q.2) :=
        mul_nonneg ht.1 (sub_nonneg.mpr (by linarith))
      nlinarith
    exact boundary_disjoint_open_cell c _ hxC ⟨hxlo, hxhi, hylo, hyhi⟩

private theorem square_point_same_domain :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (U : Set (Real × Real)), ∀ (V : Set (Real
        × Real)), (Disjoint U V) → (
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
    (∀ (a : Real × Real), ∀ (b : Real × Real), (segment ℝ a b ⊆ Cᶜ) → (segment ℝ a b ⊆ U ∨
        segment ℝ a b ⊆ V)) → (
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    (∀ (c : GaussianInt), ∀ (q : Real × Real), (q ∈ ClosedSquareRealization c) → ((q ∉ C) →
        (segment ℝ (cellCenter c) q ⊆ Cᶜ))) → (∀ (c : GaussianInt), ∀ q ∈ ClosedSquareRealization
        c, q ∉ C → (q ∈ U ↔ cellCenter c ∈ U)))) := by
  classical
  intro n p U V hdisjoint C segment_stays_on_one_side cellCenter center_to_square_point_avoid c q
      hq hqC
  have havoid := center_to_square_point_avoid c q hq hqC
  rcases segment_stays_on_one_side _ _ havoid with hU | hV
  · constructor
    · intro _
      exact hU (left_mem_segment ℝ _ _)
    · intro _
      exact hU (right_mem_segment ℝ _ _)
  · constructor
    · intro hqU
      have hqV := hV (right_mem_segment ℝ _ _)
      exact False.elim ((Set.disjoint_left.mp hdisjoint) hqU hqV)
    · intro hcU
      have hcV := hV (left_mem_segment ℝ _ _)
      exact False.elim ((Set.disjoint_left.mp hdisjoint) hcU hcV)

private theorem open_complement_cell_in_V :
    ∀ (T : ProtoTile), ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (U : Set (Real ×
        Real)), ∀ (V : Set (Real × Real)), (Disjoint U V) → (
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
    (∀ (a : Real × Real), ∀ (b : Real × Real), (segment ℝ a b ⊆ Cᶜ) → (segment ℝ a b ⊆ U ∨
        segment ℝ a b ⊆ V)) → (
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    (∀ (z : GaussianInt), (z ∉ T.cells) → (cellCenter z ∈ V)) → (
    let inOpenCell : GaussianInt → (Real × Real) → Prop := fun c q =>
      (c.re : Real) < q.1 ∧ q.1 < (c.re : Real) + 1 ∧
        (c.im : Real) < q.2 ∧ q.2 < (c.im : Real) + 1
    (∀ (c : GaussianInt), ∀ (q : Real × Real), (q ∈ C) → ((inOpenCell c q) → (False))) → ((∀ (c :
        GaussianInt), ∀ (x : Real × Real), ∀ (y : Real × Real), (inOpenCell c x) → ((inOpenCell c
        y) → (segment ℝ x y ⊆ {q | inOpenCell c q}))) → ((∀ (c : GaussianInt), inOpenCell c
        (cellCenter c)) → (∀ c ∉ T.cells, ∀ (q : ℝ × ℝ), inOpenCell c q → q ∈ V)))))) := by
  classical
  intro T n p U V hdisjoint C segment_stays_on_one_side cellCenter every_complement_center_in_V
      inOpenCell boundary_disjoint_open_cell open_cell_segment_subset center_in_open_cell c hc q hq
  have hseg : segment ℝ (cellCenter c) q ⊆ Cᶜ := by
    intro x hx hC
    exact boundary_disjoint_open_cell c x hC
      (open_cell_segment_subset c (cellCenter c) q (center_in_open_cell c) hq hx)
  rcases segment_stays_on_one_side _ _ hseg with hU | hV
  · have hcU : cellCenter c ∈ U := hU (left_mem_segment ℝ _ _)
    have hcV := every_complement_center_in_V c hc
    exact False.elim ((Set.disjoint_left.mp hdisjoint) hcU hcV)
  · exact hV (right_mem_segment ℝ _ _)

private theorem qSeedSide :
    ∀ (seed : LatticeCell),
    let qSeed : Real × Real := ((seed.re : Real) + 1, (seed.im : Real) + 1 / 2)
    qSeed ∈ segment ℝ (GaussianRealPoint (seed + 1)) (GaussianRealPoint (seed + 1 + ⟨0, 1⟩)) := by
  classical
  intro seed qSeed
  rw [segment_eq_image]
  refine ⟨1 / 2, by norm_num, ?_⟩
  apply Prod.ext
  · simp? [qSeed, GaussianRealPoint, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_one, Zsqrtd.im_one, Int.cast_add, Int.cast_one,
      add_zero,
      smul_eq_mul]
    rw [(GaussianInt.intCast_re seed).symm]
    ring
  · simp? [qSeed, GaussianRealPoint, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_one, Zsqrtd.im_one, Int.cast_add, Int.cast_one,
      add_zero, smul_eq_mul]
    rw [(GaussianInt.intCast_im seed).symm]
    ring

end SquareUnionProof

namespace SquareUnionDetails

private theorem every_complement_center_in_V :
    ∀ (T : ProtoTile), (FourNeighborConnected (↑T.cells : Set LatticeCell)ᶜ) → (∀ (U : Set (ℝ ×
        ℝ)), ∀ (V : Set (ℝ × ℝ)),
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    (∀ (a : GaussianInt), (a ∉ T.cells) → (cellCenter a ∈ U ∨ cellCenter a ∈ V)) → ((∀ (l : List
        GaussianInt), ∀ (x : GaussianInt), ∀ (y : GaussianInt), l.head? = some x → l.getLast? =
        some y → (∀ z ∈ l, z ∉ T.cells) → (∀ a, ∀ b, ∀ l₁, ∀ l₂, l = l₁ ++ a :: b :: l₂ →
        FourNeighborAdjacent a b) → (cellCenter x ∈ U ↔ cellCenter y ∈ U)) → (∀ (farCell :
        GaussianInt), (farCell ∉ T.cells) → ((cellCenter farCell ∉ U) → (∀ z ∉ T.cells,
        cellCenter z ∈ V))))) := by
  classical
  intro T houtside U V cellCenter center_in_domain list_center_transport farCell hfarCell
      hfarNotU z hz
  obtain ⟨l, hlhead, hllast, hlnodes, hlsteps⟩ :=
    houtside.2 z hz farCell hfarCell
  have htransport := list_center_transport l z farCell hlhead hllast hlnodes hlsteps
  rcases center_in_domain z hz with hzU | hzV
  · exact False.elim (hfarNotU (htransport.mp hzU))
  · exact hzV

private theorem horizontal_segment_y :
    ∀ (z : GaussianInt), ∀ q ∈ segment ℝ (GaussianRealPoint z) (GaussianRealPoint (z + (1 :
        GaussianInt))), q.2 = (↑z.im : ℝ) := by
  classical
  intro z q hq
  rw [segment_eq_image] at hq
  rcases hq with ⟨t, ht, rfl⟩
  simp [GaussianRealPoint, Zsqrtd.im_add, Zsqrtd.im_one, add_zero,
    smul_eq_mul]
  ring

private theorem vertical_segment_x :
    ∀ (z : GaussianInt), ∀ q ∈ segment ℝ (GaussianRealPoint z) (GaussianRealPoint (z + ⟨(0 : ℤ),
        (1 : ℤ)⟩)), q.1 = (↑z.re : ℝ) := by
  classical
  intro z q hq
  rw [segment_eq_image] at hq
  rcases hq with ⟨t, ht, rfl⟩
  simp [GaussianRealPoint, Zsqrtd.re_add, Int.cast_add,
    add_zero, smul_eq_mul]
  ring

private theorem center_in_open_cell :
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    let inOpenCell : GaussianInt → (Real × Real) → Prop := fun c q =>
      (c.re : Real) < q.1 ∧ q.1 < (c.re : Real) + 1 ∧
        (c.im : Real) < q.2 ∧ q.2 < (c.im : Real) + 1
    ∀ (c : GaussianInt), inOpenCell c (cellCenter c) := by
  classical
  intro cellCenter inOpenCell c
  change (c.re : Real) < (cellCenter c).1 ∧
    (cellCenter c).1 < (c.re : Real) + 1 ∧
    (c.im : Real) < (cellCenter c).2 ∧
    (cellCenter c).2 < (c.im : Real) + 1
  simp [cellCenter]
  norm_num

private theorem eastSeedEmpty :
    ∀ (T : ProtoTile), ∀ (seed : LatticeCell), (∀ x' ∈ T.cells, x'.re ≤ seed.re) → (seed + 1 ∉
        T.cells) := by
  classical
  intro T seed hseedMax h
  have hle := hseedMax (seed + 1) h
  have hlt : seed.re < (seed + 1).re := by simp
  omega

private theorem eastSeedEdge :
    ∀ (T : ProtoTile), ∀ (seed : LatticeCell), (seed ∈ T.cells) → ((seed + 1 ∉ T.cells) →
        (({seed + 1, seed + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges T)) := by
  classical
  intro T seed hseed eastSeedEmpty
  refine ⟨seed + 1, Or.inr ⟨rfl, Or.inr ?_⟩⟩
  constructor
  · simpa using eastSeedEmpty
  · simpa using hseed

private theorem qSeedFront :
    ∀ (n : ℕ), ∀ (p : P3381T1PolygonBoundary n), ∀ (U : Set (ℝ × ℝ)), (frontier U = ⋃ (i : Fin
        (n + (3 : ℕ))), segment ℝ (p.vertex i) (p.vertex (i + (1 : Fin (n + (3 : ℕ)))))) → (
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
    ∀ (seed : LatticeCell),
    let qSeed : Real × Real := ((seed.re : Real) + 1, (seed.im : Real) +
        1 / 2)
    (qSeed ∈ C) → (qSeed ∈ frontier U)) := by
  classical
  intro n p U hfrontU C seed qSeed qSeedC
  rw [hfrontU]
  exact qSeedC

private theorem hrxLower :
    ∀ (seed : LatticeCell),
    let qSeed : Real × Real := ((seed.re : Real) + 1, (seed.im : Real) +
        1 / 2)
    ∀ (r : ℝ × ℝ), (|qSeed.1 - r.1| < (1 / 4 : Real)) → ((seed.re : Real) + (3 / 4 : Real) < r.1)
        := by
  classical
  intro seed qSeed r hdx
  have := abs_lt.mp hdx
  dsimp [qSeed] at this
  linarith

private theorem hrxUpper :
    ∀ (seed : LatticeCell),
    let qSeed : Real × Real := ((seed.re : Real) + 1, (seed.im : Real) +
        1 / 2)
    ∀ (r : ℝ × ℝ), (|qSeed.1 - r.1| < (1 / 4 : Real)) → (r.1 < (seed.re : Real) + (5 / 4 : Real))
        := by
  classical
  intro seed qSeed r hdx
  have := abs_lt.mp hdx
  dsimp [qSeed] at this
  linarith

private theorem hryLower :
    ∀ (seed : LatticeCell),
    let qSeed : Real × Real := ((seed.re : Real) + 1, (seed.im : Real) +
        1 / 2)
    ∀ (r : ℝ × ℝ), (|qSeed.2 - r.2| < (1 / 4 : Real)) → ((seed.im : Real) < r.2) := by
  classical
  intro seed qSeed r hdy
  have := abs_lt.mp hdy
  dsimp [qSeed] at this
  linarith

private theorem hryUpper :
    ∀ (seed : LatticeCell),
    let qSeed : Real × Real := ((seed.re : Real) + 1, (seed.im : Real) +
        1 / 2)
    ∀ (r : ℝ × ℝ), (|qSeed.2 - r.2| < (1 / 4 : Real)) → (((seed.im : Real) < r.2) → (r.2 <
        (seed.im : Real) + 1)) := by
  classical
  intro seed qSeed r hdy hryLower
  have := abs_lt.mp hdy
  dsimp [qSeed] at this
  linarith

private theorem rnotC :
    ∀ (n : ℕ), ∀ (p : P3381T1PolygonBoundary n), ∀ (U : Set (ℝ × ℝ)), ∀ (V : Set (ℝ × ℝ)), (U ∪
        V = (⋃ (i : Fin (n + (3 : ℕ))), segment ℝ (p.vertex i) (p.vertex (i + (1 : Fin (n + (3 :
        ℕ))))))ᶜ) → (
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
    ∀ (r : ℝ × ℝ), (r ∈ U) → (r ∉ C)) := by
  classical
  intro n p U V hcover C r hrU
  have : r ∈ Cᶜ := by rw [← hcover]; exact Or.inl hrU
  exact this

private theorem hrNotSide :
    ∀ (T : ProtoTile), ∀ (n : ℕ), ∀ (p : P3381T1PolygonBoundary n),
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
    (∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges T) → (∀ (a : GaussianInt), ∀ (b :
        GaussianInt), (e = {a, b}) → ((a ≠ b) → (∀ (q : Real × Real), (q ∈ segment ℝ
        (GaussianRealPoint a) (GaussianRealPoint b)) → (q ∈ C))))) → (∀ (seed : LatticeCell),
        (({seed + 1, seed + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges T) → (∀ (r
        : ℝ × ℝ), ((seed.im : Real) < r.2) → ((r.2 < (seed.im : Real) + 1) → ((r ∉ C) → (r.1 ≠
        (seed.re : Real) + 1))))) := by
  classical
  intro T n p C boundary_side_segment_in_C seed eastSeedEdge r hryLower hryUpper rnotC hr
  have hside : r ∈ segment ℝ (GaussianRealPoint (seed + 1))
      (GaussianRealPoint (seed + 1 + ⟨0, 1⟩)) := by
    rw [segment_eq_image]
    refine ⟨r.2 - (seed.im : Real), ⟨by linarith [hryLower], by linarith [hryUpper]⟩, ?_⟩
    apply Prod.ext
    · simp? [GaussianRealPoint, Zsqrtd.re_add, Zsqrtd.re_one,
        Int.cast_add, Int.cast_one, smul_eq_mul]
      rw [hr, (GaussianInt.intCast_re seed).symm]
      ring
    · simp [GaussianRealPoint, Zsqrtd.im_add, Zsqrtd.im_one,
        Int.cast_add, Int.cast_one, smul_eq_mul]
      ring
  exact rnotC (boundary_side_segment_in_C _ eastSeedEdge _ _ rfl
    (by intro h; have hi := congrArg (fun z : GaussianInt => z.im) h; simp at hi) r hside)

private theorem seedCenterU :
    ∀ (T : ProtoTile), ∀ (n : ℕ), ∀ (p : P3381T1PolygonBoundary n), ∀ (U : Set (ℝ × ℝ)), ∀ (V :
        Set (ℝ × ℝ)), (Disjoint U V) → (
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex
        i) (p.vertex (i + 1))
    (∀ (a : Real × Real), ∀ (b : Real × Real), (segment ℝ a b ⊆ Cᶜ) → (segment ℝ a b ⊆ U ∨
        segment ℝ a b ⊆ V)) → (
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    let inOpenCell : GaussianInt → (Real × Real) → Prop := fun c q =>
      (c.re : Real) < q.1 ∧ q.1 < (c.re : Real) + 1 ∧
        (c.im : Real) < q.2 ∧ q.2 < (c.im : Real) + 1
    (∀ (c : GaussianInt), ∀ (q : Real × Real), (q ∈ C) → ((inOpenCell c q) → (False))) → ((∀ (c :
        GaussianInt), ∀ (x : Real × Real), ∀ (y : Real × Real), (inOpenCell c x) → ((inOpenCell c
        y) → (segment ℝ x y ⊆ {q | inOpenCell c q}))) → ((∀ (c : GaussianInt), inOpenCell c
        (cellCenter c)) → ((∀ (c : GaussianInt), (c ∉ T.cells) → (∀ (q : Real × Real),
        (inOpenCell c q) → (q ∈ V))) → (∀ (seed : LatticeCell), (seed + 1 ∉ T.cells) → (∀ (r : ℝ
        × ℝ), (r ∈ U) → (((seed.re : Real) + (3 / 4 : Real) < r.1) → ((r.1 < (seed.re : Real) +
        (5 / 4 : Real)) → (((seed.im : Real) < r.2) → ((r.2 < (seed.im : Real) + 1) → ((r.1 ≠
        (seed.re : Real) + 1) → (cellCenter seed ∈ U))))))))))))) := by
  classical
  intro T n p U V hdisjoint C segment_stays_on_one_side cellCenter inOpenCell
      boundary_disjoint_open_cell open_cell_segment_subset center_in_open_cell
      open_complement_cell_in_V seed eastSeedEmpty r hrU hrxLower hrxUpper hryLower hryUpper
      hrNotSide
  have hcases : r.1 < (seed.re : Real) + 1 ∨
      (seed.re : Real) + 1 < r.1 := lt_or_gt_of_ne hrNotSide
  rcases hcases with hleft | hright
  · have hrOpen : inOpenCell seed r := by
      change (seed.re : Real) < r.1 ∧ r.1 < (seed.re : Real) + 1 ∧
        (seed.im : Real) < r.2 ∧ r.2 < (seed.im : Real) + 1
      exact ⟨by linarith [hrxLower], hleft, hryLower, hryUpper⟩
    have havoid : segment ℝ (cellCenter seed) r ⊆ Cᶜ := by
      intro x hx hxC
      exact boundary_disjoint_open_cell seed x hxC
        (open_cell_segment_subset seed (cellCenter seed) r (center_in_open_cell seed) hrOpen hx)
    rcases segment_stays_on_one_side _ _ havoid with hU | hV
    · exact hU (left_mem_segment ℝ _ _)
    · have hrV : r ∈ V := hV (right_mem_segment ℝ _ _)
      exact False.elim ((Set.disjoint_left.mp hdisjoint) hrU hrV)
  · have hcomp : seed + 1 ∉ T.cells := eastSeedEmpty
    have hrOpen : inOpenCell (seed + 1) r := by
      change ((seed + 1).re : Real) < r.1 ∧ r.1 < ((seed + 1).re : Real) + 1 ∧
        ((seed + 1).im : Real) < r.2 ∧ r.2 < ((seed + 1).im : Real) + 1
      simp only [Zsqrtd.re_add, Zsqrtd.re_one, Int.cast_add, Int.cast_one,
        Zsqrtd.im_add, Zsqrtd.im_one, add_zero]
      exact ⟨hright, by linarith [hrxUpper], hryLower, hryUpper⟩
    have hrV := open_complement_cell_in_V (seed + 1) hcomp r hrOpen
    exact False.elim ((Set.disjoint_left.mp hdisjoint) hrU hrV)

private theorem every_occupied_center_in_U :
    ∀ (T : ProtoTile), (FourNeighborConnected (↑T.cells : Set LatticeCell)) → (∀ (U : Set (ℝ ×
        ℝ)),
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    (∀ (l : List GaussianInt), ∀ (x : GaussianInt), ∀ (y : GaussianInt), l.head? = some x →
        l.getLast? = some y → (∀ z ∈ l, z ∈ T.cells) → (∀ a, ∀ b, ∀ l₁, ∀ l₂, l = l₁ ++ a :: b ::
        l₂ → FourNeighborAdjacent a b) → (cellCenter x ∈ U ↔ cellCenter y ∈ U)) → (∀ (seed :
        LatticeCell), (seed ∈ T.cells) → ((cellCenter seed ∈ U) → (∀ z ∈ T.cells, cellCenter z ∈
        U)))) := by
  classical
  intro T hinside U cellCenter list_occupied_center_transport seed hseed seedCenterU z hz
  obtain ⟨l, hlhead, hllast, hlnodes, hlsteps⟩ := hinside.2 seed hseed z hz
  have htransport := list_occupied_center_transport l seed z hlhead hllast hlnodes hlsteps
  exact htransport.mp seedCenterU

private theorem tile_cover :
    ∀ (T : ProtoTile), ∀ (n : ℕ), ∀ (p : P3381T1PolygonBoundary n), ∀ (U : Set (ℝ × ℝ)), ∀ (V :
        Set (ℝ × ℝ)), (Disjoint U V) → (
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex
        i) (p.vertex (i + 1))
    (C ⊆ TileRealization T) → (
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    (∀ (z : GaussianInt), (z ∉ T.cells) → (cellCenter z ∈ V)) → ((∀ (c : GaussianInt), ∀ (q :
        Real × Real), (q ∈ ClosedSquareRealization c) → ((q ∉ C) → ((q ∈ U ↔ cellCenter c ∈ U))))
        → ((∀ (z : GaussianInt), (z ∈ T.cells) → (cellCenter z ∈ U)) → (TileRealization T = U ∪
        C))))) := by
  classical
  intro T n p U V hdisjoint C boundary_carrier_in_tile cellCenter every_complement_center_in_V
      square_point_same_domain every_occupied_center_in_U
  ext q
  constructor
  · intro hq
    simp only [TileRealization, Set.mem_iUnion] at hq
    obtain ⟨c, hc, hqSquare⟩ := hq
    by_cases hqC : q ∈ C
    · exact Or.inr hqC
    · apply Or.inl
      exact (square_point_same_domain c q hqSquare hqC).mpr
        (every_occupied_center_in_U c hc)
  · intro hq
    rcases hq with hqU | hqC
    · by_cases hqBoundary : q ∈ C
      · exact boundary_carrier_in_tile hqBoundary
      · let c : GaussianInt := ⟨Int.floor q.1, Int.floor q.2⟩
        have hqSquare : q ∈ ClosedSquareRealization c := by
          simp? [ClosedSquareRealization, c, Set.mem_Icc, Prod.le_def]
          constructor
          · constructor
            · exact_mod_cast Int.floor_le q.1
            · exact_mod_cast Int.floor_le q.2
          · constructor
            · exact_mod_cast (Int.lt_floor_add_one q.1).le
            · exact_mod_cast (Int.lt_floor_add_one q.2).le
        by_cases hc : c ∈ T.cells
        · simp only [TileRealization, Set.mem_iUnion]
          exact ⟨c, hc, hqSquare⟩
        · have hcV := every_complement_center_in_V c hc
          have hcU := (square_point_same_domain c q hqSquare hqBoundary).mp hqU
          exact False.elim ((Set.disjoint_left.mp hdisjoint) hcU hcV)
    · exact boundary_carrier_in_tile hqC

end SquareUnionDetails

namespace SquareDomainBlocks

private theorem every_complement_center_in_V :
    ∀ (T : ProtoTile), (FourNeighborConnected (↑T.cells : Set LatticeCell)) →
        ((FourNeighborConnected (↑T.cells : Set LatticeCell)ᶜ) → (∀ (n : ℕ), ∀ (p :
        P3381T1PolygonBoundary n), ∀ (U : Set (ℝ × ℝ)), ∀ (V : Set (ℝ × ℝ)),
        (Bornology.IsBounded U) → ((Disjoint U V) → ((U ∪ V = (⋃ (i : Fin (n + (3 : ℕ))), segment
        ℝ (p.vertex i) (p.vertex (i + (1 : Fin (n + (3 : ℕ))))))ᶜ) → (
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
    (⋃ (i : Fin (n + (3 : ℕ))), segment ℝ (p.vertex i) (p.vertex (i + (1 : Fin (n + (3 : ℕ))))) ⊆
        TileRealization T) → ((∀ (a : ℝ × ℝ), ∀ (b : ℝ × ℝ), segment ℝ a b ⊆ Cᶜ → segment ℝ a b ⊆
        U ∨ segment ℝ a b ⊆ V) → (
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    ∀ z ∉ T.cells, cellCenter z ∈ V))))))) := by
  classical
  intro T hinside houtside n p U V hUbounded hdisjoint hcover C boundary_carrier_in_tile
      segment_stays_on_one_side cellCenter z hz
  have east_center_segment_outside (a : GaussianInt)
      (ha : a ∉ T.cells) (hb : a + 1 ∉ T.cells) := SquareUnionProof.east_center_segment_outside T
          a ha hb
  have north_center_segment_outside (a : GaussianInt)
      (ha : a ∉ T.cells) (hb : a + ⟨0, 1⟩ ∉ T.cells) :=
          SquareUnionProof.north_center_segment_outside T a ha hb
  have complement_adjacent_segment_avoid (a b : GaussianInt)
      (hab : FourNeighborAdjacent a b) (ha : a ∉ T.cells) (hb : b ∉ T.cells) :=
          SquareUnionProof.complement_adjacent_segment_avoid T n p boundary_carrier_in_tile
          east_center_segment_outside north_center_segment_outside a b hab ha hb
  have center_not_tile (a : GaussianInt) (ha : a ∉ T.cells) := SquareUnionProof.center_not_tile T
      a ha
  have center_in_domain (a : GaussianInt) (ha : a ∉ T.cells) := SquareUnionProof.center_in_domain
      T n p U V hcover
          boundary_carrier_in_tile center_not_tile a ha
  have complement_adjacent_same_domain (a b : GaussianInt)
      (hab : FourNeighborAdjacent a b) (ha : a ∉ T.cells) (hb : b ∉ T.cells) :=
          SquareUnionProof.complement_adjacent_same_domain T
          n p U V hdisjoint segment_stays_on_one_side complement_adjacent_segment_avoid a b hab
          ha hb
  have list_center_transport := SquareUnionProof.list_center_transport T U
          complement_adjacent_same_domain
  have farComplementCell := SquareUnionProof.farComplementCell T hinside U hUbounded
  obtain ⟨farCell, hfarCell, hfarNotU⟩ := farComplementCell
  exact SquareUnionDetails.every_complement_center_in_V T houtside U V center_in_domain
      list_center_transport farCell hfarCell hfarNotU z hz

end SquareDomainBlocks

private theorem identificationFromExteriorCenters
    (T : ProtoTile) (hinside : FourNeighborConnected (T.cells : Set LatticeCell))
    {n : Nat} (p : P3381T1PolygonBoundary n) (v : Fin (n + 3) → GaussianInt)
    (hvertex : ∀ i, p.vertex i = GaussianRealPoint (v i))
    (hedges : BoundaryFootprintEdges T = {e | ∃ i, e = {v i, v (i + 1)}})
    (U V : Set (Real × Real)) (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hdisjoint : Disjoint U V)
    (hcover : U ∪ V = (⋃ i, segment Real (p.vertex i) (p.vertex (i + 1)))ᶜ)
    (hfrontU : frontier U = ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1))) :
    let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
    let cellCenter : GaussianInt → Real × Real := fun z =>
      ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
    (∀ z, z ∉ T.cells → cellCenter z ∈ V) → TileRealization T = U ∪ C := by
  classical
  intro C cellCenter every_complement_center_in_V
  have edge_support (e : Finset GaussianInt) (he : e ∈ BoundaryFootprintEdges T) :=
      SquareUnionProof.edge_support T e he
  have edge_endpoint_square (z : GaussianInt) (e : Finset GaussianInt)
      (he : e = {z, z + 1} ∨ e = {z, z + ⟨0, 1⟩} ∨
        e = {z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩} ∨
        e = {z + 1, z + 1 + ⟨0, 1⟩})
      (w : GaussianInt) (hw : w ∈ e) := SquareUnionProof.edge_endpoint_square z
          e he w hw
  have boundary_carrier_in_tile := SquareUnionProof.boundary_carrier_in_tile T n p v hvertex
      hedges edge_support
      edge_endpoint_square
  have segment_stays_on_one_side (a b : Real × Real)
      (havoid : segment ℝ a b ⊆ Cᶜ) := SquareUnionProof.segment_stays_on_one_side n p U V
        hUopen hVopen hdisjoint hcover a b havoid
  have pair_eq_cases (a b c d : GaussianInt)
      (hcd : c ≠ d) (hpair : ({a, b} : Finset GaussianInt) = {c, d}) :=
          SquareUnionProof.pair_eq_cases a b c d hcd hpair
  have boundary_side_segment_in_C (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges T) (a b : GaussianInt)
      (hab : e = {a, b}) (habne : a ≠ b) (q : Real × Real)
      (hq : q ∈ segment ℝ (GaussianRealPoint a) (GaussianRealPoint b)) :=
          SquareUnionProof.boundary_side_segment_in_C T n p v hvertex hedges pair_eq_cases e he a
          b hab habne q hq
  have east_side_not_boundary (a : GaussianInt)
      (hsame : (a ∈ T.cells ↔ a + 1 ∈ T.cells)) := SquareUnionProof.east_side_not_boundary T
          pair_eq_cases a hsame
  have north_side_not_boundary (a : GaussianInt)
      (hsame : (a ∈ T.cells ↔ a + ⟨0, 1⟩ ∈ T.cells)) := SquareUnionProof.north_side_not_boundary
          T pair_eq_cases a hsame
  have boundary_edge_adjacent (i : Fin (n + 3))
      (he : ({v i, v (i + 1)} : Finset GaussianInt) ∈ BoundaryFootprintEdges T) :=
          SquareUnionProof.boundary_edge_adjacent T n v
          edge_support pair_eq_cases i he
  have boundary_carrier_has_integer_coordinate (q : Real × Real) (hq : q ∈ C) :=
      SquareUnionProof.boundary_carrier_has_integer_coordinate T n p v hvertex hedges
          edge_support pair_eq_cases SquareUnionDetails.horizontal_segment_y
              SquareUnionDetails.vertical_segment_x q hq
  have east_same_center_segment_avoids (a : GaussianInt)
      (hsame : (a ∈ T.cells ↔ a + 1 ∈ T.cells)) :=
          SquareUnionProof.east_same_center_segment_avoids T n p v hvertex hedges
          east_side_not_boundary boundary_edge_adjacent boundary_carrier_has_integer_coordinate a
          hsame
  have north_same_center_segment_avoids (a : GaussianInt)
      (hsame : (a ∈ T.cells ↔ a + ⟨0, 1⟩ ∈ T.cells)) :=
          SquareUnionProof.north_same_center_segment_avoids T n p v hvertex hedges
          north_side_not_boundary boundary_edge_adjacent boundary_carrier_has_integer_coordinate
          a hsame
  have occupied_same_adjacent_avoid (a b : GaussianInt)
      (hab : FourNeighborAdjacent a b)
      (ha : a ∈ T.cells) (hb : b ∈ T.cells) := SquareUnionProof.occupied_same_adjacent_avoid T n
          p east_same_center_segment_avoids
          north_same_center_segment_avoids a b hab ha hb
  have occupied_adjacent_same_domain (a b : GaussianInt)
      (hab : FourNeighborAdjacent a b) (ha : a ∈ T.cells) (hb : b ∈ T.cells) :=
          SquareUnionProof.occupied_adjacent_same_domain T n
          p U V hdisjoint segment_stays_on_one_side occupied_same_adjacent_avoid a b hab ha hb
  have list_occupied_center_transport := SquareUnionProof.list_occupied_center_transport T
          U occupied_adjacent_same_domain
  let inOpenCell : GaussianInt → (Real × Real) → Prop := fun c q =>
    (c.re : Real) < q.1 ∧ q.1 < (c.re : Real) + 1 ∧
      (c.im : Real) < q.2 ∧ q.2 < (c.im : Real) + 1
  have boundary_disjoint_open_cell (c : GaussianInt) (q : Real × Real)
      (hq : q ∈ C) (hcell : inOpenCell c q) := SquareUnionProof.boundary_disjoint_open_cell n p
          boundary_carrier_has_integer_coordinate c q hq hcell
  have open_cell_segment_subset (c : GaussianInt) (x y : Real × Real)
      (hx : inOpenCell c x) (hy : inOpenCell c y) := SquareUnionProof.open_cell_segment_subset c
          x y hx hy
  have center_to_square_point_avoid (c : GaussianInt) (q : Real × Real)
      (hq : q ∈ ClosedSquareRealization c) (hqC : q ∉ C) :=
          SquareUnionProof.center_to_square_point_avoid n p
          boundary_disjoint_open_cell c q hq hqC
  have square_point_same_domain (c : GaussianInt) (q : Real × Real)
      (hq : q ∈ ClosedSquareRealization c) (hqC : q ∉ C) :=
          SquareUnionProof.square_point_same_domain n p U V hdisjoint
          segment_stays_on_one_side center_to_square_point_avoid c q hq hqC
  have center_in_open_cell (c : GaussianInt) := SquareUnionDetails.center_in_open_cell c
  have open_complement_cell_in_V (c : GaussianInt) (hc : c ∉ T.cells)
      (q : Real × Real) (hq : inOpenCell c q) := SquareUnionProof.open_complement_cell_in_V T n p
          U V hdisjoint
          segment_stays_on_one_side every_complement_center_in_V boundary_disjoint_open_cell
          open_cell_segment_subset center_in_open_cell c hc q hq
  obtain ⟨seed, hseed, hseedMax⟩ := T.cells.exists_max_image (fun z => z.re) hinside.1
  have eastSeedEmpty := SquareUnionDetails.eastSeedEmpty T seed hseedMax
  have eastSeedEdge := SquareUnionDetails.eastSeedEdge T seed hseed eastSeedEmpty
  let qSeed : Real × Real := ((seed.re : Real) + 1, (seed.im : Real) + 1 / 2)
  have qSeedSide := SquareUnionProof.qSeedSide seed
  have qSeedC : qSeed ∈ C :=
    boundary_side_segment_in_C _ eastSeedEdge _ _ rfl (by
      intro h
      have hi := congrArg (fun z : GaussianInt => z.im) h
      simp at hi) qSeed qSeedSide
  have qSeedFront := SquareUnionDetails.qSeedFront n p U hfrontU seed qSeedC
  have qSeedClosure : qSeed ∈ closure U := frontier_subset_closure qSeedFront
  obtain ⟨r, hrU, hrdist⟩ :=
    (Metric.mem_closure_iff.mp qSeedClosure) (1 / 4) (by norm_num)
  have hdist : max |qSeed.1 - r.1| |qSeed.2 - r.2| < (1 / 4 : Real) := by
    simpa [Prod.dist_eq, Real.dist_eq, qSeed] using hrdist
  have hdx : |qSeed.1 - r.1| < (1 / 4 : Real) := (max_lt_iff.mp hdist).1
  have hdy : |qSeed.2 - r.2| < (1 / 4 : Real) := (max_lt_iff.mp hdist).2
  have hrxLower := SquareUnionDetails.hrxLower seed r hdx
  have hrxUpper := SquareUnionDetails.hrxUpper seed r hdx
  have hryLower := SquareUnionDetails.hryLower seed r hdy
  have hryUpper := SquareUnionDetails.hryUpper seed r hdy hryLower
  have rnotC := SquareUnionDetails.rnotC n p U V hcover r hrU
  have hrNotSide := SquareUnionDetails.hrNotSide T n p boundary_side_segment_in_C seed
      eastSeedEdge r hryLower hryUpper rnotC
  have seedCenterU := SquareUnionDetails.seedCenterU T n p U V hdisjoint
      segment_stays_on_one_side boundary_disjoint_open_cell open_cell_segment_subset
      center_in_open_cell open_complement_cell_in_V seed eastSeedEmpty r hrU hrxLower hrxUpper
      hryLower hryUpper hrNotSide
  have every_occupied_center_in_U (z : GaussianInt) (hz : z ∈ T.cells) :=
      SquareUnionDetails.every_occupied_center_in_U T hinside U list_occupied_center_transport
      seed hseed seedCenterU z hz
  have tile_cover := SquareUnionDetails.tile_cover T n p U V hdisjoint boundary_carrier_in_tile
      every_complement_center_in_V square_point_same_domain every_occupied_center_in_U
  exact tile_cover


theorem P3475T1SquareUnionIdentification :
    ∀ (T : ProtoTile), (FourNeighborConnected (T.cells : Set LatticeCell)) →
        ((FourNeighborConnected ((T.cells : Set LatticeCell)ᶜ)) → (∀ {n : Nat}, ∀ (p :
        P3381T1PolygonBoundary n), ∀ (v : Fin (n + 3) → GaussianInt), (∀ i, p.vertex i =
        GaussianRealPoint (v i)) → ((BoundaryFootprintEdges T = {e | ∃ i, e = {v i, v (i + 1)}})
        → (∀ (U : Set (Real × Real)), ∀ (V : Set (Real × Real)), (IsOpen U) → ((IsConnected U) →
        ((Bornology.IsBounded U) → ((IsOpen V) → ((IsConnected V) → ((¬ Bornology.IsBounded V) →
        ((Disjoint U V) → ((U ∪ V = (⋃ i, segment Real (p.vertex i) (p.vertex (i + 1)))ᶜ) →
        ((frontier U = ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1))) → ((frontier V = ⋃ i,
        segment Real (p.vertex i) (p.vertex (i + 1))) → (TileRealization T = U ∪ ⋃ i, segment
        Real (p.vertex i) (p.vertex (i + 1)))))))))))))))) := by
  intro T hinside houtside n p v hvertex hedges U V hUopen hUconn hUbounded hVopen hVconn
      hVunbounded hdisjoint hcover hfrontU hfrontV
-- BODY
  classical
  let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1));
  have edge_support (e : Finset GaussianInt) (he : e ∈ BoundaryFootprintEdges T) :=
      SquareUnionProof.edge_support T e he
  have edge_endpoint_square (z : GaussianInt) (e : Finset GaussianInt)
      (he : e = {z, z + 1} ∨ e = {z, z + ⟨0, 1⟩} ∨
        e = {z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩} ∨
        e = {z + 1, z + 1 + ⟨0, 1⟩})
      (w : GaussianInt) (hw : w ∈ e) := SquareUnionProof.edge_endpoint_square z
          e he w hw
  have boundary_carrier_in_tile := SquareUnionProof.boundary_carrier_in_tile T n p v hvertex
      hedges edge_support
      edge_endpoint_square
  have segment_stays_on_one_side (a b : Real × Real)
      (havoid : segment ℝ a b ⊆ Cᶜ) := SquareUnionProof.segment_stays_on_one_side n p U V
        hUopen hVopen hdisjoint hcover a b havoid
  let cellCenter : GaussianInt → Real × Real := fun z =>
    ((z.re : Real) + (1 / 2 : Real), (z.im : Real) + (1 / 2 : Real))
  have every_complement_center_in_V (z : GaussianInt) (hz : z ∉ T.cells) :
      cellCenter z ∈ V := SquareDomainBlocks.every_complement_center_in_V T hinside houtside n p
          U V hUbounded hdisjoint hcover boundary_carrier_in_tile segment_stays_on_one_side z hz
  exact identificationFromExteriorCenters T hinside p v hvertex hedges U V
    hUopen hVopen hdisjoint hcover hfrontU every_complement_center_in_V

end ApollonianSuperharmonic

end
