/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.CommonFootprintEdgeVertices
public import LeanPool.ApollonianSuperharmonic.ClosedSquareRealization
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.GridEdgeCarrier
public import LeanPool.ApollonianSuperharmonic.ProtoTile
public import LeanPool.ApollonianSuperharmonic.TileRealization

-- [TABLET NODE: DisjointSquareUnionCommonEdgeCarrier]

/-!
# DisjointSquareUnionCommonEdgeCarrier

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SquareUnionCommonCarrierConstruction

private noncomputable abbrev I : GaussianInt := by
  classical
  exact ⟨0, 1⟩

private theorem footprint_finite (T : ProtoTile) : (FootprintEdges T).Finite := by
  classical
  let I : GaussianInt := ⟨0, 1⟩
  let edge : T.cells × (Bool × Bool) → Finset GaussianInt := fun q =>
    match q.2 with
    | (false, false) => {q.1.1, q.1.1 + 1}
    | (false, true) => {q.1.1, q.1.1 + I}
    | (true, false) => {q.1.1 + 1, q.1.1 + 1 + I}
    | (true, true) => {q.1.1 + I, q.1.1 + 1 + I}
  apply (Set.finite_range edge).subset
  rintro e ⟨c, hc, h | h | h | h⟩
  · exact ⟨(⟨c, hc⟩, false, false), by simpa [edge] using h.symm⟩
  · exact ⟨(⟨c, hc⟩, false, true), by simpa [edge, I] using h.symm⟩
  · exact ⟨(⟨c, hc⟩, true, false), by simpa [edge, I] using h.symm⟩
  · exact ⟨(⟨c, hc⟩, true, true), by simpa [edge, I] using h.symm⟩

private theorem edge_endpoint_square (c : LatticeCell) (e : Finset GaussianInt)
      (he : e = {c, c + 1} ∨ e = {c, c + I} ∨
        e = {c + 1, c + 1 + I} ∨ e = {c + I, c + 1 + I})
      (z : GaussianInt) (hz : z ∈ e) :
      GaussianRealPoint z ∈ ClosedSquareRealization c := by
  classical
  let I : GaussianInt := ⟨0, 1⟩
  rcases he with rfl | rfl | rfl | rfl
  all_goals simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  all_goals rcases hz with rfl | rfl
  all_goals simp [GaussianRealPoint, ClosedSquareRealization, Prod.le_def]

private theorem edge_carrier_subset (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ FootprintEdges T) : GridEdgeCarrier e ⊆ TileRealization T := by
  classical
  let I : GaussianInt := ⟨0, 1⟩
  have edge_endpoint_square (c : LatticeCell) (e : Finset GaussianInt)
      (he : e = {c, c + 1} ∨ e = {c, c + I} ∨
        e = {c + 1, c + 1 + I} ∨ e = {c + I, c + 1 + I})
      (z : GaussianInt) (hz : z ∈ e) :
      GaussianRealPoint z ∈ ClosedSquareRealization c := edge_endpoint_square c e he z hz
  rintro p hp
  rcases he with ⟨c, hc, he⟩
  rw [TileRealization]
  refine Set.mem_iUnion.2 ⟨c, Set.mem_iUnion.2 ⟨hc, ?_⟩⟩
  unfold GridEdgeCarrier at hp
  rcases Set.mem_iUnion.1 hp with ⟨x, hp⟩
  rcases Set.mem_iUnion.1 hp with ⟨hx, hp⟩
  rcases Set.mem_iUnion.1 hp with ⟨y, hp⟩
  rcases Set.mem_iUnion.1 hp with ⟨hy, hp⟩
  have hxSq := edge_endpoint_square c e he x hx
  have hySq := edge_endpoint_square c e he y hy
  change GaussianRealPoint x ⊓ GaussianRealPoint y ≤ p ∧
    p ≤ GaussianRealPoint x ⊔ GaussianRealPoint y at hp
  change (((c.re : Int) : Real), ((c.im : Int) : Real)) ≤ p ∧
    p ≤ ((((c.re : Int) : Real) + 1), (((c.im : Int) : Real) + 1))
  exact ⟨le_trans (le_inf hxSq.1 hySq.1) hp.1,
    le_trans hp.2 (sup_le hxSq.2 hySq.2)⟩

end SquareUnionCommonCarrierConstruction

theorem DisjointSquareUnionCommonEdgeCarrier (U V : ProtoTile)
    (hdisjoint : Disjoint U.cells V.cells)
    (hvertices : FootprintVertices U ∩ FootprintVertices V =
      CommonFootprintEdgeVertices U V) :
    (FootprintEdges U ∩ FootprintEdges V).Finite ∧
      TileRealization U ∩ TileRealization V =
        ⋃ e ∈ FootprintEdges U ∩ FootprintEdges V, GridEdgeCarrier e := by
-- BODY
  classical
  let I : GaussianInt := ⟨0, 1⟩
  have footprint_finite (T : ProtoTile) : (FootprintEdges T).Finite :=
      SquareUnionCommonCarrierConstruction.footprint_finite T
  have edge_endpoint_square (c : LatticeCell) (e : Finset GaussianInt)
      (he : e = {c, c + 1} ∨ e = {c, c + I} ∨
        e = {c + 1, c + 1 + I} ∨ e = {c + I, c + 1 + I})
      (z : GaussianInt) (hz : z ∈ e) :
      GaussianRealPoint z ∈ ClosedSquareRealization c :=
          SquareUnionCommonCarrierConstruction.edge_endpoint_square c e he z hz
  have edge_carrier_subset (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ FootprintEdges T) : GridEdgeCarrier e ⊆ TileRealization T :=
          SquareUnionCommonCarrierConstruction.edge_carrier_subset T e he
  have carrier_of_endpoints (p : Real × Real) (e : Finset GaussianInt)
      (x y : GaussianInt) (hx : x ∈ e) (hy : y ∈ e)
      (hp : p ∈ Set.uIcc (GaussianRealPoint x) (GaussianRealPoint y)) :
      p ∈ GridEdgeCarrier e := by
    unfold GridEdgeCarrier
    exact Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨hx,
      Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hy, hp⟩⟩⟩⟩
  refine ⟨(footprint_finite U).inter_of_left (FootprintEdges V), ?_⟩
  apply Set.Subset.antisymm
  · rintro p ⟨hpU, hpV⟩
    simp only [TileRealization, Set.mem_iUnion] at hpU hpV
    rcases hpU with ⟨c, hc, hpc⟩
    rcases hpV with ⟨d, hd, hpd⟩
    have hcd : c ≠ d := fun h =>
      (Finset.disjoint_left.mp hdisjoint) hc (h ▸ hd)
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hpc hpd
    have hrlo : (-1 : ℝ) ≤ (c.re : ℝ) - d.re := by
      linarith [hpc.1.1, hpd.1.2]
    have hrhi : (c.re : ℝ) - d.re ≤ 1 := by
      linarith [hpc.1.2, hpd.1.1]
    have hilo : (-1 : ℝ) ≤ (c.im : ℝ) - d.im := by
      linarith [hpc.2.1, hpd.2.2]
    have hihi : (c.im : ℝ) - d.im ≤ 1 := by
      linarith [hpc.2.2, hpd.2.1]
    have rlo : (-1 : ℤ) ≤ c.re - d.re := by exact_mod_cast hrlo
    have rhi : c.re - d.re ≤ (1 : ℤ) := by exact_mod_cast hrhi
    have ilo : (-1 : ℤ) ≤ c.im - d.im := by exact_mod_cast hilo
    have ihi : c.im - d.im ≤ (1 : ℤ) := by exact_mod_cast hihi
    have rd : c.re - d.re = -1 ∨ c.re - d.re = 0 ∨ c.re - d.re = 1 := by
      omega
    have id : c.im - d.im = -1 ∨ c.im - d.im = 0 ∨ c.im - d.im = 1 := by
      omega
    have corner_case (z : GaussianInt) (hzU : z ∈ FootprintVertices U)
        (hzV : z ∈ FootprintVertices V) (hpz : p = GaussianRealPoint z) :
        p ∈ ⋃ e ∈ FootprintEdges U ∩ FootprintEdges V, GridEdgeCarrier e := by
      have hz : z ∈ CommonFootprintEdgeVertices U V := by
        rw [← hvertices]
        exact ⟨hzU, hzV⟩
      rcases hz with ⟨e, he, hze⟩
      refine Set.mem_iUnion.2 ⟨e, Set.mem_iUnion.2 ⟨he, ?_⟩⟩
      apply carrier_of_endpoints p e z z hze hze
      rw [hpz]
      exact Set.mem_uIcc_of_le le_rfl le_rfl
    rcases rd with hr | hr | hr <;> rcases id with hi | hi | hi
    · have hdrel : d = c + 1 + I := by
        apply Zsqrtd.ext <;> simp [I] <;> omega
      subst d
      have hpz : p = GaussianRealPoint (c + 1 + I) := by
        apply Prod.ext <;> simp only [GaussianRealPoint]
        · norm_num [I] at hpc hpd ⊢
          linarith
        · norm_num [I] at hpc hpd ⊢
          linarith
      apply corner_case (c + 1 + I)
      · unfold FootprintVertices
        rw [ite_eq_left ⟨c, hc⟩]
        exact ⟨c, hc, Or.inr (Or.inr (Or.inr rfl))⟩
      · unfold FootprintVertices
        rw [ite_eq_left ⟨c + 1 + I, hd⟩]
        exact ⟨c + 1 + I, hd, Or.inl rfl⟩
      · exact hpz
    · have hdrel : d = c + 1 := by
        apply Zsqrtd.ext <;> simp [] <;> omega
      subst d
      let e : Finset GaussianInt := {c + 1, c + 1 + I}
      have heU : e ∈ FootprintEdges U := by
        exact ⟨c, hc, Or.inr (Or.inr (Or.inl rfl))⟩
      have heV : e ∈ FootprintEdges V := by
        exact ⟨c + 1, hd, Or.inr (Or.inl rfl)⟩
      refine Set.mem_iUnion.2 ⟨e, Set.mem_iUnion.2 ⟨⟨heU, heV⟩, ?_⟩⟩
      apply carrier_of_endpoints p e (c + 1) (c + 1 + I) (by simp [e]) (by simp [e])
      simp only [Set.uIcc, Set.mem_Icc, GaussianRealPoint, Prod.le_def]
      norm_num [I] at hpc hpd ⊢
      constructor <;> constructor <;> linarith
    · have hdrel : d = c + 1 - I := by
        apply Zsqrtd.ext <;> simp [I] <;> omega
      subst d
      have hpz : p = GaussianRealPoint (c + 1) := by
        apply Prod.ext <;> simp only [GaussianRealPoint]
        · norm_num [I] at hpc hpd ⊢
          linarith
        · norm_num [I] at hpc hpd ⊢
          linarith
      apply corner_case (c + 1)
      · unfold FootprintVertices
        rw [ite_eq_left ⟨c, hc⟩]
        exact ⟨c, hc, Or.inr (Or.inl rfl)⟩
      · unfold FootprintVertices
        rw [ite_eq_left ⟨c + 1 - I, hd⟩]
        refine ⟨c + 1 - I, hd, Or.inr (Or.inr (Or.inl ?_))⟩
        simp [I]
      · exact hpz
    · have hdrel : d = c + I := by
        apply Zsqrtd.ext <;> simp [I] <;> omega
      subst d
      let e : Finset GaussianInt := {c + I, c + 1 + I}
      have heU : e ∈ FootprintEdges U := by
        exact ⟨c, hc, Or.inr (Or.inr (Or.inr rfl))⟩
      have heV : e ∈ FootprintEdges V := by
        refine ⟨c + I, hd, Or.inl ?_⟩
        simp [e, I, add_comm, add_left_comm, add_assoc]
      refine Set.mem_iUnion.2 ⟨e, Set.mem_iUnion.2 ⟨⟨heU, heV⟩, ?_⟩⟩
      apply carrier_of_endpoints p e (c + I) (c + 1 + I) (by simp [e]) (by simp [e])
      simp only [Set.uIcc, Set.mem_Icc, GaussianRealPoint, Prod.le_def]
      norm_num [I] at hpc hpd ⊢
      constructor <;> constructor <;> linarith
    · exfalso
      apply hcd
      exact Zsqrtd.ext (by omega) (by omega)
    · have hdrel : d = c - I := by
        apply Zsqrtd.ext <;> simp [I] <;> omega
      subst d
      let e : Finset GaussianInt := {c, c + 1}
      have heU : e ∈ FootprintEdges U := ⟨c, hc, Or.inl rfl⟩
      have heV : e ∈ FootprintEdges V := by
        refine ⟨c - I, hd, Or.inr (Or.inr (Or.inr ?_))⟩
        simp [e, I, add_comm, add_left_comm]
      refine Set.mem_iUnion.2 ⟨e, Set.mem_iUnion.2 ⟨⟨heU, heV⟩, ?_⟩⟩
      apply carrier_of_endpoints p e c (c + 1) (by simp [e]) (by simp [e])
      simp only [Set.uIcc, Set.mem_Icc, GaussianRealPoint, Prod.le_def]
      norm_num [I] at hpc hpd ⊢
      constructor <;> constructor <;> linarith
    · have hdrel : d = c - 1 + I := by
        apply Zsqrtd.ext <;> simp [I] <;> omega
      subst d
      have hpz : p = GaussianRealPoint (c + I) := by
        apply Prod.ext <;> simp only [GaussianRealPoint]
        · norm_num [I] at hpc hpd ⊢
          linarith
        · norm_num [I] at hpc hpd ⊢
          linarith
      apply corner_case (c + I)
      · unfold FootprintVertices
        rw [ite_eq_left ⟨c, hc⟩]
        exact ⟨c, hc, Or.inr (Or.inr (Or.inl rfl))⟩
      · unfold FootprintVertices
        rw [ite_eq_left ⟨c - 1 + I, hd⟩]
        refine ⟨c - 1 + I, hd, Or.inr (Or.inl ?_)⟩
        simp [I, Zsqrtd.ext_iff]
      · exact hpz
    · have hdrel : d = c - 1 := by
        apply Zsqrtd.ext <;> simp [] <;> omega
      subst d
      let e : Finset GaussianInt := {c, c + I}
      have heU : e ∈ FootprintEdges U := ⟨c, hc, Or.inr (Or.inl rfl)⟩
      have heV : e ∈ FootprintEdges V := by
        refine ⟨c - 1, hd, Or.inr (Or.inr (Or.inl ?_))⟩
        simp [e, I]
      refine Set.mem_iUnion.2 ⟨e, Set.mem_iUnion.2 ⟨⟨heU, heV⟩, ?_⟩⟩
      apply carrier_of_endpoints p e c (c + I) (by simp [e]) (by simp [e])
      simp only [Set.uIcc, Set.mem_Icc, GaussianRealPoint, Prod.le_def]
      norm_num [I] at hpc hpd ⊢
      constructor <;> constructor <;> linarith
    · have hdrel : d = c - 1 - I := by
        apply Zsqrtd.ext <;> simp [I] <;> omega
      subst d
      have hpz : p = GaussianRealPoint c := by
        apply Prod.ext <;> simp only [GaussianRealPoint]
        · norm_num [I] at hpc hpd ⊢
          linarith
        · norm_num [I] at hpc hpd ⊢
          linarith
      apply corner_case c
      · unfold FootprintVertices
        rw [ite_eq_left ⟨c, hc⟩]
        exact ⟨c, hc, Or.inl rfl⟩
      · unfold FootprintVertices
        rw [ite_eq_left ⟨c - 1 - I, hd⟩]
        refine ⟨c - 1 - I, hd, Or.inr (Or.inr (Or.inr ?_))⟩
        simp [I, Zsqrtd.ext_iff]
      · exact hpz
  · rintro p hp
    rcases Set.mem_iUnion.1 hp with ⟨e, hp⟩
    rcases Set.mem_iUnion.1 hp with ⟨he, hp⟩
    exact ⟨edge_carrier_subset U e he.1 hp,
      edge_carrier_subset V e he.2 hp⟩

end ApollonianSuperharmonic

end
