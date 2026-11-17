/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3544T1RayParity
public import LeanPool.ApollonianSuperharmonic.P3381T1TriangleDeterminant
public import Mathlib.Topology.Connected.PathConnected
public import LeanPool.ApollonianSuperharmonic.P3597T1VertexSectors

-- [TABLET NODE: P3544T1LocalParity]

/-!
# P3544T1LocalParity

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3544T1LocalParity {n : Nat} (p : P3381T1PolygonBoundary n) :
    closure (P3544T1RayParity p) =
      P3544T1RayParity p ∪ P3544T1BoundaryCarrier p ∧
    IsOpen (P3544T1RayParity p) ∧
    interior (P3544T1RayParity p ∪ P3544T1BoundaryCarrier p) =
      P3544T1RayParity p ∧
    frontier (P3544T1RayParity p ∪ P3544T1BoundaryCarrier p) =
      P3544T1BoundaryCarrier p ∧
    (∀ x, x ∉ P3544T1BoundaryCarrier p →
      ∃ r : Real, 0 < r ∧
        (Metric.ball x r ⊆ P3544T1RayParity p ∨
          Disjoint (Metric.ball x r) (P3544T1RayParity p))) ∧
    (∀ x, x ∉ P3544T1BoundaryCarrier p → ∃ d : Real × Real,
      (∀ i, d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1 ≠ 0) ∧
      (∀ i, d.1 * (p.vertex (i + 1) - p.vertex i).2 -
        d.2 * (p.vertex (i + 1) - p.vertex i).1 ≠ 0)) ∧
    (∀ x d : Real × Real, x ∉ P3544T1BoundaryCarrier p →
      (∀ i, d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1 ≠ 0) →
      (∀ i, d.1 * (p.vertex (i + 1) - p.vertex i).2 -
        d.2 * (p.vertex (i + 1) - p.vertex i).1 ≠ 0) →
      (x ∈ P3544T1RayParity p ↔
        Set.ncard {i : Fin (n + 3) | ∃ t : Real, 0 < t ∧
          x + t • d ∈ segment Real (p.vertex i) (p.vertex (i + 1))} % 2 = 1)) ∧
    (∀ i, ∃ r : Real, 0 < r ∧
      IsPathConnected (Metric.ball (p.vertex i) r ∩ P3544T1RayParity p) ∧
      IsPathConnected (Metric.ball (p.vertex i) r \
        (P3544T1RayParity p ∪ P3544T1BoundaryCarrier p))) ∧
    (∀ i x, x ∈ openSegment Real (p.vertex i) (p.vertex (i + 1)) →
      ∃ r : Real, 0 < r ∧ ∃ s : Bool, ∀ y ∈ Metric.ball x r,
        (y ∈ P3544T1RayParity p ↔
          if s then 0 < P3381T1TriangleDeterminant
            ![p.vertex i, p.vertex (i + 1), y]
          else P3381T1TriangleDeterminant
            ![p.vertex i, p.vertex (i + 1), y] < 0)) := by
-- BODY
  classical
  let O := P3544T1RayParity p
  let C := P3544T1BoundaryCarrier p
  have hgeneric : ∀ x : Real × Real, x ∉ C → ∃ d : Real × Real,
      (∀ i, d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1 ≠ 0) ∧
      (∀ i, d.1 * (p.vertex (i + 1) - p.vertex i).2 -
        d.2 * (p.vertex (i + 1) - p.vertex i).1 ≠ 0) := by
    intro x hx
    apply (P3597T1GenericRayStability p).1 x
    intro i hi
    have hv : p.vertex i ∈ C := by
      exact Set.mem_iUnion.mpr ⟨i, left_mem_segment Real _ _⟩
    exact hx (hi ▸ hv)
  have hparity : ∀ x d : Real × Real, x ∉ C →
      (∀ i, d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1 ≠ 0) →
      (∀ i, d.1 * (p.vertex (i + 1) - p.vertex i).2 -
        d.2 * (p.vertex (i + 1) - p.vertex i).1 ≠ 0) →
      (x ∈ O ↔ Set.ncard {i : Fin (n + 3) | ∃ t : Real, 0 < t ∧
        x + t • d ∈ segment Real (p.vertex i) (p.vertex (i + 1))} % 2 = 1) := by
    intro x d hx hdv hde
    constructor
    · rintro ⟨_, d', hdv', hde', hodd⟩
      exact (P3597T1DirectionParity p x d d' hx hdv hdv').trans hodd
    · intro hodd
      exact ⟨hx, d, hdv, hde, hodd⟩
  have hlocal : ∀ x : Real × Real, x ∉ C → ∃ r : Real, 0 < r ∧
      ∀ y ∈ Metric.ball x r, y ∉ C ∧ (y ∈ O ↔ x ∈ O) := by
    intro x hx
    obtain ⟨d, hdv, hde⟩ := hgeneric x hx
    obtain ⟨r, hr, hstable⟩ := (P3597T1GenericRayStability p).2.1 x d hx hdv hde
    refine ⟨r, hr, ?_⟩
    intro y hy
    obtain ⟨hyC, hdy, hsides⟩ := hstable y hy
    refine ⟨hyC, ?_⟩
    have hcount : Set.ncard {i : Fin (n + 3) | ∃ t : Real, 0 < t ∧
          y + t • d ∈ segment Real (p.vertex i) (p.vertex (i + 1))} % 2 =
        Set.ncard {i : Fin (n + 3) | ∃ t : Real, 0 < t ∧
          x + t • d ∈ segment Real (p.vertex i) (p.vertex (i + 1))} % 2 :=
      congrArg (fun S : Set (Fin (n + 3)) => Set.ncard S % 2) (Set.ext hsides)
    rw [hparity y d hyC hdy hde, hparity x d hx hdv hde, hcount]
  have hballs : ∀ x : Real × Real, x ∉ C → ∃ r : Real, 0 < r ∧
      (Metric.ball x r ⊆ O ∨ Disjoint (Metric.ball x r) O) := by
    intro x hx
    obtain ⟨r, hr, hball⟩ := hlocal x hx
    refine ⟨r, hr, ?_⟩
    by_cases ho : x ∈ O
    · exact Or.inl (fun y hy => (hball y hy).2.mpr ho)
    · exact Or.inr (Set.disjoint_left.mpr (fun y hy hyo => ho ((hball y hy).2.mp hyo)))
  have hdisjoint : Disjoint O C :=
    Set.disjoint_left.mpr (fun _ ho hc => ho.1 hc)
  have hO : IsOpen O := by
    apply Metric.isOpen_iff.mpr
    intro x hx
    obtain ⟨r, hr, hball⟩ := hlocal x hx.1
    exact ⟨r, hr, fun y hy => (hball y hy).2.mpr hx⟩
  have hE : IsOpen (O ∪ C)ᶜ := by
    apply Metric.isOpen_iff.mpr
    intro x hx
    obtain ⟨r, hr, hball⟩ := hlocal x (fun hc => hx (Or.inr hc))
    refine ⟨r, hr, ?_⟩
    intro y hy hmem
    rcases hmem with hyo | hyc
    · exact hx (Or.inl ((hball y hy).2.mp hyo))
    · exact (hball y hy).1 hyc
  have hvertices : ∀ i, ∃ r : Real, 0 < r ∧
      IsPathConnected (Metric.ball (p.vertex i) r ∩ O) ∧
      IsPathConnected (Metric.ball (p.vertex i) r \ (O ∪ C)) := by
    intro i
    obtain ⟨r, hr, hodd, heven, _, _⟩ := P3597T1VertexSectors p i
    exact ⟨r, hr, hodd, heven⟩
  have hsides : ∀ i x, x ∈ openSegment Real (p.vertex i) (p.vertex (i + 1)) →
      ∃ r : Real, 0 < r ∧ ∃ s : Bool, ∀ y ∈ Metric.ball x r,
        (y ∈ O ↔ if s then 0 < P3381T1TriangleDeterminant
          ![p.vertex i, p.vertex (i + 1), y]
        else P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i + 1), y] < 0) := by
    intro i x hx
    obtain ⟨r, hr, hsign, _, _⟩ := P3597T1SideCrossing p i x hx
    exact ⟨r, hr, hsign⟩
  have haccumulation : ∀ x ∈ C, x ∈ closure O ∧ x ∈ closure (O ∪ C)ᶜ := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    by_cases hleft : p.vertex i = x
    · obtain ⟨_, _, _, _, hodd, heven⟩ := P3597T1VertexSectors p i
      exact hleft ▸ ⟨hodd, heven⟩
    by_cases hright : p.vertex (i + 1) = x
    · obtain ⟨_, _, _, _, hodd, heven⟩ := P3597T1VertexSectors p (i + 1)
      exact hright ▸ ⟨hodd, heven⟩
    · have hopen := mem_openSegment_of_ne_left_right hleft hright hi
      obtain ⟨_, _, _, hodd, heven⟩ := P3597T1SideCrossing p i x hopen
      exact ⟨hodd, heven⟩
  have hodd : C ⊆ closure O := fun x hx => (haccumulation x hx).1
  have heven : C ⊆ closure (O ∪ C)ᶜ := fun x hx => (haccumulation x hx).2
  -- The boundary identities use only the local odd/even accumulation.
  have hclosed : IsClosed (O ∪ C) := by
    simpa only [compl_compl] using hE.isClosed_compl
  have hclosure : closure O = O ∪ C :=
    (closure_minimal Set.subset_union_left hclosed).antisymm
      (Set.union_subset subset_closure hodd)
  have hinterior : interior (O ∪ C) = O := by
    apply Set.Subset.antisymm _ (interior_maximal Set.subset_union_left hO)
    intro x hx
    rcases interior_subset hx with ho | hc
    · exact ho
    · have hnot : x ∉ closure (O ∪ C)ᶜ := by
        simpa only [interior_eq_compl_closure_compl, Set.mem_compl_iff] using hx
      exact False.elim (hnot (heven hc))
  have hfrontier : frontier (O ∪ C) = C := by
    rw [frontier, hclosed.closure_eq, hinterior]
    ext x
    constructor
    · rintro ⟨h, hn⟩
      exact h.resolve_left hn
    · intro hc
      exact ⟨Or.inr hc, fun ho => Set.disjoint_left.mp hdisjoint ho hc⟩
  exact ⟨hclosure, hO, hinterior, hfrontier, hballs, hgeneric, hparity, hvertices, hsides⟩

end ApollonianSuperharmonic

end
