/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.GlobalOdometerExtends
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian
public import LeanPool.ApollonianSuperharmonic.TileOdometerTranslationUniqueness

-- [TABLET NODE: P4120T1AffineComparison]

/-!
# P4120T1AffineComparison

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4120T1AffineComparison
    (C : CircleCoordinates) (T U : ProtoTile) (h k : PartialOdometer)
    (g f : IntegerLatticeFunction) (hC : 0 < C.1)
    (hodo : TileOdometer C T h) (kodo : TileOdometer C U k)
    (hext : GlobalOdometerExtends g h)
    (hf : ∀ z, z ∈ k.domain → k.value z = f z)
    (x : GaussianInt) (hx : x ∈ FootprintVertices T)
    (hxb : x ∉ BoundaryFootprintVertices T) :
    ∃ u : GaussianInt,
      T.cells = (TileTranslation U u).cells ∧
      (T.cells = ∅ → T.anchor = (TileTranslation U u).anchor) ∧
      FourNeighborLaplacian g x = FourNeighborLaplacian f (x - u) := by
-- BODY
  classical
  obtain ⟨u, ⟨hcell, hanchor, a, b, hdom, hvalue⟩, _⟩ :=
    TileOdometerTranslationUniqueness C T U h k hC hodo kodo
  obtain ⟨c, hc⟩ := hext
  have hne : T.cells.Nonempty := by
    by_contra hn
    simp only [FootprintVertices, ite_eq_right hn, Set.mem_singleton_iff] at hx
    apply hxb
    simp [BoundaryFootprintVertices, hn, hx]
  have hsome : ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells := by
    rw [FootprintVertices, ite_eq_left hne] at hx
    rcases hx with ⟨y, hy, rfl | rfl | rfl | rfl⟩
    · exact ⟨0, by simpa [LatticeVertexIncidentCell] using hy⟩
    · exact ⟨1, by simpa [LatticeVertexIncidentCell] using hy⟩
    · exact ⟨3, by simpa [LatticeVertexIncidentCell] using hy⟩
    · refine ⟨2, ?_⟩
      simpa [LatticeVertexIncidentCell, sub_eq_add_neg,
        add_assoc, add_comm, add_left_comm] using hy
  have hall : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells := by
    intro j
    by_contra hj
    exact hxb (P3161T2IncidentBoundary T x hsome ⟨j, hj⟩)
  have cells : x ∈ T.cells ∧ x - 1 ∈ T.cells ∧
      x - ⟨0, 1⟩ ∈ T.cells ∧ x - 1 - ⟨0, 1⟩ ∈ T.cells :=
    ⟨by simpa [LatticeVertexIncidentCell] using hall 0,
      by simpa [LatticeVertexIncidentCell] using hall 1,
      by simpa [LatticeVertexIncidentCell] using hall 3,
      by simpa [LatticeVertexIncidentCell] using hall 2⟩
  have value (z : GaussianInt) (hz : z ∈ FootprintVertices T) :
      g z = f (z - u) + a.re * z.re + a.im * z.im + b + c := by
    have hzh : z ∈ h.domain := by
      change z ∈ (h.domain : Set GaussianInt)
      rw [PositiveCurvatureTileOdometerDomain C T h hC hodo]
      exact hz
    rw [hc z hzh, hvalue z hzh, hf (z - u) ((hdom z).mp hzh)]
  have right_mem : x + 1 ∈ FootprintVertices T := by
    simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
    exact ⟨x, cells.1, Or.inr (Or.inl rfl)⟩
  have left_mem : x - 1 ∈ FootprintVertices T := by
    simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
    exact ⟨x - 1, cells.2.1, Or.inl rfl⟩
  have up_mem : x + ⟨0, 1⟩ ∈ FootprintVertices T := by
    simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
    exact ⟨x, cells.1, Or.inr (Or.inr (Or.inl rfl))⟩
  have down_mem : x - ⟨0, 1⟩ ∈ FootprintVertices T := by
    simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
    exact ⟨x - ⟨0, 1⟩, cells.2.2.1, Or.inl rfl⟩
  refine ⟨u, hcell, hanchor, ?_⟩
  simp only [FourNeighborLaplacian, value _ right_mem, value _ left_mem,
    value _ up_mem, value _ down_mem, value _ hx]
  have r : x + 1 - u = x - u + 1 := by abel
  have l : x - 1 - u = x - u - 1 := by abel
  have t : x + ⟨0, 1⟩ - u = x - u + ⟨0, 1⟩ := by abel
  have d : x - ⟨0, 1⟩ - u = x - u - ⟨0, 1⟩ := by abel
  rw [r, l, t, d]
  simp; ring

end ApollonianSuperharmonic

end
