/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4590T1RotationalDiskCenter
public import LeanPool.ApollonianSuperharmonic.P3776T1CellCenterMembership
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetric
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import LeanPool.ApollonianSuperharmonic.ClosedSquareRealization
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import Mathlib.Tactic.FinCases

-- [TABLET NODE: P4590T1CentralDiskSectors]

/-!
# P4590T1CentralDiskSectors

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4590T1CentralDiskSectors (T : ProtoTile) (hT : LatticeTile T)
    (hQ : QuarterTurnSymmetric T) (x : GaussianInt)
    (hcent : TileCentroid T = GaussianRealPoint x) :
    ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells := by
-- BODY
  have hc : GaussianRealPoint x ∈ TileRealization T := by
    apply P4590T1RotationalDiskCenter _ hT
    intro p hp
    simpa only [← hcent] using (hQ p).mp hp
  obtain ⟨a, hsq⟩ := Set.mem_iUnion.mp hc
  obtain ⟨ha, hsq⟩ := Set.mem_iUnion.mp hsq
  have haAt : a = x ∨ a = x - 1 ∨ a = x - 1 - ⟨0, 1⟩ ∨
      a = x - ⟨0, 1⟩ := by
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def,
      GaussianRealPoint] at hsq
    have hre : a.re = x.re ∨ a.re = x.re - 1 := by
      have h1 : a.re ≤ x.re := by exact_mod_cast hsq.1.1
      have h2 : x.re ≤ a.re + 1 := by exact_mod_cast hsq.2.1
      omega
    have him : a.im = x.im ∨ a.im = x.im - 1 := by
      have h1 : a.im ≤ x.im := by exact_mod_cast hsq.1.2
      have h2 : x.im ≤ a.im + 1 := by exact_mod_cast hsq.2.2
      omega
    rcases hre with hr | hr <;> rcases him with hi | hi
    · exact Or.inl (by ext <;> assumption)
    · exact Or.inr (Or.inr (Or.inr (by ext <;> simp_all)))
    · exact Or.inr (Or.inl (by ext <;> simp_all))
    · exact Or.inr (Or.inr (Or.inl (by ext <;> simp_all)))
  have rotate (j : Fin 4) (hj : LatticeVertexIncidentCell x j ∈ T.cells) :
      LatticeVertexIncidentCell x (j + 1) ∈ T.cells := by
    let p : Real × Real :=
      (((LatticeVertexIncidentCell x j).re : Real) + 1 / 2,
        ((LatticeVertexIncidentCell x j).im : Real) + 1 / 2)
    have hp := (hQ p).mp (by
      simpa only [p, GaussianRealPoint, Prod.mk_add_mk] using
        (P3776T1CellCenterMembership T _).mpr hj)
    rw [hcent] at hp
    have heq :
        ((GaussianRealPoint x).1 - (p.2 - (GaussianRealPoint x).2),
          (GaussianRealPoint x).2 + (p.1 - (GaussianRealPoint x).1)) =
        (((LatticeVertexIncidentCell x (j + 1)).re : Real) + 1 / 2,
          ((LatticeVertexIncidentCell x (j + 1)).im : Real) + 1 / 2) := by
      fin_cases j <;> ext <;>
        simp [p, LatticeVertexIncidentCell, GaussianRealPoint] <;> ring
    change ((GaussianRealPoint x).1 - (p.2 - (GaussianRealPoint x).2),
      (GaussianRealPoint x).2 + (p.1 - (GaussianRealPoint x).1)) ∈ TileRealization T at hp
    rw [heq] at hp
    exact (P3776T1CellCenterMembership T _).mp (by
      simpa only [GaussianRealPoint, Prod.mk_add_mk] using hp)
  have hsome : ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells := by
    rcases haAt with rfl | rfl | rfl | rfl
    · exact ⟨0, ha⟩
    · exact ⟨1, ha⟩
    · exact ⟨2, ha⟩
    · exact ⟨3, ha⟩
  obtain ⟨j, hj⟩ := hsome
  have hj1 := rotate j hj
  have hj2 := rotate (j + 1) hj1
  have hj3 := rotate (j + 1 + 1) hj2
  intro k
  fin_cases j <;> fin_cases k <;> assumption

end ApollonianSuperharmonic

end
