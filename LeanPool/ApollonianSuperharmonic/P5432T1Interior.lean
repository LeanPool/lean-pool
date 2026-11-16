/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondVertexIncidence
public import LeanPool.ApollonianSuperharmonic.DiamondVertexDomains

-- [TABLET NODE: P5432T1Interior]

/-!
# P5432T1Interior

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5432T1Interior (K : DiamondParameter) :
    (∀ z, (z ∈ FootprintVertices (DiamondTile K.1) ∧
      z ∉ BoundaryFootprintVertices (DiamondTile K.1)) ↔
        z ∈ DiamondVertexDomains K true) ∧
    (∀ z, z ∈ DiamondVertexDomains K true →
      ∀ d ∈ ({0, 1, -1, ⟨0, 1⟩, -⟨0, 1⟩} : Finset GaussianInt),
        z + d ∈ DiamondVertexDomains K false) := by
-- BODY
  classical
  have hk := K.2
  have inner (z : GaussianInt) : z ∈ DiamondVertexDomains K true ↔
      |z.re| + |z.im - (K.1 : Int)| ≤ (K.1 : Int) - 1 := by
    change Int.natAbs z.re + Int.natAbs (z.im - (K.1 : Int)) ≤ K.1 - 1 ↔ _
    have ha := Int.natCast_natAbs z.re
    have hb := Int.natCast_natAbs (z.im - (K.1 : Int))
    omega
  constructor
  · intro z
    rw [(P4194T1DiamondVertexIncidence K.1 hk z).1,
      (P4194T1DiamondVertexIncidence K.1 hk z).2]
    have all_iff : ((∃ j : Fin 4,
        LatticeVertexIncidentCell z j ∈ DiamondCellDomain K.1) ∧
        ¬ ((∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ DiamondCellDomain K.1) ∧
          ∃ j : Fin 4, LatticeVertexIncidentCell z j ∉ DiamondCellDomain K.1)) ↔
        ∀ j : Fin 4, LatticeVertexIncidentCell z j ∈ DiamondCellDomain K.1 := by
      constructor
      · rintro ⟨hex, hn⟩ j
        by_contra hj
        exact hn ⟨hex, j, hj⟩
      · intro h
        exact ⟨⟨0, h 0⟩, fun ⟨_, j, hj⟩ => hj (h j)⟩
    rw [all_iff, (P4194T1DiamondCellRows K.1 z).2, inner]
    simp only [abs_eq_max_neg]
    omega
  · intro z hz d hd
    rw [inner] at hz
    have bound (w : GaussianInt)
        (hw : |w.re| + |w.im - (K.1 : Int)| ≤ (K.1 : Int)) :
        w ∈ DiamondVertexDomains K false := by
      change max (Int.natAbs w.re)
        (max (Int.natAbs (w.im - (K.1 : Int)))
          (Int.natAbs w.re + Int.natAbs (w.im - (K.1 : Int)) - 1)) ≤ K.1
      have ha := Int.natCast_natAbs w.re
      have hb := Int.natCast_natAbs (w.im - (K.1 : Int))
      simp only [max_le_iff]
      have hapos := abs_nonneg w.re
      have hbpos := abs_nonneg (w.im - (K.1 : Int))
      omega
    apply bound
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;>
      norm_num <;>
      simp only [abs_eq_max_neg] at hz ⊢ <;> omega

end ApollonianSuperharmonic

end
