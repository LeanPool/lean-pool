/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import LeanPool.ApollonianSuperharmonic.ProtoTile
public import Mathlib.Init


/-!
# LatticeVertexSectorFacts

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace LatticeVertexSectorFacts

/-- Shared neighborDistinct identity for LatticeVertexSectorFacts. -/
theorem neighborDistinct :
    (by
      classical
      exact
        let neighbor (x : GaussianInt) : Fin 4 → GaussianInt :=
          ![x + ⟨0, 1⟩, x - 1, x - ⟨0, 1⟩, x + 1]
        ∀ (x : GaussianInt), ∀ (j : Fin 4), neighbor x j ≠ x ) := by
  classical
  intro neighbor x j
  fin_cases j <;> simp [neighbor, Zsqrtd.ext_iff]

/-- Shared edgeMembership identity for LatticeVertexSectorFacts. -/
theorem edgeMembership :
    (by
      classical
      exact
        let neighbor (x : GaussianInt) : Fin 4 → GaussianInt :=
          ![x + ⟨0, 1⟩, x - 1, x - ⟨0, 1⟩, x + 1]
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        ∀ (x : GaussianInt), ∀ (j : Fin 4), x ∈ edgeAt x j ∧ neighbor x j ∈ edgeAt x j ) := by
  classical
  intro neighbor edgeAt x j
  fin_cases j <;> simp [neighbor, edgeAt]

/-- Shared edgePair identity for LatticeVertexSectorFacts. -/
theorem edgePair :
    (by
      classical
      exact
        let neighbor (x : GaussianInt) : Fin 4 → GaussianInt :=
          ![x + ⟨0, 1⟩, x - 1, x - ⟨0, 1⟩, x + 1]
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        ∀ (x : GaussianInt), ∀ (j : Fin 4), edgeAt x j = {x, neighbor x j} ) := by
  classical
  intro neighbor edgeAt x j
  fin_cases j <;> simp [edgeAt, neighbor, Finset.pair_comm]

/-- Shared edgeInjective identity for LatticeVertexSectorFacts. -/
theorem edgeInjective :
    (by
      classical
      exact
        let neighbor (x : GaussianInt) : Fin 4 → GaussianInt :=
          ![x + ⟨0, 1⟩, x - 1, x - ⟨0, 1⟩, x + 1]
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        (∀ (x : GaussianInt), ∀ (j : Fin 4), neighbor x j ≠ x) → ((∀ (x : GaussianInt), ∀
            {j : Fin 4}, ∀ {k : Fin 4}, (neighbor x j = neighbor x k) → (j = k)) → ((∀ (x :
            GaussianInt), ∀ (j : Fin 4), x ∈ edgeAt x j ∧ neighbor x j ∈ edgeAt x j) → (∀ (x :
            GaussianInt), ∀ {j : Fin 4}, ∀ {k : Fin 4}, (edgeAt x j = edgeAt x k) → (j = k)))) )
            := by
  classical
  intro neighbor edgeAt neighbor_ne_center neighbor_injective edgeAt_mem x j k h
  have hx := (edgeAt_mem x j).1
  have hn := (edgeAt_mem x j).2
  have hnm : neighbor x j ∈ edgeAt x k := by rw [← h]; exact hn
  have hchoices : neighbor x j = x ∨ neighbor x j = neighbor x k := by
    fin_cases k
    · simpa [edgeAt, neighbor] using hnm
    · have hh : neighbor x j = x - 1 ∨ neighbor x j = x := by
        simpa [edgeAt, neighbor] using hnm
      exact Or.symm hh
    · have hh : neighbor x j = x - ⟨0, 1⟩ ∨ neighbor x j = x := by
        simpa [edgeAt, neighbor] using hnm
      exact Or.symm hh
    · simpa [edgeAt, neighbor] using hnm
  exact neighbor_injective x (hchoices.resolve_left (neighbor_ne_center x j))

/-- Shared firstTileLabel identity for LatticeVertexSectorFacts. -/
theorem firstTileLabel :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        ∀ (x : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ T0.cells) →
            (outerLabel x j = 0) ) := by
  classical
  intro T0 T0' outerLabel x j hc
  simp [outerLabel, hc]

/-- Shared secondTileLabel identity for LatticeVertexSectorFacts. -/
theorem secondTileLabel :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), (Disjoint T0.cells T0'.cells) → (
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        ∀ (x : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ T0'.cells) →
            (outerLabel x j = 1)) ) := by
  classical
  intro T0 T0' hdis outerLabel x j hc
  have hn : LatticeVertexIncidentCell x j ∉ T0.cells :=
    Finset.disjoint_left.mp hdis.symm hc
  simp [outerLabel, hn, hc]

end LatticeVertexSectorFacts
end ApollonianSuperharmonic

end
