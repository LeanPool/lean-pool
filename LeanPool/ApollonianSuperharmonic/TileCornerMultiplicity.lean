/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.ProtoTile
public import Mathlib.Init



/-!
# TileCornerMultiplicity

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace TileCornerMultiplicity

/-- Shared cornerCount identity for TileCornerMultiplicity. -/
theorem cornerCount :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        ∀ (z : GaussianInt), cornerBag.count z = (if z ∈ T.cells then 1 else 0) + (if z - 1 ∈
            T.cells then 1 else 0) + (if z - I ∈ T.cells then 1 else 0) + (if z - 1 - I ∈ T.cells
            then 1 else 0) ) := by
  classical
  intro T I cornerBag z
  dsimp only [cornerBag]
  rw [Multiset.count_bind, ← Finset.sum_eq_multiset_sum]
  simp only [Multiset.coe_count, List.count_cons, beq_iff_eq,
    List.count_nil]
  have h11 : ∀ c : GaussianInt, (c + 1 + I = z) ↔
      (c = z - 1 - I) := by
    intro c
    constructor <;> intro h
    · rw [← h]; ring
    · rw [h]; ring
  have hI : ∀ c : GaussianInt, (c + I = z) ↔ (c = z - I) := by
    intro c
    constructor <;> intro h
    · rw [← h]; ring
    · rw [h]; ring
  have h1 : ∀ c : GaussianInt, (c + 1 = z) ↔ (c = z - 1) := by
    intro c
    constructor <;> intro h
    · rw [← h]; ring
    · rw [h]; ring
  simp_rw [h11, hI, h1]
  simp only [Finset.sum_add_distrib, zero_add]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq',
    Finset.sum_ite_eq']
  omega

/-- Shared vertexSupport fact. -/
theorem vertexSupport :
    ∀ (T : ProtoTile), (T.cells.Nonempty) → (
    let I : GaussianInt := ⟨0, 1⟩
    let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
      ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
    (cornerBag.toFinset : Set GaussianInt) = FootprintVertices T) := by
  classical
  intro T hne I cornerBag
  ext z
  change z ∈ cornerBag.toFinset ↔ z ∈ FootprintVertices T
  rw [Multiset.mem_toFinset]
  dsimp only [cornerBag, I]
  simp [FootprintVertices, hne]

end TileCornerMultiplicity
end ApollonianSuperharmonic

end
