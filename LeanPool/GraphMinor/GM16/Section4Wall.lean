/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM01.Defs
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Ring.Parity

/-!
# The wall in Graph Minors XVI, (4.2)

On page 53 the proof starts with a rectangular grid and deletes alternate
vertical edges. Coordinates here start at zero. The horizontal edges
remain, and a vertical edge above a vertex remains exactly when the sum
of its coordinates is even. At most one vertical edge meets each vertex,
so the resulting graph has maximum degree at most three.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph SimpleGraph
universe u

/-- The graph `N₁` in the proof of XVI (4.2), page 53. Its vertex
`(i,j)` is the paper's vertex `(i+1,j+1)`. -/
def sphereWallSimpleGraph (θ : ℕ) : SimpleGraph (Fin (2 * θ + 1) × Fin θ) where
  Adj x y :=
    (x.2 = y.2 ∧ (x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val)) ∨
    (x.1 = y.1 ∧ ((x.2.val + 1 = y.2.val ∧ Even (x.1.val + x.2.val)) ∨
      (y.2.val + 1 = x.2.val ∧ Even (y.1.val + y.2.val))))
  symm := ⟨by
    intro x y h
    rcases h with ⟨hxy, hstep⟩ | ⟨hxy, hstep⟩
    · exact Or.inl ⟨hxy.symm, hstep.symm⟩
    · exact Or.inr ⟨hxy.symm, hstep.symm⟩⟩
  loopless := ⟨fun x h => by
    rcases h with ⟨_, hstep | hstep⟩ | ⟨_, ⟨hstep, _⟩ | ⟨hstep, _⟩⟩ <;> omega⟩

/-- The graph `N₁` from XVI (4.2), retaining the grid's edge names. -/
def sphereWallGraph (θ : ℕ) :
    Graph (Fin (2 * θ + 1) × Fin θ) (Sym2 (Fin (2 * θ + 1) × Fin θ)) :=
  Graph.ofSimpleGraph (sphereWallSimpleGraph θ)

/-- Inclusion of the rectangular wall in the square grid of XVI (4.2),
page 53. The coordinates are exchanged so its horizontal paths are the
rows in `GM10.gridRowPath`. -/
def sphereWallGridVertex (θ : ℕ) (x : Fin (2 * θ + 1) × Fin θ) :
    Fin (2 * θ + 1) × Fin (2 * θ + 1) :=
  (Fin.castLE (by omega) x.2, x.1)

/-- The wall inclusion is injective on vertices. -/
theorem sphereWallGridVertex_injective (θ : ℕ) :
    Function.Injective (sphereWallGridVertex θ) := by
  intro x y h
  have h₁ := congrArg (fun z => z.1.val) h
  have h₂ := congrArg Prod.snd h
  exact Prod.ext h₂ (Fin.ext h₁)

/-- Every retained edge is an edge of the square grid. -/
theorem sphereWallGridVertex_adj {θ : ℕ}
    {x y : Fin (2 * θ + 1) × Fin θ}
    (h : (sphereWallSimpleGraph θ).Adj x y) :
    (pathGraph (2 * θ + 1) □ pathGraph (2 * θ + 1)).Adj
      (sphereWallGridVertex θ x) (sphereWallGridVertex θ y) := by
  rw [SimpleGraph.boxProd_adj]
  rcases h with ⟨heq, hstep⟩ | ⟨heq, hstep⟩
  · right
    refine ⟨SimpleGraph.pathGraph_adj.mpr hstep, ?_⟩
    apply Fin.ext
    simpa only [sphereWallGridVertex, Fin.val_castLE] using congrArg (Fin.val : Fin θ → ℕ) heq
  · left
    refine ⟨SimpleGraph.pathGraph_adj.mpr ?_, heq⟩
    rcases hstep with ⟨hstep, _⟩ | ⟨hstep, _⟩
    · exact Or.inl hstep
    · exact Or.inr hstep

/-- No two different vertical neighbours meet the same vertex in `N₁`.
The potential vertical edges above and below have opposite parity. -/
theorem sphereWall_vertical_neighbor_unique {θ : ℕ}
    {x y z : Fin (2 * θ + 1) × Fin θ}
    (hxy : (sphereWallSimpleGraph θ).Adj x y)
    (hxz : (sphereWallSimpleGraph θ).Adj x z)
    (hy : y.1 = x.1) (hz : z.1 = x.1) : y = z := by
  have hyi : y.1.val = x.1.val := congrArg Fin.val hy
  have hzi : z.1.val = x.1.val := congrArg Fin.val hz
  have hstepy : (x.2.val + 1 = y.2.val ∧ Even (x.1.val + x.2.val)) ∨
      (y.2.val + 1 = x.2.val ∧ Even (y.1.val + y.2.val)) := by
    rcases hxy with ⟨_, hstep | hstep⟩ | ⟨_, hstep⟩
    · omega
    · omega
    · exact hstep
  have hstepz : (x.2.val + 1 = z.2.val ∧ Even (x.1.val + x.2.val)) ∨
      (z.2.val + 1 = x.2.val ∧ Even (z.1.val + z.2.val)) := by
    rcases hxz with ⟨_, hstep | hstep⟩ | ⟨_, hstep⟩
    · omega
    · omega
    · exact hstep
  apply Prod.ext (hy.trans hz.symm)
  apply Fin.ext
  rcases hstepy with ⟨hup, heven⟩ | ⟨hdown, heven⟩ <;>
    rcases hstepz with ⟨hup', heven'⟩ | ⟨hdown', heven'⟩
  · omega
  · rw [Nat.even_iff] at heven heven'
    omega
  · rw [Nat.even_iff] at heven heven'
    omega
  · omega

/-- The maximum-degree assertion in the last paragraph of the proof of
XVI (4.2), page 54. The three possible neighbours are left, right, and
the unique vertical neighbour. -/
theorem sphereWall_neighborSet_ncard_le_three (θ : ℕ)
    (x : Fin (2 * θ + 1) × Fin θ) :
    ((sphereWallSimpleGraph θ).neighborSet x).ncard ≤ 3 := by
  classical
  let tag : Fin (2 * θ + 1) × Fin θ → Fin 3 := fun y =>
    if y.1.val < x.1.val then 0 else if x.1.val < y.1.val then 1 else 2
  have hinj : InjOn tag ((sphereWallSimpleGraph θ).neighborSet x) := by
    intro y hy z hz htag
    change (sphereWallSimpleGraph θ).Adj x y at hy
    change (sphereWallSimpleGraph θ).Adj x z at hz
    by_cases hyl : y.1.val < x.1.val
    · have hzl : z.1.val < x.1.val := by
        by_contra hzl
        simp only [tag, hyl, hzl, ↓reduceIte] at htag
        split_ifs at htag <;> contradiction
      have hyc : y.2 = x.2 ∧ y.1.val + 1 = x.1.val := by
        rcases hy with ⟨h, hs | hs⟩ | ⟨h, _⟩
        · omega
        · exact ⟨h.symm, hs⟩
        · have := congrArg Fin.val h; omega
      have hzc : z.2 = x.2 ∧ z.1.val + 1 = x.1.val := by
        rcases hz with ⟨h, hs | hs⟩ | ⟨h, _⟩
        · omega
        · exact ⟨h.symm, hs⟩
        · have := congrArg Fin.val h; omega
      exact Prod.ext (Fin.ext (by omega)) (hyc.1.trans hzc.1.symm)
    · by_cases hyr : x.1.val < y.1.val
      · have hzr : x.1.val < z.1.val := by
          by_contra hzr
          simp only [tag, hyl, hyr, hzr, ↓reduceIte] at htag
          split_ifs at htag <;> contradiction
        have hyc : y.2 = x.2 ∧ x.1.val + 1 = y.1.val := by
          rcases hy with ⟨h, hs | hs⟩ | ⟨h, _⟩
          · exact ⟨h.symm, hs⟩
          · omega
          · have := congrArg Fin.val h; omega
        have hzc : z.2 = x.2 ∧ x.1.val + 1 = z.1.val := by
          rcases hz with ⟨h, hs | hs⟩ | ⟨h, _⟩
          · exact ⟨h.symm, hs⟩
          · omega
          · have := congrArg Fin.val h; omega
        exact Prod.ext (Fin.ext (by omega)) (hyc.1.trans hzc.1.symm)
      · have hzi : z.1.val = x.1.val := by
          by_contra hzi
          simp only [tag, hyl, hyr, ↓reduceIte] at htag
          split_ifs at htag <;> omega
        exact sphereWall_vertical_neighbor_unique hy hz (Fin.ext (by omega)) (Fin.ext hzi)
  have hcard := Set.ncard_le_ncard_of_injOn tag (fun _ _ => Set.mem_univ _) hinj
    (Set.finite_univ : (Set.univ : Set (Fin 3)).Finite)
  simpa only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] using hcard

/-- Every vertex of the wall has a horizontal neighbor. -/
theorem sphereWall_no_isolated (θ : ℕ) (v : Fin (2 * θ + 1) × Fin θ) :
    ∃ w, (sphereWallSimpleGraph θ).Adj v w := by
  have hθ : 0 < θ := lt_of_le_of_lt (Nat.zero_le v.2.val) v.2.isLt
  by_cases hi : v.1.val + 1 < 2 * θ + 1
  · exact ⟨(⟨v.1.val + 1, hi⟩, v.2), Or.inl ⟨rfl, Or.inl rfl⟩⟩
  · have hPrev : v.1.val - 1 < 2 * θ + 1 := by omega
    refine ⟨(⟨v.1.val - 1, hPrev⟩, v.2), Or.inl ⟨rfl, Or.inr ?_⟩⟩
    change v.1.val - 1 + 1 = v.1.val
    omega

end GraphMinor.GM16
