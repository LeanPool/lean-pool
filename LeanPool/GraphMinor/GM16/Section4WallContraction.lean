/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4Wall
public import LeanPool.GraphMinor.Minor.Model
import Mathlib.Algebra.Ring.Parity

/-!
# The contraction in XVI (4.2), Claim (1)

Delete the last column of the wall, then contract each horizontal edge
from column `2i` to column `2i+1`. Each resulting vertex is a pair of
vertices of the wall. Between neighbouring pairs in one row there is a
horizontal edge. Between neighbouring rows there is one vertical edge,
selected by the parity of the lower row. These are exactly the edges of
the smaller square grid used on page 53.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph SimpleGraph

/-- The two wall vertices identified with `(i,j)` in Claim (1) of
XVI (4.2), page 53. -/
def sphereWallPairVertex (θ : ℕ) (v : Fin θ × Fin θ) (b : Fin 2) :
    Fin (2 * θ + 1) × Fin θ :=
  (⟨2 * v.1.val + b.val, by omega⟩, v.2)

/-- The quotient coordinate on the wall after contracting the pairs.
The final column is deleted in the proof, and its value here is unused. -/
def sphereWallPairProjection (θ : ℕ) (x : Fin (2 * θ + 1) × Fin θ) :
    Fin θ × Fin θ :=
  (⟨min (x.1.val / 2) (θ - 1), by have := x.2.isLt; omega⟩, x.2)

/-- Each of the two pair vertices projects to its grid vertex. -/
theorem sphereWallPairProjection_vertex (θ : ℕ) (v : Fin θ × Fin θ) (b : Fin 2) :
    sphereWallPairProjection θ (sphereWallPairVertex θ v b) = v := by
  apply Prod.ext
  · apply Fin.ext
    simp only [sphereWallPairProjection, sphereWallPairVertex]
    have := v.1.isLt
    have := b.isLt
    omega
  · rfl

/-- The vertex set of a contracted pair. -/
def sphereWallPair (θ : ℕ) (v : Fin θ × Fin θ) :
    Set (Fin (2 * θ + 1) × Fin θ) :=
  {sphereWallPairVertex θ v 0, sphereWallPairVertex θ v 1}

/-- Distinct contracted pairs have disjoint vertex sets. -/
theorem sphereWallPair_disjoint {θ : ℕ} {u v : Fin θ × Fin θ} (hne : u ≠ v) :
    Disjoint (sphereWallPair θ u) (sphereWallPair θ v) := by
  refine disjoint_left.mpr ?_
  intro x hx hy
  simp only [sphereWallPair, mem_insert_iff, mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with h | h
  all_goals
    have hi := congrArg (fun z => z.1.val) h
    have hj := congrArg Prod.snd h
    apply hne
    exact Prod.ext (Fin.ext (by simp only [sphereWallPairVertex] at hi; omega)) hj

/-- The edge contracted within each pair is retained in the wall. -/
theorem sphereWallPairVertex_adj (θ : ℕ) (v : Fin θ × Fin θ) :
    (sphereWallSimpleGraph θ).Adj
      (sphereWallPairVertex θ v 0) (sphereWallPairVertex θ v 1) := by
  exact Or.inl ⟨rfl, Or.inl (by simp only [sphereWallPairVertex]; omega)⟩

/-- For grid edges in one row, choose the edge between successive pairs.
For edges between rows, choose the retained vertical edge. -/
def sphereWallEdgePair (θ : ℕ) (x y : Fin θ × Fin θ) :
    Sym2 (Fin (2 * θ + 1) × Fin θ) :=
  if x.2 = y.2 then
    if x.1.val < y.1.val then
      s(sphereWallPairVertex θ x 1, sphereWallPairVertex θ y 0)
    else s(sphereWallPairVertex θ x 0, sphereWallPairVertex θ y 1)
  else
    s(sphereWallPairVertex θ x ⟨min x.2.val y.2.val % 2, Nat.mod_lt _ (by decide)⟩,
      sphereWallPairVertex θ y ⟨min x.2.val y.2.val % 2, Nat.mod_lt _ (by decide)⟩)

/-- The chosen edge does not depend on the order of its ends. -/
theorem sphereWallEdgePair_symm (θ : ℕ) (x y : Fin θ × Fin θ) :
    sphereWallEdgePair θ x y = sphereWallEdgePair θ y x := by
  unfold sphereWallEdgePair
  by_cases hj : x.2 = y.2
  · rw [ite_eq_left hj, ite_eq_left hj.symm]
    rcases lt_trichotomy x.1.val y.1.val with hi | hi | hi
    · rw [ite_eq_left hi, ite_eq_right (not_lt_of_gt hi)]
      exact Sym2.eq_swap
    · have hxy : x = y := Prod.ext (Fin.ext hi) hj
      subst y
      rfl
    · rw [ite_eq_right (not_lt_of_gt hi), ite_eq_left hi]
      exact Sym2.eq_swap
  · rw [ite_eq_right hj, ite_eq_right (Ne.symm hj)]
    simp only [min_comm y.2.val x.2.val]
    exact Sym2.eq_swap

/-- The edge map of the contraction model in XVI (4.2), Claim (1). -/
def sphereWallGridEdge (θ : ℕ) :
    Sym2 (Fin θ × Fin θ) → Sym2 (Fin (2 * θ + 1) × Fin θ) :=
  Sym2.lift ⟨sphereWallEdgePair θ, sphereWallEdgePair_symm θ⟩

/-- Evaluation of the contraction edge map. -/
theorem sphereWallGridEdge_mk (θ : ℕ) (x y : Fin θ × Fin θ) :
    sphereWallGridEdge θ s(x,y) = sphereWallEdgePair θ x y := by rfl

/-- Projection is a left inverse for the chosen edge map. In particular,
no two edges of the smaller grid use the same wall edge. -/
theorem sphereWallGridEdge_projection (θ : ℕ) (e : Sym2 (Fin θ × Fin θ)) :
    Sym2.map (sphereWallPairProjection θ) (sphereWallGridEdge θ e) = e := by
  induction e with
  | h x y =>
    rw [sphereWallGridEdge_mk]
    unfold sphereWallEdgePair
    split_ifs <;> simp only [Sym2.map_mk, sphereWallPairProjection_vertex]

/-- The contraction model's edge map is injective. -/
theorem sphereWallGridEdge_injective (θ : ℕ) :
    Function.Injective (sphereWallGridEdge θ) := by
  intro e f heq
  have h := congrArg (Sym2.map (sphereWallPairProjection θ)) heq
  simpa only [sphereWallGridEdge_projection] using h

/-- Both cases of the edge map give a retained wall edge. -/
theorem sphereWallGridEdge_mem {θ : ℕ} {e : Sym2 (Fin θ × Fin θ)}
    (he : e ∈ E(GM01.gridGraph θ)) :
    sphereWallGridEdge θ e ∈ E(sphereWallGraph θ) := by
  induction e with
  | h x y =>
    have hxy : (pathGraph θ □ pathGraph θ).Adj x y := he
    rw [SimpleGraph.boxProd_adj] at hxy
    rw [sphereWallGridEdge_mk]
    rcases hxy with ⟨hstep, hj⟩ | ⟨hstep, hi⟩
    · have hj' : x.2 = y.2 := hj
      rw [sphereWallEdgePair, ite_eq_left hj']
      rcases SimpleGraph.pathGraph_adj.mp hstep with hstep | hstep
      · rw [ite_eq_left (by omega)]
        exact Or.inl ⟨hj', Or.inl (by simp only [sphereWallPairVertex]; omega)⟩
      · rw [ite_eq_right (by omega)]
        exact Or.inl ⟨hj', Or.inr (by simp only [sphereWallPairVertex]; omega)⟩
    · have hj : x.2 ≠ y.2 := fun h => (SimpleGraph.pathGraph_adj.mp hstep).elim
        (fun hs => by have := congrArg Fin.val h; omega)
        (fun hs => by have := congrArg Fin.val h; omega)
      rw [sphereWallEdgePair, ite_eq_right hj]
      refine Or.inr ⟨?_, ?_⟩
      · exact congrArg (fun a : Fin θ => (⟨2 * a.val + min x.2.val y.2.val % 2,
          by have := a.isLt; omega⟩ : Fin (2 * θ + 1))) hi
      · rcases SimpleGraph.pathGraph_adj.mp hstep with hstep | hstep
        · left
          refine ⟨hstep, ?_⟩
          rw [Nat.even_iff]
          simp only [sphereWallPairVertex]
          rw [min_eq_left (by omega)]
          omega
        · right
          refine ⟨hstep, ?_⟩
          rw [Nat.even_iff]
          simp only [sphereWallPairVertex]
          rw [min_eq_right (by omega)]
          omega

end GraphMinor.GM16
