/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Balanced.RSa
public import LeanPool.BalancedEdgeColourings.Overfull.Multifan

/-!
# Equitable strong colourings (Rudašová–Soták), part B: the graph of ends

For colours `a ≠ b`, the *ends* are the vertices at which exactly one of `a, b` is present (the
ends of the `(a, b)`-paths). The graph `endGraph c a b` (`H_{a,b}` of Rudašová–Soták) joins two
ends when they lie on the same `(a, b)`-path, or when their colour sets are exchanged by `(a b)`.
In a strong colouring it has maximum degree `2`, and an end `u` without a partner set
`i_ab S(u)` has degree at most `1`.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Balanced

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ}

section Ends

variable (c : PEC G (Fin k)) (a b : Fin k)

/-- Exactly one of `a, b` is present at `v`. -/
def IsEnd (v : V) : Prop :=
  (a ∈ colSet c v ∧ b ∉ colSet c v) ∨ (b ∈ colSet c v ∧ a ∉ colSet c v)

/-- The graph `H_{a,b}` on the ends. -/
def endGraph : SimpleGraph V where
  Adj u v := u ≠ v ∧ IsEnd c a b u ∧ IsEnd c a b v ∧
    ((c.kempeGraph a b).Reachable u v ∨ colSet c v = swapSet a b (colSet c u))
  symm.symm := by
    rintro u v ⟨h1, h2, h3, h4⟩
    refine ⟨h1.symm, h3, h2, ?_⟩
    rcases h4 with r | e
    · exact Or.inl r.symm
    · right; rw [e, swapSet_swapSet]
  loopless := ⟨fun _ h => h.1 rfl⟩

end Ends

variable {c : PEC G (Fin k)} {a b : Fin k}

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
theorem IsEnd.free {v : V} (h : IsEnd c a b v) : c.IsFree v a ∨ c.IsFree v b := by
  classical
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · right; simpa [mem_colSet] using h
  · left; simpa [mem_colSet] using h

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
theorem IsEnd.of_swap {v : V} (h : IsEnd c a b v) (w : V) (hw : colSet c w = swapSet a b
    (colSet c v)) :
    IsEnd c a b w := by
  classical
  have ea : a ∈ colSet c w ↔ b ∈ colSet c v := by rw [hw, mem_swapSet, Equiv.swap_apply_left]
  have eb : b ∈ colSet c w ↔ a ∈ colSet c v := by rw [hw, mem_swapSet, Equiv.swap_apply_right]
  unfold IsEnd at h ⊢
  rw [ea, eb]
  tauto
omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
theorem IsEnd.swap_ne {v : V} (h : IsEnd c a b v) : swapSet a b (colSet c v) ≠ colSet c v := by
  classical
  intro e
  have ea : a ∈ swapSet a b (colSet c v) ↔ b ∈ colSet c v := by
    rw [mem_swapSet, Equiv.swap_apply_left]
  rw [e] at ea
  unfold IsEnd at h
  tauto

omit [DecidableEq V] [DecidableRel G.Adj] in
omit [Fintype V] in
/-- Two ends on the same `(a, b)`-path as an end `u` coincide. -/
theorem end_reach_unique [Finite V] {u x y : V} (hu : IsEnd c a b u) (hx : IsEnd c a b x)
    (hy : IsEnd c a b y) (hux : u ≠ x) (huy : u ≠ y) (rx : (c.kempeGraph a b).Reachable u x)
    (ry : (c.kempeGraph a b).Reachable u y) : x = y := by
  classical
  let : Fintype V := Fintype.ofFinite V
  by_contra hxy
  exact not_three_linked c hux huy hxy hu.free hx.free hy.free rx ry

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem endGraph_degree_le_two (hinj : Function.Injective (colSet c)) (u : V) :
    (endGraph c a b).degree u ≤ 2 := by
  classical
  by_contra hlt
  push Not at hlt
  rw [← card_neighborFinset_eq_degree] at hlt
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := two_lt_card.1 hlt
  rw [mem_neighborFinset] at hx hy hz
  obtain ⟨ux, eu, ex, kx⟩ := hx
  obtain ⟨uy, -, ey, ky⟩ := hy
  obtain ⟨uz, -, ez, kz⟩ := hz
  have K : ∀ {p q}, p ≠ q → IsEnd c a b p → IsEnd c a b q → u ≠ p → u ≠ q →
      (c.kempeGraph a b).Reachable u p → (c.kempeGraph a b).Reachable u q → False :=
    fun hpq ep eq up uq rp rq => hpq (end_reach_unique eu ep eq up uq rp rq)
  have E : ∀ {p q}, p ≠ q → colSet c p = swapSet a b (colSet c u) →
      colSet c q = swapSet a b (colSet c u) → False :=
    fun hpq e1 e2 => hpq (hinj (e1.trans e2.symm))
  rcases kx with kx | kx <;> rcases ky with ky | ky <;> rcases kz with kz | kz
  · exact K hxy ex ey ux uy kx ky
  · exact K hxy ex ey ux uy kx ky
  · exact K hxz ex ez ux uz kx kz
  · exact E hyz ky kz
  · exact K hyz ey ez uy uz ky kz
  · exact E hxz kx kz
  · exact E hxy kx ky
  · exact E hxy kx ky

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem endGraph_degree_le_one (_ : Function.Injective (colSet c)) {u : V}
    (hun : ∀ w, colSet c w ≠ swapSet a b (colSet c u)) : (endGraph c a b).degree u ≤ 1 := by
  classical
  rw [← card_neighborFinset_eq_degree]
  refine card_le_one.2 fun x hx y hy => ?_
  rw [mem_neighborFinset] at hx hy
  obtain ⟨ux, eu, ex, kx⟩ := hx
  obtain ⟨uy, -, ey, ky⟩ := hy
  rcases kx with kx | kx
  · rcases ky with ky | ky
    · exact end_reach_unique eu ex ey ux uy kx ky
    · exact absurd ky (hun y)
  · exact absurd kx (hun x)
end Balanced

end LeanPool.BalancedEdgeColourings
