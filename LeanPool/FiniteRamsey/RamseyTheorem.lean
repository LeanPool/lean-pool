/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.FiniteRamsey.MonochromaticClique
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Ramsey's theorem for finitely many colours

For a finite colour type `ι` and target sizes `n : ι → ℕ`, every `ι`-colouring of the edges of a
large enough complete graph has, for some colour `c`, a clique of size `n c` all of whose edges have
colour `c`.

The proof is the direct induction on the total size `∑ c, n c`, for all colour counts at once,
rather than a reduction to the two-colour case. If some `n c = 0` there is nothing to prove.
Otherwise fix a vertex `v`. By the pigeonhole principle, some colour `c` occurs on at least `N c`
of the edges at `v`, where `N c` works for the sizes `n` with `n c` lowered by one. Inside that
colour-`c` neighbourhood we find either a colour-`d` clique of size `n d` for some `d ≠ c`, or a
colour-`c` clique of size `n c - 1`, which `v` extends.

## Main declarations

* `SimpleGraph.IsRamseyValid V n`: every `ι`-labelling of the complete graph on `V` has, for some
  colour `c`, a `c`-monochromatic clique of size `n c`.
* `SimpleGraph.IsRamseyValid.of_embedding`: the property passes to larger vertex types.
* `SimpleGraph.exists_isRamseyValid`: **Ramsey's theorem**: some `N` makes every vertex type with at
  least `N` elements Ramsey-valid.

## References

* F. P. Ramsey, *On a problem of formal logic*, Proc. London Math. Soc. (2) 30 (1930), 264-286.

## Tags

ramsey theory, edge coloring, combinatorics
-/

@[expose] public section

open Finset Fintype

namespace SimpleGraph

universe u w

variable {ι : Type w}

/-- `IsRamseyValid V n`: every `ι`-labelling of the edges of the complete graph on `V` has, for
some colour `c`, a clique of size `n c` all of whose edges have colour `c`. -/
def IsRamseyValid (V : Type u) (n : ι → ℕ) : Prop :=
  ∀ C : TopEdgeLabeling V ι, ∃ c, EdgeLabeling.HasMonochromaticClique C c (n c)

/-- Ramsey-validity passes along embeddings of vertex types. -/
theorem IsRamseyValid.of_embedding {V V' : Type u} {n : ι → ℕ} (f : V ↪ V')
    (h : IsRamseyValid V n) : IsRamseyValid V' n :=
  fun C => (h (C.pullback f)).imp fun c hc =>
    EdgeLabeling.hasMonochromaticClique_map_pullback C f c hc

/-- With no colours, a vertex type with two elements is (vacuously) Ramsey-valid: its complete
graph has an edge, which cannot be labelled. -/
theorem IsRamseyValid.of_isEmpty [IsEmpty ι] {V : Type u} [Fintype V] (hV : 2 ≤ card V)
    (n : ι → ℕ) : IsRamseyValid V n := fun C =>
  let ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < card V)
  isEmptyElim (C.get x y hxy)

/-- Lowering one target size by one decreases the total size, when that size is positive. -/
theorem sum_update_sub_one_lt [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {c : ι} (hc : n c ≠ 0) :
    ∑ d, Function.update n c (n c - 1) d < ∑ d, n d := by
  rw [sum_update_of_mem (mem_univ c), sdiff_singleton_eq_erase, ← add_sum_erase _ _ (mem_univ c)]
  omega

/-- **Ramsey's theorem** for a finite colour type: for all target sizes `n`, some `N` makes every
vertex type with at least `N` elements Ramsey-valid. -/
theorem exists_isRamseyValid [Finite ι] (n : ι → ℕ) :
    ∃ N, ∀ (V : Type u) [Fintype V], N ≤ card V → IsRamseyValid V n := by
  classical
  have := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨2, fun V _ hV => IsRamseyValid.of_isEmpty hV n⟩
  -- strong induction on the total size
  induction hs : ∑ c, n c using Nat.strong_induction_on generalizing n with
  | _ s ih =>
  by_cases h0 : ∃ c, n c = 0
  · obtain ⟨c, hc⟩ := h0
    exact ⟨0, fun V _ _ C => ⟨c, ∅, isNClique_empty.mpr hc⟩⟩
  push Not at h0
  have hsub : ∀ c, ∃ N, ∀ (V : Type u) [Fintype V], N ≤ card V →
      IsRamseyValid V (Function.update n c (n c - 1)) :=
    fun c => ih _ (hs ▸ sum_update_sub_one_lt (h0 c)) _ rfl
  choose N hN using hsub
  refine ⟨∑ c, N c + 1, fun V _ hV C => ?_⟩
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨c₀⟩ := hι
  -- the colour of the edge from `v` to `w` (an arbitrary colour at `w = v`)
  let col : V → ι := fun w => if h : v = w then c₀ else C.get v w h
  let S : Finset V := univ.erase v
  -- pigeonhole: some colour class at `v` is large
  obtain ⟨c, hc⟩ : ∃ c, N c ≤ #(S.filter fun w => col w = c) := by
    by_contra! hcon
    have := card_eq_sum_card_fiberwise (s := S) fun w _ => mem_univ (col w)
    have := sum_lt_sum_of_nonempty (univ_nonempty_iff.mpr ⟨c₀⟩) fun c _ => hcon c
    have : #S = card V - 1 := by simp [S]
    omega
  set T := S.filter fun w => col w = c with hT
  -- apply the induction hypothesis inside the colour-`c` neighbourhood `T`
  have hTcard : N c ≤ Fintype.card T := by simpa using hc
  obtain ⟨d, t, ht⟩ := hN c T hTcard (C.pullback (Function.Embedding.subtype (· ∈ T)))
  have hmap := EdgeLabeling.monochromaticClique_map_pullback C _ d ht
  by_cases hdc : d = c
  · subst hdc
    rw [Function.update_self] at hmap
    have hins := IsNClique.insert hmap (a := v) fun w hw => ?_
    · exact ⟨d, _, by rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero (h0 d))] at hins⟩
    obtain ⟨⟨w, hwT⟩, -, rfl⟩ := mem_map.mp hw
    obtain ⟨hwv, hcol⟩ : w ≠ v ∧ col w = d := by simpa [hT, S] using hwT
    simp only [col, hwv.symm, ↓reduceDIte] at hcol
    exact (TopEdgeLabeling.labelGraph_adj v w).mpr ⟨hwv.symm, hcol⟩
  · rw [Function.update_of_ne hdc] at hmap
    exact ⟨d, _, hmap⟩

end SimpleGraph
