/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Group.Action.Defs

/-!
# Counting subsets with a prescribed trace

Let `V` be a finite set with `N` elements and let `u ⊆ V`. This file counts the
`b`-element subsets `d ⊆ V` according to their trace `u ∩ d` on `u`.

* `card_trace_eq`: if `x ⊆ u` and `|x| ≤ b`, exactly `C(N - |u|, b - |x|)` of the
  `b`-subsets `d` satisfy `u ∩ d = x`.
* `card_trace_card_eq`: if `k ≤ b`, exactly `C(|u|, k) · C(N - |u|, b - k)` of the
  `b`-subsets `d` satisfy `|u ∩ d| = k`.

These are the two counting facts used by the sector dimensions
(`HubbardMoments.Sectors`) and by the second-moment theorem
(`HubbardMoments.SecondMoment`). They involve no physics.
-/

@[expose] public section

namespace HubbardMoments

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If `x ⊆ u` and `|x| ≤ b`, the `b`-subsets of `V` whose trace on `u` is `x` are
in bijection with the `(b - |x|)`-subsets of the complement of `u`, through
`d ↦ d \ u` and `y ↦ x ∪ y`. -/
theorem card_trace_eq (u x : Finset V) (hxu : x ⊆ u) (b : ℕ) (hxb : x.card ≤ b) :
    ((powersetCard b univ).filter (fun d => u ∩ d = x)).card =
      (Fintype.card V - u.card).choose (b - x.card) := by
  rw [← card_compl, ← card_powersetCard]
  refine card_nbij' (fun d => d \ u) (fun y => x ∪ y) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [mem_coe, mem_filter, mem_powersetCard, subset_univ, true_and] at hd
    obtain ⟨hdb, hdx⟩ := hd
    simp only [mem_coe, mem_powersetCard]
    refine ⟨fun a ha => ?_, ?_⟩
    · simp only [mem_sdiff] at ha
      simpa using ha.2
    · have h := card_sdiff_add_card_inter d u
      rw [inter_comm, hdx, hdb] at h
      omega
  · intro y hy
    simp only [mem_coe, mem_powersetCard] at hy
    obtain ⟨hyu, hyb⟩ := hy
    have hdisj : Disjoint x y := by
      rw [disjoint_left]
      intro a hax hay
      have := hyu hay
      simp only [mem_compl] at this
      exact this (hxu hax)
    simp only [mem_coe, mem_filter, mem_powersetCard, subset_univ, true_and]
    refine ⟨?_, ?_⟩
    · rw [card_union_of_disjoint hdisj, hyb]
      omega
    · ext a
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨hau, hax | hay⟩
        · exact hax
        · have := hyu hay
          simp only [mem_compl] at this
          exact absurd hau this
      · intro hax
        exact ⟨hxu hax, Or.inl hax⟩
  · intro d hd
    simp only [mem_coe, mem_filter, mem_powersetCard, subset_univ, true_and] at hd
    obtain ⟨-, hdx⟩ := hd
    ext a
    simp only [mem_union, mem_sdiff]
    rw [← hdx]
    simp only [mem_inter]
    tauto
  · intro y hy
    simp only [mem_coe, mem_powersetCard] at hy
    ext a
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨hax | hay, hau⟩
      · exact absurd (hxu hax) hau
      · exact hay
    · intro hay
      have := hy.1 hay
      simp only [mem_compl] at this
      exact ⟨Or.inr hay, this⟩

/-- If `k ≤ b`, exactly `C(|u|, k) · C(N - |u|, b - k)` of the `b`-subsets of `V`
meet `u` in `k` elements: sum `card_trace_eq` over the `k`-subsets `x` of `u`. -/
theorem card_trace_card_eq (u : Finset V) (b k : ℕ) (hkb : k ≤ b) :
    ((powersetCard b univ).filter (fun d => (u ∩ d).card = k)).card =
      u.card.choose k * (Fintype.card V - u.card).choose (b - k) := by
  rw [card_eq_sum_card_fiberwise (f := fun d => u ∩ d) (t := powersetCard k u)]
  · rw [← card_powersetCard k u, ← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun x hx => ?_
    rw [mem_powersetCard] at hx
    rw [← hx.2, ← card_trace_eq u x hx.1 b (hx.2 ▸ hkb), filter_filter]
    congr 1
    refine filter_congr fun d _ => ?_
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by rw [h], h⟩
  · intro d hd
    simp only [mem_coe, mem_filter, mem_powersetCard, subset_univ, true_and] at hd
    simp only [mem_coe, mem_powersetCard]
    exact ⟨inter_subset_left, hd.2⟩

end HubbardMoments
