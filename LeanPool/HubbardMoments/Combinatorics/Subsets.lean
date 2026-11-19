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

/-- If `x ⊆ u` and `|x| ≤ b`, count the `b`-subsets whose intersection with `u` is
`x` by counting the subsets of `(u \ x)ᶜ` that contain `x`. -/
theorem card_trace_eq (u x : Finset V) (hxu : x ⊆ u) (b : ℕ) (hxb : x.card ≤ b) :
    ((powersetCard b univ).filter (fun d => u ∩ d = x)).card =
      (Fintype.card V - u.card).choose (b - x.card) := by
  have hfilter : (powersetCard b (univ : Finset V)).filter (fun d => u ∩ d = x) =
      (powersetCard b (u \ x)ᶜ).filter (x ⊆ ·) := by
    ext d
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
    constructor
    · rintro ⟨hcard, hinter⟩
      refine ⟨⟨fun a ha => ?_, hcard⟩, fun a ha => ?_⟩
      · simp only [mem_compl, mem_sdiff]
        exact fun hb => hb.2 (hinter ▸ mem_inter.mpr ⟨hb.1, ha⟩)
      · rw [← hinter] at ha
        exact (mem_inter.mp ha).2
    · rintro ⟨⟨hd, hcard⟩, hxd⟩
      refine ⟨hcard, ?_⟩
      ext a
      rw [mem_inter]
      refine ⟨fun ha => ?_, fun ha => ⟨hxu ha, hxd ha⟩⟩
      by_contra ha'
      exact (mem_compl.mp (hd ha.2)) (mem_sdiff.mpr ⟨ha.1, ha'⟩)
  have hx : x ⊆ (u \ x)ᶜ := fun _ ha => by simp [ha]
  rw [hfilter, card_filter_powersetCard_subset _ _ _ hx hxb, card_compl,
    card_sdiff_of_subset hxu]
  have hu : u.card ≤ Fintype.card V := card_le_univ _
  have hxu' := card_le_card hxu
  congr 1
  omega

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
