/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

/-!
# Counting the pairs in XVI (8.1)

Claim (5), page 72, takes the union of one separator for each unordered
pair of battlefield discs. There are at most half as many such pairs
as ordered pairs. Thus separators of size less than `φ²` already give
the stated bound. The printed per-pair bound `φ²/2` is unnecessary:
Menger's theorem gives size less than `φ²` from Claim (4).
-/

public section
namespace GraphMinor.GM16
open Finset

/-- The ordered pairs with first coordinate smaller than the second
occupy at most half of the square of a finite linearly ordered set. -/
theorem twice_card_increasing_pairs {ι : Type*} [LinearOrder ι] (s : Finset ι) :
    2 * ((s ×ˢ s).filter (fun p => p.1 < p.2)).card ≤ s.card ^ 2 := by
  classical
  let t := (s ×ˢ s).filter (fun p => p.1 < p.2)
  have hswap : (t.image Prod.swap).card = t.card :=
    card_image_of_injective t Prod.swap_injective
  have hdis : Disjoint t (t.image Prod.swap) := by
    apply disjoint_left.mpr
    intro p hp hp'
    obtain ⟨q, hq, hqp⟩ := mem_image.mp hp'
    have hpLt := (mem_filter.mp hp).2
    have hqLt := (mem_filter.mp hq).2
    subst p
    exact lt_asymm hpLt hqLt
  have hsub : t ∪ t.image Prod.swap ⊆ s ×ˢ s := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact (mem_filter.mp hp).1
    · obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
      have hq' := mem_product.mp (mem_filter.mp hq).1
      exact mem_product.mpr ⟨hq'.2, hq'.1⟩
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdis, hswap, card_product] at hc
  simpa only [pow_two, two_mul] using hc

/-- The union of one finite separator of size at most `φ²` for each
increasing pair satisfies the bound in XVI (8.1), Claim (5). In the
paper, Menger gives the stronger per-pair bound strictly below `φ²`. -/
theorem pair_separator_union_bound {ι α : Type*} [LinearOrder ι] [DecidableEq α]
    (s : Finset ι) (φ : ℕ) (Z : ι → ι → Finset α)
    (hZ : ∀ i ∈ s, ∀ j ∈ s, i < j → (Z i j).card ≤ φ ^ 2) :
    (((s ×ˢ s).filter (fun p => p.1 < p.2)).biUnion (fun p => Z p.1 p.2)).card <
      s.card ^ 2 * φ ^ 2 / 2 + 1 := by
  classical
  let t := (s ×ˢ s).filter (fun p => p.1 < p.2)
  have hb : (t.biUnion (fun p => Z p.1 p.2)).card ≤ t.card * φ ^ 2 := by
    calc
      _ ≤ ∑ p ∈ t, (Z p.1 p.2).card := card_biUnion_le
      _ ≤ ∑ _p ∈ t, φ ^ 2 := by
        apply sum_le_sum
        intro p hp
        have hm := mem_product.mp (mem_filter.mp hp).1
        exact hZ p.1 hm.1 p.2 hm.2 (mem_filter.mp hp).2
      _ = _ := by simp
  have hpairs := twice_card_increasing_pairs s
  have hm := Nat.mul_le_mul_right (φ ^ 2) hpairs
  have hdouble : 2 * (t.biUnion (fun p => Z p.1 p.2)).card ≤ s.card ^ 2 * φ ^ 2 := by
    dsimp only [t] at hb
    nlinarith
  dsimp only [t] at hdouble
  omega

end GraphMinor.GM16
