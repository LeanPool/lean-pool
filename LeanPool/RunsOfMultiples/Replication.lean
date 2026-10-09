/-
Copyright (c) 2026 Jason Hoelscher-Obermaier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5
-/
module

-- Adapted for Lean Pool: module visibility, imports, and proof organization.

public import LeanPool.RunsOfMultiples.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Tactic.Ring

/-!
# Replicating finite multiplicative blocks

Disjoint dilates and padding preserve cardinality and a quantitative lower bound on runs.
-/

@[expose] public section

open Finset

namespace RunsOfMultiples

/-! ### Replication of a block -/

lemma pow_mul_inj {M j j' a a' : ℕ} (ha : 0 < a) (ha' : 0 < a') (haM : a < M) (haM' : a' < M)
    (h : M ^ j * a = M ^ j' * a') : j = j' ∧ a = a' := by
  have hM : 0 < M := by omega
  have key : ∀ {j j' a a' : ℕ}, 0 < a' → a < M → j < j' → M ^ j * a ≠ M ^ j' * a' := by
    intro j j' a a' ha' haM hjj' h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hjj'
    have h' : M ^ j * a = M ^ j * (M ^ d * M * a') := by rw [h]; ring
    have h2 := Nat.eq_of_mul_eq_mul_left (pow_pos hM j) h'
    have h1 : 1 ≤ M ^ d := Nat.one_le_pow _ _ hM
    have h3 : 1 * M * 1 ≤ M ^ d * M * a' := Nat.mul_le_mul (Nat.mul_le_mul h1 le_rfl) ha'
    omega
  rcases lt_trichotomy j j' with hlt | rfl | hgt
  · exact absurd h (key ha' haM hlt)
  · exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (pow_pos hM j) h⟩
  · exact absurd h.symm (key ha haM' hgt)

/-- Replication: from a block `B` with a subset `G` whose first `y` multiples lie in `B`,
build an `n`-element set of positive integers whose `kVal`-sum is at least
`⌊n / |B|⌋ · |G| · (y + 1)`. -/
lemma replicate (B G : Finset ℕ) (y n : ℕ) (hB : ∀ a ∈ B, 0 < a) (hGB : G ⊆ B)
    (hG : ∀ a ∈ G, ∀ j, 1 ≤ j → j ≤ y → j * a ∈ B) :
    ∃ S : Finset ℕ, (∀ a ∈ S, 0 < a) ∧ S.card = n ∧
      n / B.card * G.card * (y + 1) ≤ ∑ a ∈ S, kVal S a := by
  set M := B.sup id + 1 with hM
  set t := n / B.card with ht
  have hMpos : 0 < M := Nat.succ_pos _
  have hltM : ∀ a ∈ B, a < M := fun a ha => Nat.lt_succ_of_le (Finset.le_sup (f := id) ha)
  set φ : ℕ × ℕ → ℕ := fun p => M ^ p.1 * p.2 with hφ
  have hinj : Set.InjOn φ ↑(range t ×ˢ B) := by
    rintro ⟨j, a⟩ hja ⟨j', a'⟩ hja' h
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio, mem_coe] at hja hja'
    obtain ⟨h1, h2⟩ := pow_mul_inj (hB a hja.2) (hB a' hja'.2) (hltM a hja.2) (hltM a' hja'.2) h
    exact Prod.ext h1 h2
  set T := (range t ×ˢ B).image φ with hT
  set G' := (range t ×ˢ G).image φ with hG'
  have hTcard : T.card ≤ n := by
    refine card_image_le.trans ?_
    rw [card_product, card_range]
    exact Nat.div_mul_le_self n B.card
  have hUcard : n ≤ (T ∪ Icc 1 n).card := by
    have := card_le_card (subset_union_right (s₁ := T) (s₂ := Icc 1 n))
    simpa using this
  obtain ⟨S, hTS, hSU, hScard⟩ := exists_subsuperset_card_eq subset_union_left hTcard hUcard
  have hTpos : ∀ x ∈ T, 0 < x := by
    intro x hx
    obtain ⟨⟨j, a⟩, hja, rfl⟩ := mem_image.1 hx
    rw [mem_product] at hja
    exact Nat.mul_pos (pow_pos hMpos j) (hB a hja.2)
  have hSpos : ∀ a ∈ S, 0 < a := by
    intro a ha
    rcases mem_union.1 (hSU ha) with h | h
    · exact hTpos a h
    · exact (mem_Icc.1 h).1
  have hG'T : G' ⊆ T := image_subset_image (product_subset_product_right hGB)
  have hk : ∀ x ∈ G', y + 1 ≤ kVal S x := by
    intro x hx
    obtain ⟨⟨j, a⟩, hja, rfl⟩ := mem_image.1 hx
    rw [mem_product] at hja
    have hxpos : 0 < φ (j, a) := hTpos _ (hG'T hx)
    have := (forall_mul_mem_iff S hxpos y).1 (fun i hi => by
      rw [mem_Icc] at hi
      refine hTS (mem_image.2 ⟨(j, i * a), mem_product.2 ⟨hja.1, hG a hja.2 i hi.1 hi.2⟩, ?_⟩)
      simp only [hφ]
      ring)
    omega
  have hG'card : G'.card = t * G.card := by
    rw [card_image_of_injOn (hinj.mono (coe_subset.2 (product_subset_product_right hGB))),
      card_product, card_range]
  refine ⟨S, hSpos, hScard, ?_⟩
  calc t * G.card * (y + 1) = ∑ x ∈ G', (y + 1) := by rw [sum_const, nsmul_eq_mul, hG'card]; rfl
    _ ≤ ∑ x ∈ G', kVal S x := sum_le_sum hk
    _ ≤ ∑ x ∈ S, kVal S x := sum_le_sum_of_subset (hG'T.trans hTS)

end RunsOfMultiples
