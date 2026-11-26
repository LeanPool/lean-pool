/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Logic.Relation
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Data.Set.Basic

/-!
# Selecting the two corners for a circle through the boundary vertex

The local drawing in XII (7.2) has two half-edges from the circle and
at least one from the old drawing. In their cyclic order each circle
half-edge has an old half-edge on at least one side. Otherwise the two
circle half-edges would form a whole orbit, missing the old half-edges.
The two selected mixed corners are distinct.
-/

public section

namespace GraphMinor.GM12

open Set

private theorem exists_mixed_corner_at {α : Type*} [Finite α]
    (next : α → α) (hinj : Function.Injective next)
    (hreach : ∀ a b, Relation.ReflTransGen (fun a b => b = next a) a b)
    (hneq : ∀ a, next a ≠ a)
    {old : Set α} (hold : old.Nonempty) {x y : α}
    (hx : x ∉ old) (hy : y ∉ old)
    (hbad : ∀ z, z ∉ old → z = x ∨ z = y) :
    ∃ k, (k = x ∧ next k ∈ old) ∨ (k ∈ old ∧ next k = x) := by
  by_cases hnext : next x ∈ old
  · exact ⟨x, Or.inl ⟨rfl, hnext⟩⟩
  · obtain ⟨p, hpx⟩ := Finite.surjective_of_injective hinj x
    by_cases hp : p ∈ old
    · exact ⟨p, Or.inr ⟨hp, hpx⟩⟩
    · have hnextx : next x = y := (hbad (next x) hnext).resolve_left (hneq x)
      have hpy : p = y := (hbad p hp).resolve_left (fun h => hneq x (h ▸ hpx))
      have hnexty : next y = x := hpy ▸ hpx
      obtain ⟨z, hz⟩ := hold
      have horbit : ∀ w, Relation.ReflTransGen (fun a b => b = next a) x w → w = x ∨ w = y := by
        intro w hpath
        induction hpath with
        | refl => exact Or.inl rfl
        | @tail a b _ hab ih =>
          rw [hab]
          rcases ih with rfl | rfl
          · exact Or.inr hnextx
          · exact Or.inl hnexty
      rcases horbit z (hreach x z) with rfl | rfl
      · exact (hx hz).elim
      · exact (hy hz).elim

/-- The two mixed corners used for the vertex diversion in XII (7.2),
page 260. The two new half-edges in a cyclic order can each be paired
with an adjacent old half-edge, using distinct corners. -/
theorem exists_two_mixed_corners {α : Type*} [Finite α]
    (next : α → α) (hinj : Function.Injective next)
    (hreach : ∀ a b, Relation.ReflTransGen (fun a b => b = next a) a b)
    (hneq : ∀ a, next a ≠ a)
    {old : Set α} (hold : old.Nonempty) {x y : α} (hxy : x ≠ y)
    (hx : x ∉ old) (hy : y ∉ old)
    (hbad : ∀ z, z ∉ old → z = x ∨ z = y) :
    ∃ k l, k ≠ l ∧
      ((k = x ∧ next k ∈ old) ∨ (k ∈ old ∧ next k = x)) ∧
      ((l = y ∧ next l ∈ old) ∨ (l ∈ old ∧ next l = y)) := by
  obtain ⟨k, hk⟩ := exists_mixed_corner_at next hinj hreach hneq hold hx hy hbad
  obtain ⟨l, hl⟩ := exists_mixed_corner_at next hinj hreach hneq hold hy hx
    (fun z hz => (hbad z hz).symm)
  refine ⟨k, l, ?_, hk, hl⟩
  intro hkl
  rcases hk with ⟨hkx, hkn⟩ | ⟨hko, hkn⟩
  · rcases hl with ⟨hly, _⟩ | ⟨hlo, _⟩
    · exact hxy (hkx.symm.trans (hkl.trans hly))
    · exact hx (hkx ▸ (hkl.symm ▸ hlo))
  · rcases hl with ⟨hly, _⟩ | ⟨_, hln⟩
    · exact hy (hly ▸ (hkl ▸ hko))
    · exact hxy (hkn.symm.trans ((congrArg next hkl).trans hln))

end GraphMinor.GM12
