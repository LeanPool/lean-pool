/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.SimpleGridPath

-- [TABLET NODE: P3161T2PathSubwalk]

/-!
# P3161T2PathSubwalk

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3161T2PathSubwalk
    {V : Set GaussianInt} {E : Set (Finset GaussianInt)}
    (hpath : SimpleGridPath V E) (x y : GaussianInt)
    (hx : x ∈ V) (hy : y ∈ V) :
    ∃ w : List GaussianInt,
      w.head? = some x ∧ w.getLast? = some y ∧
      (∀ z ∈ w, z ∈ V) ∧
      ∀ a b : GaussianInt, ∀ l r : List GaussianInt,
        w = l ++ a :: b :: r → {a, b} ∈ E := by
-- BODY
  classical
  rcases hpath with ⟨p, _, _, hV, _, hE⟩
  have prefix_to (a : GaussianInt) (r : List GaussianInt)
      (b : GaussianInt) (hb : b ∈ a :: r) :
      ∃ w t : List GaussianInt, a :: r = w ++ t ∧
        w.head? = some a ∧ w.getLast? = some b := by
    rcases List.mem_cons.mp hb with hba | hb
    · subst b
      exact ⟨[a], r, rfl, rfl, rfl⟩
    · obtain ⟨l, t, h⟩ := List.append_of_mem hb
      refine ⟨a :: (l ++ [b]), t, ?_, rfl, ?_⟩
      · simp [h, List.append_assoc]
      · change ((a :: l) ++ [b]).getLast? = some b
        rw [List.getLast?_append_of_ne_nil (a :: l) (by simp)]
        rfl
  have segment : ∀ p : List GaussianInt, ∀ x y : GaussianInt,
      x ∈ p → y ∈ p →
      ∃ w : List GaussianInt, w.head? = some x ∧ w.getLast? = some y ∧
        ∃ l r : List GaussianInt,
          p = l ++ w ++ r ∨ p = l ++ w.reverse ++ r := by
    intro p
    induction p with
    | nil => simp
    | cons a p ih =>
      intro x y hx hy
      by_cases hxa : x = a
      · subst x
        obtain ⟨w, t, hp, hh, ht⟩ := prefix_to a p y hy
        exact ⟨w, hh, ht, [], t, Or.inl (by simpa using hp)⟩
      by_cases hya : y = a
      · subst y
        obtain ⟨w, t, hp, hh, ht⟩ := prefix_to a p x hx
        refine ⟨w.reverse, ?_, ?_, [], t, Or.inr ?_⟩
        · simpa using ht
        · simpa using hh
        · simpa using hp
      obtain ⟨w, hh, ht, l, r, h | h⟩ :=
        ih x y (List.mem_of_ne_of_mem hxa hx) (List.mem_of_ne_of_mem hya hy)
      · exact ⟨w, hh, ht, a :: l, r, Or.inl (by simp [h])⟩
      · exact ⟨w, hh, ht, a :: l, r, Or.inr (by simp [h])⟩
  obtain ⟨w, hh, ht, l, r, hs⟩ := segment p x y
    (by simpa [hV] using hx) (by simpa [hV] using hy)
  refine ⟨w, hh, ht, ?_, ?_⟩
  · intro z hz
    have hzp : z ∈ p := by
      rcases hs with hs | hs <;> rw [hs]
      · simp [hz]
      · simp [hz]
    simpa [hV] using hzp
  · intro a b k s h
    apply (hE {a, b}).mpr
    rcases hs with hs | hs
    · exact ⟨a, b, l ++ k, s ++ r, by simp [hs, h, List.append_assoc], rfl⟩
    · refine ⟨b, a, l ++ s.reverse, k.reverse ++ r, ?_, ?_⟩
      · simp [hs, h, List.reverse_append, List.append_assoc]
      · exact Finset.pair_comm a b

end ApollonianSuperharmonic

end
