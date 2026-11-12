/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween

-- [TABLET NODE: P4055T1GridPathImage]

/-!
# P4055T1GridPathImage

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4055T1GridPathImage : ∀ (f : GaussianInt → GaussianInt),
    Function.Injective f →
    (∀ a b : GaussianInt,
      (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) →
      (f b = f a + 1 ∨ f b = f a - 1 ∨
        f b = f a + ⟨0, 1⟩ ∨ f b = f a - ⟨0, 1⟩)) →
    ∀ (V : Set GaussianInt) (E : Set (Finset GaussianInt)) (x y : GaussianInt),
    SimpleGridPathBetween V E x y →
    SimpleGridPathBetween
      (f '' V) ((fun e : Finset GaussianInt => e.image f) '' E)
      (f x) (f y) := by
-- BODY
  intro f fi st V E x y h
  rcases h with ⟨p, hn, hl, hh, ht, hv, hs, he⟩
  refine ⟨p.map f, hn.map fi, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hl
  · rw [List.head?_map, hh]
    rfl
  · rw [List.getLast?_map, ht]
    rfl
  · rw [hv]
    ext z
    simp []
  · intro a b l₁ l₂ hmap
    have recover : ∀ (q : List GaussianInt),
        (∀ a b l₁ l₂, q = l₁ ++ a :: b :: l₂ →
          b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) →
        ∀ a b l₁ l₂, q.map f = l₁ ++ a :: b :: l₂ →
          b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩ := by
      intro q
      induction q with
      | nil => intro hs a b l₁ l₂ hm; cases l₁ <;> simp_all
      | cons z q ih =>
          intro hs a b l₁ l₂ hm
          cases l₁ with
          | nil =>
              cases q with
              | nil => simp_all
              | cons w q =>
                  simp? at hm
                  rw [← hm.1, ← hm.2.1]
                  exact st z w (hs z w [] q (by simp))
          | cons z' l' =>
              simp? at hm
              apply ih (fun c d k m hcm => hs c d (z :: k) m (by simp [hcm]))
                a b l' l₂ hm.2
    exact recover p hs a b l₁ l₂ hmap
  · intro e
    constructor
    · rintro ⟨d, hd, rfl⟩
      rcases (he d).mp hd with ⟨a, b, l₁, l₂, hp, rfl⟩
      refine ⟨f a, f b, l₁.map f, l₂.map f, ?_, ?_⟩
      · simpa using congrArg (List.map f) hp
      · simp [Finset.image_insert]
    · rintro ⟨a, b, l₁, l₂, hp, heq⟩
      have ha : a ∈ p.map f := by rw [hp]; simp
      have hb : b ∈ p.map f := by rw [hp]; simp
      rcases List.mem_map.mp ha with ⟨a₀, ha₀, rfl⟩
      rcases List.mem_map.mp hb with ⟨b₀, hb₀, rfl⟩
      have unmap : ∀ (q : List GaussianInt) (k m : List GaussianInt)
          (r s : GaussianInt), q.map f = k ++ f r :: f s :: m →
          ∃ k₀ m₀, q = k₀ ++ r :: s :: m₀ := by
        intro q
        induction q with
        | nil => intro k m r s h; cases k <;> simp_all
        | cons z q ihq =>
            intro k m r s h
            cases k with
            | nil =>
                simp? at h
                cases q with
                | nil => simp_all
                | cons w q =>
                    simp? at h
                    have hz : z = r := fi h.1
                    have hw : w = s := fi h.2.1
                    subst r; subst s
                    exact ⟨[], q, by simp []⟩
            | cons z' k' =>
                simp? at h
                rcases ihq k' m r s h.2 with ⟨k₀, m₀, hm⟩
                exact ⟨z :: k₀, m₀, by simp [hm]⟩
      have hdecomp : ∃ k m, p = k ++ a₀ :: b₀ :: m := by
        rcases unmap p l₁ l₂ a₀ b₀ hp with ⟨k, m, hm⟩
        exact ⟨k, m, hm⟩
      rcases hdecomp with ⟨k, m, hm⟩
      refine ⟨{a₀, b₀}, (he {a₀, b₀}).mpr ⟨a₀, b₀, k, m, hm, rfl⟩, ?_⟩
      simpa [Finset.image_insert] using heq.symm

end ApollonianSuperharmonic

end
