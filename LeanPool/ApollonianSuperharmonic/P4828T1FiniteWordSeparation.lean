/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Data.List.Induction
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Lattice.Disjoint


-- [TABLET NODE: P4828T1FiniteWordSeparation]

/-!
# P4828T1FiniteWordSeparation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4828T1FiniteWordSeparation {A B X : Type*}
    (G D : B → List A → Set X)
    (hroot : ∀ a b, a ≠ b → Disjoint (G a []) (G b []))
    (hsub : ∀ a w b, G a (w ++ [b]) ⊆ G a w)
    (hsibling : ∀ a w b c, b ≠ c →
      Disjoint (G a (w ++ [b])) (G a (w ++ [c])))
    (hexclude : ∀ a w b, Disjoint (G a (w ++ [b])) (D a w))
    (hinside : ∀ a w, D a w ⊆ G a w)
    (hnonempty : ∀ a w, (D a w).Nonempty) :
    (∀ a u v, G a (u ++ v) ⊆ G a u) ∧
    (∀ a u b v, G a (u ++ b :: v) ⊂ G a u ∧
      Disjoint (G a (u ++ b :: v)) (D a u)) ∧
    (∀ a b u v, (a ≠ b ∨ (¬ u <+: v) ∧ (¬ v <+: u)) →
      Disjoint (G a u) (G b v)) ∧
    ∀ a b u v, (a, u) ≠ (b, v) → Disjoint (D a u) (D b v) := by
-- BODY
  classical
  have descendant : ∀ a u v, G a (u ++ v) ⊆ G a u := by
    intro a u v
    induction v using List.reverseRecOn with
    | nil => simp
    | append_singleton v c ih =>
        simpa only [List.append_assoc] using (hsub a (u ++ v) c).trans ih
  have avoid : ∀ a u b v, Disjoint (G a (u ++ b :: v)) (D a u) := by
    intro a u b v
    have h := descendant a (u ++ [b]) v
    simp only [List.append_assoc, List.singleton_append] at h
    exact (hexclude a u b).mono_left h
  refine ⟨descendant, ?_, ?_, ?_⟩
  · intro a u b v
    refine ⟨?_, avoid a u b v⟩
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨descendant a u (b :: v), ?_⟩
    intro heq
    obtain ⟨p, hp⟩ := hnonempty a u
    have hp' : p ∈ G a (u ++ b :: v) := by rw [heq]; exact hinside a u hp
    exact Set.disjoint_left.mp (avoid a u b v) hp' hp
  · have incomparable : ∀ a u v w, (¬ u <+: v) → (¬ v <+: u) →
        Disjoint (G a (w ++ u)) (G a (w ++ v)) := by
      intro a u
      induction u with
      | nil =>
          intro v w h
          exact (h List.nil_prefix).elim
      | cons b u ih =>
          intro v w huv hvu
          cases v with
          | nil => exact (hvu List.nil_prefix).elim
          | cons c v =>
              by_cases hbc : b = c
              · subst c
                have h1 : ¬ u <+: v := fun h => huv ((List.prefix_cons_inj b).2 h)
                have h2 : ¬ v <+: u := fun h => hvu ((List.prefix_cons_inj b).2 h)
                simpa only [List.append_assoc, List.singleton_append] using
                  ih v (w ++ [b]) h1 h2
              · exact (hsibling a w b c hbc).mono
                  (by simpa only [List.append_assoc, List.singleton_append] using
                    descendant a (w ++ [b]) u)
                  (by simpa only [List.append_assoc, List.singleton_append] using
                    descendant a (w ++ [c]) v)
    intro a b u v h
    by_cases hab : a = b
    · subst b
      rcases h with h | h
      · exact (h rfl).elim
      · simpa using incomparable a u v [] h.1 h.2
    · exact (hroot a b hab).mono
        (by simpa using descendant a [] u) (by simpa using descendant b [] v)
  · have sameRoot : ∀ a u v w, u ≠ v →
        Disjoint (D a (w ++ u)) (D a (w ++ v)) := by
      intro a u
      induction u with
      | nil =>
          intro v w hne
          cases v with
          | nil => exact (hne rfl).elim
          | cons b v =>
              simpa only [List.append_nil] using
                ((avoid a w b v).mono_left (hinside a (w ++ b :: v))).symm
      | cons b u ih =>
          intro v w hne
          cases v with
          | nil =>
              simpa only [List.append_nil] using
                (avoid a w b u).mono_left (hinside a (w ++ b :: u))
          | cons c v =>
              by_cases hbc : b = c
              · subst c
                have huv : u ≠ v := by intro h; apply hne; rw [h]
                simpa only [List.append_assoc, List.singleton_append] using
                  ih v (w ++ [b]) huv
              · have hu := (hinside a (w ++ b :: u)).trans
                    (by simpa only [List.append_assoc, List.singleton_append] using
                      descendant a (w ++ [b]) u)
                have hv := (hinside a (w ++ c :: v)).trans
                    (by simpa only [List.append_assoc, List.singleton_append] using
                      descendant a (w ++ [c]) v)
                exact (hsibling a w b c hbc).mono hu hv
    intro a b u v hne
    by_cases hab : a = b
    · subst b
      have huv : u ≠ v := by intro h; exact hne (by rw [h])
      simpa using sameRoot a u v [] huv
    · exact (hroot a b hab).mono
        ((hinside a u).trans (by simpa using descendant a [] u))
        ((hinside b v).trans (by simpa using descendant b [] v))

end ApollonianSuperharmonic

end
