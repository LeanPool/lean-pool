/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/RegularTreeCompatibility.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import Mathlib.SetTheory.ZFC.Basic

/-!
# Regular Tree Compatibility
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RegularTreeCompatibility

theorem words_compare (s t : List Bool) :
    s <+: t ∨ t <+: s ∨ ∃ a u v : List Bool,
      (s = a ++ [false] ++ u ∧ t = a ++ [true] ++ v) ∨
      (s = a ++ [true] ++ u ∧ t = a ++ [false] ++ v) := by
  induction s generalizing t with
  | nil => exact Or.inl List.nil_prefix
  | cons b s ih =>
    cases t with
    | nil => exact Or.inr (Or.inl List.nil_prefix)
    | cons d t =>
      by_cases h : b = d
      · subst d
        rcases ih t with h|h|⟨a,u,v,h|h⟩
        · exact Or.inl (by simpa only [List.cons_prefix_cons, true_and] using h)
        · exact Or.inr (Or.inl (by simpa only [List.cons_prefix_cons, true_and] using h))
        · exact Or.inr (Or.inr ⟨b::a,u,v,Or.inl ⟨by simp [h.1],by simp [h.2]⟩⟩)
        · exact Or.inr (Or.inr ⟨b::a,u,v,Or.inr ⟨by simp [h.1],by simp [h.2]⟩⟩)
      · cases b <;> cases d
        · exact False.elim (h rfl)
        · exact Or.inr (Or.inr ⟨[],s,t,Or.inl ⟨rfl,rfl⟩⟩)
        · exact Or.inr (Or.inr ⟨[],s,t,Or.inr ⟨rfl,rfl⟩⟩)
        · exact False.elim (h rfl)

theorem comparable_of_overlap (f : List Bool → ZFSet.{0})
    (hd : ∀ a u v : List Bool, ∀ p ∈ f (a ++ [false] ++ u),
      p ∉ f (a ++ [true] ++ v))
    (s t : List Bool) (p : ZFSet.{0}) (hp : p ∈ f s) (hq : p ∈ f t) :
    s <+: t ∨ t <+: s := by
  rcases words_compare s t with h|h|⟨a,u,v,h|h⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim (hd a u v p (h.1 ▸ hp) (h.2 ▸ hq))
  · exact False.elim (hd a v u p (h.2 ▸ hq) (h.1 ▸ hp))

theorem subset_iff_prefix (f : List Bool → ZFSet.{0})
    (hn : ∀ s, f s ≠ ∅)
    (hm : ∀ s t, s <+: t → f t ⊆ f s)
    (hd : ∀ a u v : List Bool, ∀ p ∈ f (a ++ [false] ++ u),
      p ∉ f (a ++ [true] ++ v)) (s t : List Bool) :
    f t ⊆ f s ↔ s <+: t := by
  constructor
  · intro h
    obtain he|⟨p,hp⟩ := ZFSet.eq_empty_or_nonempty (f t)
    · exact False.elim (hn t he)
    rcases comparable_of_overlap f hd s t p (h hp) hp with hs|⟨u,hu⟩
    · exact hs
    cases u with
    | nil =>
      have he : t = s := by simpa only [List.append_nil] using hu
      exact ⟨[], by simpa only [List.append_nil] using he.symm⟩
    | cons b u =>
      have hx : f (t ++ [!b]) ⊆ f t := hm _ _ ⟨[!b],rfl⟩
      obtain he|⟨q,hq⟩ := ZFSet.eq_empty_or_nonempty (f (t ++ [!b]))
      · exact False.elim (hn _ he)
      have hqs : q ∈ f s := h (hx hq)
      have hqs' : q ∈ f (t ++ [b] ++ u) := by
        simpa only [List.append_assoc, List.singleton_append, hu] using hqs
      cases b
      · exact False.elim (hd t u [] q hqs' (by simpa using hq))
      · exact False.elim (hd t [] u q (by simpa using hq) hqs')
  · exact hm s t

end TuringRigidity.RegularTreeCompatibility

end OAI
