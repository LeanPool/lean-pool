/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.List.Basic

/-!
# Lemmas on lists

Candidates for Mathlib's lemmas on lists, about the notions of core: filtering a list before
`List.flatMap f` changes nothing when every element `x` with `f x ≠ []` passes the filter, the
counterpart of `Finset.prod_filter_of_ne`, next to `List.flatMap_congr`, and so a list without
duplicates within another one without duplicates that holds every `x` with `f x ≠ []` gives a
permutation of its `List.flatMap f`; and a filter by a test that holds on all elements of a list
or on none keeps all of it or nothing.

## Main statements

* `List.flatMap_filter_of_ne`: a filter before `List.flatMap` that changes nothing.
* `List.perm_flatMap_of_nodup`: the `List.flatMap` of a list without duplicates of members of a
  list `l` without duplicates, in any order, that holds every member with a nonempty image, is a
  permutation of that of `l`.
* `List.filter_eq_ite_of_forall`: a filter that keeps all of a list or nothing.
-/

@[expose] public section

namespace List

variable {α β : Type*}

/-- Filtering the list `l` by `p` before `List.flatMap f` changes nothing when every element `x`
of `l` with `f x ≠ []` satisfies `p`; compare `Finset.prod_filter_of_ne`. -/
theorem flatMap_filter_of_ne {l : List α} {p : α → Bool} {f : α → List β}
    (h : ∀ x ∈ l, f x ≠ [] → p x) : (l.filter p).flatMap f = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have ih := ih fun y hy ↦ h y (.tail _ hy)
    by_cases hp : p x
    · simp [hp, ih]
    · have hf : f x = [] := by_contra fun hf ↦ hp (h x (.head _) hf)
      simp [hp, ih, hf]

/-- Filtering by a test that holds on every element of `l` exactly when `P` holds keeps all of `l`
or nothing. -/
theorem filter_eq_ite_of_forall {l : List α} {p : α → Bool} {P : Prop} [Decidable P]
    (h : ∀ a ∈ l, p a ↔ P) :
    l.filter p = if P then l else [] := by
  split_ifs with hP
  · exact filter_eq_self.mpr fun a ha ↦ (h a ha).mpr hP
  · exact filter_eq_nil_iff.mpr fun a ha hpa ↦ hP ((h a ha).mp hpa)

/-- A list `l'` without duplicates whose members lie in the list `l` without duplicates, and which
holds every member `x` of `l` with `f x ≠ []`, gives a permutation of `l.flatMap f`, whatever the
order of `l'`: `l'` is a permutation of the members of `l` that it holds
(`List.perm_ext_iff_of_nodup`), and the others give nothing (`List.flatMap_filter_of_ne`). -/
theorem perm_flatMap_of_nodup {l l' : List α} {f : α → List β} (hl : l.Nodup)
    (hl' : l'.Nodup) (hsub : l' ⊆ l) (h : ∀ x ∈ l, f x ≠ [] → x ∈ l') :
    (l'.flatMap f).Perm (l.flatMap f) := by
  classical
  have hp : l'.Perm (l.filter (· ∈ l')) :=
    (perm_ext_iff_of_nodup hl' (hl.filter _)).mpr fun x ↦ by simpa using fun hx ↦ hsub hx
  rw [← flatMap_filter_of_ne (p := (· ∈ l')) fun x hx hf ↦ decide_eq_true (h x hx hf)]
  exact hp.flatMap_right f

end List

end
