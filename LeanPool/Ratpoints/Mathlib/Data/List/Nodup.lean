/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

import Mathlib.Data.List.Nodup

/-!
# Permutations from the maps of lists without duplicates

Candidates for `Mathlib.Data.List.Nodup`, next to `List.Nodup.map_on` and `List.nodup_flatMap`: a
list without duplicates, mapped by a function that is injective on it, is a permutation of every
list without duplicates whose members are the images; and a concatenation `l.flatMap f` has no
duplicates when the member of `l` that gives an entry can be read off the entry.

## Main statements

* `List.perm_map_of_nodup`: the map of a list without duplicates by a function injective on it is
  a permutation of every list without duplicates with the same members.
* `List.Nodup.flatMap`: `l.flatMap f` has no duplicates when `l` and each `f a` have none and `a`
  is a function of each entry of `f a`.
-/

@[expose] public section

namespace List

variable {α β : Type*}

/-- A list without duplicates, mapped by a function that is injective on it, is a permutation of
every list without duplicates whose members are exactly the images; compare
`List.perm_ext_iff_of_nodup` and `List.Nodup.map_on`. -/
theorem perm_map_of_nodup {l : List α} {l' : List β} {f : α → β} (hl : l.Nodup) (hl' : l'.Nodup)
    (hf : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) (h : ∀ b, b ∈ l' ↔ ∃ a ∈ l, f a = b) :
    (l.map f).Perm l' :=
  (perm_ext_iff_of_nodup (hl.map_on hf) hl').mpr fun b ↦ by rw [mem_map, h]

/-- A concatenation `l.flatMap f` has no duplicates when `l` and each `f a` have none and the
member `a` of `l` can be read off each entry of `f a` by a function `g`, so that the lists `f a`
are disjoint; compare `List.nodup_flatMap`. -/
protected theorem Nodup.flatMap {l : List α} {f : α → List β} (hl : l.Nodup)
    (hf : ∀ a ∈ l, (f a).Nodup) (g : β → α) (hg : ∀ a ∈ l, ∀ b ∈ f a, g b = a) :
    (l.flatMap f).Nodup :=
  nodup_flatMap.mpr ⟨hf, hl.pairwise_of_forall_ne fun a ha a' ha' hne b hb hb' ↦
    hne ((hg a ha b hb).symm.trans (hg a' ha' b hb'))⟩

end List

end
