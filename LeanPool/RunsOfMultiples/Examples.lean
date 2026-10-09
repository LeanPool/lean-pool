/-
Copyright (c) 2026 Jason Hoelscher-Obermaier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5
-/
module

-- Adapted for Lean Pool: module visibility, imports, and proof organization.

public import LeanPool.RunsOfMultiples.Defs

/-!
# Sanity checks for `kVal`

`kVal S a` is computed on a small example: for `S = {1, 2, 3, 4, 6}` the values are
`k(1) = 5, k(2) = 4, k(3) = 3, k(4) = 2, k(6) = 2`, so `∑ k = 16`, beating `{1, …, 5}` (`∑ k = 15`).
-/

open Finset

@[expose] public section

namespace RunsOfMultiples

/-- `kVal` is characterised by: `k * a ∉ S`, and `j * a ∈ S` for `0 < j < k`. -/
lemma kVal_eq_of {S : Finset ℕ} {a k : ℕ} (hk : 0 < k) (hnot : k * a ∉ S)
    (hall : ∀ j ∈ Ioo 0 k, j * a ∈ S) : kVal S a = k := by
  have hne : {k : ℕ | 0 < k ∧ k * a ∉ S}.Nonempty := ⟨k, hk, hnot⟩
  apply le_antisymm (Nat.sInf_le (show k ∈ {k : ℕ | 0 < k ∧ k * a ∉ S} from ⟨hk, hnot⟩))
  by_contra h
  push Not at h
  obtain ⟨hpos, hm⟩ := Nat.sInf_mem hne
  exact hm (hall _ (mem_Ioo.2 ⟨hpos, h⟩))

example : ∑ a ∈ ({1, 2, 3, 4, 6} : Finset ℕ), kVal {1, 2, 3, 4, 6} a = 16 := by
  simp only [sum_insert (by decide : (1 : ℕ) ∉ ({2, 3, 4, 6} : Finset ℕ)),
    sum_insert (by decide : (2 : ℕ) ∉ ({3, 4, 6} : Finset ℕ)),
    sum_insert (by decide : (3 : ℕ) ∉ ({4, 6} : Finset ℕ)),
    sum_insert (by decide : (4 : ℕ) ∉ ({6} : Finset ℕ)), sum_singleton,
    kVal_eq_of (S := {1, 2, 3, 4, 6}) (a := 1) (k := 5) (by decide) (by decide) (by decide),
    kVal_eq_of (S := {1, 2, 3, 4, 6}) (a := 2) (k := 4) (by decide) (by decide) (by decide),
    kVal_eq_of (S := {1, 2, 3, 4, 6}) (a := 3) (k := 3) (by decide) (by decide) (by decide),
    kVal_eq_of (S := {1, 2, 3, 4, 6}) (a := 4) (k := 2) (by decide) (by decide) (by decide),
    kVal_eq_of (S := {1, 2, 3, 4, 6}) (a := 6) (k := 2) (by decide) (by decide) (by decide)]
  rfl

example : ∑ a ∈ Icc 1 5, kVal (Icc 1 5) a = 15 := by
  simp only [show Icc 1 5 = ({1, 2, 3, 4, 5} : Finset ℕ) by decide]
  simp only [sum_insert (by decide : (1 : ℕ) ∉ ({2, 3, 4, 5} : Finset ℕ)),
    sum_insert (by decide : (2 : ℕ) ∉ ({3, 4, 5} : Finset ℕ)),
    sum_insert (by decide : (3 : ℕ) ∉ ({4, 5} : Finset ℕ)),
    sum_insert (by decide : (4 : ℕ) ∉ ({5} : Finset ℕ)), sum_singleton,
    kVal_eq_of (S := {1, 2, 3, 4, 5}) (a := 1) (k := 6) (by decide) (by decide) (by decide),
    kVal_eq_of (S := {1, 2, 3, 4, 5}) (a := 2) (k := 3) (by decide) (by decide) (by decide),
    kVal_eq_of (S := {1, 2, 3, 4, 5}) (a := 3) (k := 2) (by decide) (by decide) (by decide),
    kVal_eq_of (S := {1, 2, 3, 4, 5}) (a := 4) (k := 2) (by decide) (by decide) (by decide),
    kVal_eq_of (S := {1, 2, 3, 4, 5}) (a := 5) (k := 2) (by decide) (by decide) (by decide)]
  rfl

end RunsOfMultiples
