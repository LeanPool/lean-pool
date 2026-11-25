/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.Higman
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Forall2
import Mathlib.Order.WellFoundedSet

/-!
# Proof of Higman's theorem (Graph Minors IV, (8.3))

This file proves `GraphMinor.GM04.Higman83Statement`, the theorem of Higman quoted as
Graph Minors IV, (8.3) (page 249): for every sequence of finite sets `X i` with labels `ℓ i` in a
well-quasi-order `Ω`, there is an infinite set `I` of indices such that for all `i < i'` in `I`
some injection `g : X i → X i'` satisfies `ℓ i x ≤ ℓ i' (g x)` for all `x ∈ X i`.

We represent each finite set `X i` as a duplicate-free list `(X i).toList`, map it by `ℓ i` to a
list in `Ω`, apply Mathlib's Higman lemma
(`Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂`) and extract a monotone
subsequence via `Set.PartiallyWellOrderedOn.exists_monotone_subseq`. A `List.SublistForall₂`
witness between two duplicate-free lists then yields the required injection.
-/

namespace GraphMinor.GM04

open Set

public section

/-- Graph Minors IV, (8.3) (page 249): for every sequence of finite sets `X i` with labels `ℓ i`
in a well-quasi-order `Ω`, there is an infinite set `I` of indices such that for all `i < i'` in
`I` some injection `g : X i → X i'` satisfies `ℓ i x ≤ ℓ i' (g x)` for all `x ∈ X i`. -/
theorem higman_8_3 : Higman83Statement := by
  classical
  intro κ Ω _ hwqo X ℓ
  have hU : (univ : Set Ω).PartiallyWellOrderedOn (· ≤ ·) :=
    partiallyWellOrderedOn_of_wellQuasiOrdered hwqo.wqo univ
  have hL := hU.partiallyWellOrderedOn_sublistForall₂
  have : IsPreorder (List Ω) (List.SublistForall₂ (· ≤ ·)) := ⟨⟩
  let f : ℕ → List Ω := fun i ↦ (X i).toList.map (ℓ i)
  have hf : ∀ i, f i ∈ {l : List Ω | ∀ x ∈ l, x ∈ (univ : Set Ω)} := fun _ _ _ ↦ mem_univ _
  obtain ⟨φ, hφ⟩ := hL.exists_monotone_subseq hf
  refine ⟨range φ, infinite_range_of_injective φ.injective, ?_⟩
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ hlt
  have hmn : m < n := φ.lt_iff_lt.1 hlt
  have hsub := hφ m n hmn.le
  dsimp only [f] at hsub
  rw [List.sublistForall₂_map_left_iff, List.sublistForall₂_map_right_iff] at hsub
  obtain ⟨g, hinj, hmem, hrel⟩ :=
    exists_inj_of_sublistForall₂ (X (φ m)).nodup_toList (X (φ n)).nodup_toList hsub
  refine ⟨g, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hinj x (Finset.mem_toList.2 hx) y (Finset.mem_toList.2 hy) hxy
  · intro x hx
    exact Finset.mem_toList.1 (hmem x (Finset.mem_toList.2 hx))
  · intro x hx
    exact hrel x (Finset.mem_toList.2 hx)

end

end GraphMinor.GM04
