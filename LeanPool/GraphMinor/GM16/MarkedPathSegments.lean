/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM09.Basic

/-!
# Consecutive marked vertices of a path

Trim an initial segment at the first new marked vertex. For the
final choice in XVI (8.1), first stop at the first marked vertex
outside the chosen shell, then trim backwards to the preceding
marked vertex. The segment between them has no other marked vertex.
This follows the choices of `t_i`, `u`, and `v` on pages 72–75.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09
universe u v
variable {α : Type u} {β : Type v}

/-- An initial path segment ends at the first marked vertex after
its marked start and has no other marked vertices. -/
theorem exists_initial_marked_segment {G P : Graph α β} {A : Set α} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    ∃ t ∈ A, t ≠ a ∧ ∃ R : Graph α β,
      R ≤ P ∧ IsGraphPathWithEnds G R a t ∧ V(R) ∩ A = {a, t} := by
  obtain ⟨a', ha', t, ht, R, hRP, hR⟩ :=
    hP.exists_isFromToPathWithEnds (X := {a}) (Y := A \ {a})
      (mem_singleton a) ⟨hb, hab.symm⟩
  have haa : a' = a := mem_singleton_iff.mp ha'
  subst a'
  refine ⟨t, ht.1, ht.2, R, hRP, hR.1, ?_⟩
  apply subset_antisymm
  · rintro x ⟨hxR, hxA⟩
    by_cases hxa : x = a
    · exact Or.inl hxa
    · exact Or.inr (mem_singleton_iff.mp (hR.2.2 ▸ ⟨hxR, hxA, hxa⟩))
  · rintro x (rfl | hxt)
    · exact ⟨hR.1.left_mem, ha⟩
    · rw [mem_singleton_iff] at hxt
      subst x
      exact ⟨hR.1.right_mem, ht.1⟩

/-- The first marked exit from a shell and the preceding marked
vertex are consecutive in the old marked set. This is the selection
of `u,v` in XVI (8.1), pages 74–75. -/
theorem exists_consecutive_marked_exit {G P : Graph α β} {A B : Set α} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) (ha : a ∈ A) (hb : b ∈ A)
    (hab : a ≠ b) (hbB : b ∉ B) :
    ∃ u ∈ A, ∃ v ∈ A,
      u ≠ v ∧ v ≠ a ∧ v ∉ B ∧ (u = a ∨ u ∈ B) ∧
      ∃ R : Graph α β, R ≤ P ∧ IsGraphPathWithEnds G R u v ∧
        V(R) ∩ A = {u, v} := by
  let E := A \ ({a} ∪ B)
  have hbE : b ∈ E := ⟨hb, fun h => h.elim hab.symm hbB⟩
  obtain ⟨a', ha', v, hv, Q, hQP, hQ⟩ :=
    hP.exists_isFromToPathWithEnds (mem_singleton a) hbE
  have haa : a' = a := mem_singleton_iff.mp ha'
  subst a'
  have hva : v ≠ a := fun h => hv.2 (Or.inl h)
  have hvB : v ∉ B := fun h => hv.2 (Or.inr h)
  obtain ⟨u, hu, huv, R, hRQ, hR, hRA⟩ :=
    exists_initial_marked_segment hQ.1.symm hv.1 ha hva
  have hCase : u = a ∨ u ∈ B := by
    by_cases hua : u = a
    · exact Or.inl hua
    · right
      by_contra huB
      have huE : u ∈ E := ⟨hu, fun h => h.elim hua huB⟩
      have huv' : u = v := mem_singleton_iff.mp
        (hQ.2.2 ▸ ⟨hRQ.vertexSet_mono hR.right_mem, huE⟩)
      exact huv huv'
  refine ⟨u, hu, v, hv.1, huv, hva, hvB, hCase, R, hRQ.trans hQP, hR.symm, ?_⟩
  simpa only [Set.pair_comm] using hRA

end GraphMinor.GM16
