/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section5
import LeanPool.GraphMinor.GM09.Basic

/-!
# The last path construction in XVI (5.4)

Two paths from the common vertex that avoid all the given disjoint paths
can be joined. Their union supplies the extra path in the last paragraph
of the proof on page 57.
-/

public section

namespace GraphMinor.GM16

open Set Graph GraphMinor.GM09

universe u v

/-- Spokes that meet only at their common start have distinct other ends. -/
theorem spoke_ends_injective
    {α : Type u} {β : Type v} {G : Graph α β} {v : α}
    {n : ℕ} {P : Fin n → Graph α β} {u : Fin n → α}
    (hP : ∀ i, u i ≠ v ∧ IsGraphPathWithEnds G (P i) v (u i))
    (hinter : ∀ i j, i ≠ j → V(P i) ∩ V(P j) = {v}) :
    Function.Injective u := by
  intro i j heq
  by_contra hne
  have hui : u i ∈ V(P j) := heq ▸ (hP j).2.right_mem
  have : u i ∈ ({v} : Set α) :=
    hinter i j hne ▸ ⟨(hP i).2.right_mem, hui⟩
  exact (hP i).1 (mem_singleton_iff.mp this)

/-- The count in the last paragraph of XVI (5.4), page 57: deleting a
set of at most `5 * m` vertices from at least `5 * m + 2` distinct spoke
ends leaves two ends. No containment between the deleted set and the
spoke ends is needed. -/
theorem exists_two_spoke_ends_outside
    {α : Type u} {n m : ℕ} {u : Fin n → α} {Y : Set α}
    (hu : Function.Injective u) (hY : Y.Finite)
    (hcard : Y.ncard ≤ 5 * m) (hn : 5 * m + 2 ≤ n) :
    ∃ i j, i ≠ j ∧ u i ∉ Y ∧ u j ∉ Y := by
  have hrange : (range u).ncard = n := by
    simpa using ncard_range_of_injective hu
  have hcount := ncard_le_ncard_sdiff_add_ncard (range u) Y hY
  have htwo : 1 < (range u \ Y).ncard := by omega
  obtain ⟨a, ⟨⟨i, rfl⟩, hi⟩, b, ⟨⟨j, rfl⟩, hj⟩, hab⟩ :=
    (one_lt_ncard ((finite_range u).sdiff)).mp htwo
  exact ⟨i, j, fun h => hab (congrArg u h), hi, hj⟩

/-- Graph Minors XVI, proof of (5.4), page 57: two distinct spokes that
avoid every `Q_j` supply the additional path. The spoke ends are distinct
because the spokes meet only at their common start. -/
theorem theorem_5_4_of_two_avoiding_spokes
    {α : Type u} {β : Type v} {G P P' : Graph α β} {v a b : α}
    {m : ℕ} {Q : Fin m → Graph α β} {s t : Fin m → α} {Z : Set α}
    (hP : IsGraphPathWithEnds G P v a)
    (hP' : IsGraphPathWithEnds G P' v b)
    (hav : a ≠ v) (hPP' : V(P) ∩ V(P') = {v})
    (ha : a ∈ Z) (hb : b ∈ Z)
    (hQ : ∀ j, IsGraphPathWithEnds G (Q j) (s j) (t j))
    (hst : ∀ j, s j ∈ Z ∧ t j ∈ Z ∧ s j ≠ t j)
    (hdisj : Pairwise (fun i j => Disjoint V(Q i) V(Q j)))
    (hPQ : ∀ j, Disjoint V(P) V(Q j))
    (hP'Q : ∀ j, Disjoint V(P') V(Q j)) :
    ∃ (R : Fin (m + 1) → Graph α β) (x y : Fin (m + 1) → α),
      Pairwise (fun i j => Disjoint V(R i) V(R j)) ∧
      ∀ i, x i ∈ Z ∧ y i ∈ Z ∧ x i ≠ y i ∧
        IsGraphPathWithEnds G (R i) (x i) (y i) := by
  have hab : a ≠ b := by
    intro hab
    have haP' : a ∈ V(P') := hab ▸ hP'.right_mem
    have : a ∈ ({v} : Set α) := hPP' ▸ ⟨hP.right_mem, haP'⟩
    exact hav (mem_singleton_iff.mp this)
  let L := subgraphUnion G P P'
  have hL : IsGraphPathWithEnds G L a b := hP.symm.subgraphUnion hP' hPP'
  have hLQ : ∀ j, Disjoint V(L) V(Q j) := by
    intro j
    rw [vertexSet_subgraphUnion, disjoint_union_left]
    exact ⟨hPQ j, hP'Q j⟩
  refine ⟨Fin.cons L Q, Fin.cons a s, Fin.cons b t, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hij
        exact False.elim (hij rfl)
      · intro _
        exact hLQ j
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro _
        exact (hLQ i).symm
      · intro hij
        exact hdisj (fun h => hij (congrArg Fin.succ h))
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨ha, hb, hab, hL⟩
    · exact ⟨(hst j).1, (hst j).2.1, (hst j).2.2, hQ j⟩

/-- Graph Minors XVI, (5.4), the case `m = 0`. Two spokes form the
required path, as in the last paragraph of the proof on page 57. -/
theorem theorem_5_4_zero
    {α : Type u} {β : Type v} {G : Graph α β} {v : α}
    {n : ℕ} {P : Fin n → Graph α β} {u : Fin n → α}
    (hP : ∀ i, u i ≠ v ∧ IsGraphPathWithEnds G (P i) v (u i))
    (hinter : ∀ i j, i ≠ j → V(P i) ∩ V(P j) = {v})
    (hn : 2 ≤ n) :
    ∃ (R : Fin 1 → Graph α β) (a b : Fin 1 → α),
      Pairwise (fun i j => Disjoint V(R i) V(R j)) ∧
      ∀ i, a i ∈ range u ∧ b i ∈ range u ∧ a i ≠ b i ∧
        IsGraphPathWithEnds G (R i) (a i) (b i) := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    change 0 = 1 at this
    contradiction
  exact theorem_5_4_of_two_avoiding_spokes
    (m := 0) (Q := fun k => k.elim0) (s := fun k => k.elim0)
    (t := fun k => k.elim0) (hP i).2 (hP j).2 (hP i).1 (hinter i j hij)
    ⟨i, rfl⟩ ⟨j, rfl⟩ (fun k => k.elim0) (fun k => k.elim0)
    (fun k => k.elim0) (fun k => k.elim0) (fun k => k.elim0)

end GraphMinor.GM16
