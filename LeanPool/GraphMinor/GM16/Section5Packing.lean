/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section5Forest
public import LeanPool.GraphMinor.GM16.ForestMarked
import Mathlib.Data.Fintype.EquivFin

/-!
# The forest case of XVI (5.3)

Pack the marked paths using the subtree packing theorem. If there are too
few paths, its cover has fewer than `μ` vertices. Assign each marked
vertex a first-hit path to this cover. The count in the paper supplies
`τ + 1` marked vertices assigned to one cover vertex. Omitting that
vertex itself leaves the required fan.
-/

public section
namespace GraphMinor.GM16

open Set SimpleGraph
universe u

/-- Graph Minors XVI, proof of (5.3), page 56, after choosing the forest.
This proves both alternatives for a finite forest with the stated
condition on its marked vertices. -/
theorem forest_marked_paths_or_fan
    {V : Type u} [Finite V] (G : SimpleGraph V) (Y : Set V) (μ τ : ℕ)
    (hG : G.IsAcyclic)
    (hcomp : ∀ y ∈ Y, ∃ z ∈ Y, z ≠ y ∧ G.Reachable y z)
    (hcount : τ * (μ - 1) < Y.ncard) :
    (∃ Q : Fin μ → MarkedPath G Y,
      Pairwise (fun i j => Disjoint {z | z ∈ (Q i).path.val.support}
        {z | z ∈ (Q j).path.val.support})) ∨
    (∃ (x : V) (s : Fin τ → V) (P : ∀ i, G.Path (s i) x),
      Function.Injective s ∧
      (∀ i j, i ≠ j → {z | z ∈ (P i).val.support} ∩
        {z | z ∈ (P j).val.support} = {x}) ∧
      ∀ i, s i ∈ Y ∧ s i ≠ x ∧
        ∀ z ∈ (P i).val.support, z ∈ Y → z = x ∨ z = s i) := by
  classical
  obtain ⟨I, X, hsize, hdisj, hcover⟩ :=
    forest_packing_cover G (fun q : MarkedPath G Y => {z | z ∈ q.path.val.support})
      hG (fun q => walk_isSubtreeSet q.path.val)
  by_cases hlarge : μ ≤ I.card
  · obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
      (α := Fin μ) (s := I) (by simpa using hlarge)
    refine Or.inl ⟨e, ?_⟩
    intro i j hij
    exact hdisj (e i) (he ⟨i, rfl⟩) (e j) (he ⟨j, rfl⟩) (e.injective.ne hij)
  · have hsmall : X.card ≤ μ - 1 := by omega
    have hX : ∀ q : MarkedPath G Y,
        ∃ x ∈ (X : Set V), x ∈ q.path.val.support := hcover
    have hpaths : ∀ y : Y, ∃ x ∈ (X : Set V), ∃ p : G.Path y.val x,
        ∀ z ∈ p.val.support, z ∈ (X : Set V) → z = x := by
      intro y
      obtain ⟨z, hz, hzy, ⟨r⟩⟩ := hcomp y.val y.property
      obtain ⟨w, hwX, hwr⟩ := marked_cover_meets_walk hX r y.property hz hzy.symm
      obtain ⟨x, hx, p, _, hfirst⟩ := exists_path_first_hit
        (X := (X : Set V)) (U := univ) (r.takeUntil w hwr) hwX (by simp)
      exact ⟨x, hx, p, hfirst⟩
    choose f hf p hp using hpaths
    have hY : Y.Finite := Set.toFinite Y
    obtain ⟨y₀, hy₀⟩ := (ncard_pos hY).mp (lt_of_le_of_lt (Nat.zero_le _) hcount)
    let f' : V → V := fun y => if hy : y ∈ Y then f ⟨y, hy⟩ else f ⟨y₀, hy₀⟩
    have hf' : ∀ y ∈ Y, f' y ∈ (X : Set V) := by
      intro y hy
      simpa only [f', dite_eq_left hy] using hf ⟨y, hy⟩
    have hnum : τ * (X : Set V).ncard < Y.ncard := by
      simpa only [Set.ncard_coe_finset] using
        lt_of_le_of_lt (Nat.mul_le_mul_left τ hsmall) hcount
    obtain ⟨x, _, Y', hY'Y, hY'card, hY'f⟩ :=
      exists_many_marked_vertices_at_one_vertex X.finite_toSet hY hf' hnum
    let B := Y' \ {x}
    have hB : B.Finite := (hY.subset hY'Y).sdiff
    have hBcard : τ ≤ B.ncard := by
      have hsub := ncard_le_ncard_sdiff_add_ncard Y' {x} (finite_singleton x)
      rw [ncard_singleton] at hsub
      dsimp only [B]
      omega
    obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
      (α := Fin τ) (s := hB.toFinset) (by
        rw [Fintype.card_fin, ← ncard_eq_toFinset_card B hB]
        exact hBcard)
    have heB : ∀ i, e i ∈ B := fun i => hB.mem_toFinset.mp (he ⟨i, rfl⟩)
    have heY : ∀ i, e i ∈ Y := fun i => hY'Y (heB i).1
    have hfx : ∀ i, f ⟨e i, heY i⟩ = x := by
      intro i
      simpa only [f', dite_eq_left (heY i)] using hY'f (e i) (heB i).1
    have hP : ∀ i, ∃ q : G.Path (e i) x,
        ∀ z ∈ q.val.support, z ∈ (X : Set V) → z = x := by
      intro i
      have h : ∃ q : G.Path (e i) (f ⟨e i, heY i⟩),
          ∀ z ∈ q.val.support, z ∈ (X : Set V) → z = f ⟨e i, heY i⟩ :=
        ⟨p ⟨e i, heY i⟩, hp ⟨e i, heY i⟩⟩
      rw [hfx i] at h
      exact h
    choose P hP using hP
    refine Or.inr ⟨x, e, P, e.injective, ?_, ?_⟩
    · intro i j hij
      exact first_hit_paths_inter_eq hX (heY i) (heY j) (e.injective.ne hij)
        (P i) (P j) (hP i) (hP j)
    · intro i
      refine ⟨heY i, ?_, ?_⟩
      · exact fun h => (heB i).2 (mem_singleton_iff.mpr h)
      · intro z hz hzY
        exact (first_hit_path_marked_only_at_ends hX (heY i) (P i) (hP i) z hz hzY).symm

end GraphMinor.GM16
