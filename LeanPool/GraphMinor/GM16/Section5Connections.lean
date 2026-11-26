/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section5
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.Walks

/-!
# Connections after removing the common start in XVI (5.4)

A spoke meeting a path that avoids its start joins its other end to
both ends of that path after the common start is removed. At least one
of those two ends differs from the spoke end. This identifies the spokes
that avoid all the given paths in the last paragraph of (5.4).
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09
universe u v

/-- A graph walk witnesses reachability for the adjacency relation. -/
theorem graphWalk_adj_reachable
    {α : Type u} {β : Type v} {G : Graph α β} {a b : α}
    (W : GraphWalk G a b) : Relation.ReflTransGen G.Adj a b := by
  induction W with
  | nil _ => exact .refl
  | cons he W ih => exact .head ⟨_, he⟩ ih

/-- A path in a graph supplies a walk in that graph. -/
theorem graphPath_exists_walk
    {α : Type u} {β : Type v} {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) : Nonempty (GraphWalk G a b) := by
  obtain ⟨hPG, W, _, _, _⟩ := hP
  obtain ⟨W', _, _⟩ := exists_walk_up_of_le hPG W
  exact ⟨W'⟩

/-- A suffix of a path, starting after its first vertex, avoids that
first vertex. Split the path at the new starting vertex. -/
theorem path_suffix_avoids_start
    {α : Type u} {β : Type v} {G P : Graph α β} {a b w : α}
    (hP : IsGraphPathWithEnds G P a b) (hw : w ∈ V(P)) (hwa : w ≠ a) :
    ∃ R : Graph α β, R ≤ P ∧ IsGraphPathWithEnds G R w b ∧ a ∉ V(R) := by
  obtain ⟨L, R, _, hRP, hL, hR, _, hinter, _⟩ := hP.exists_split_at hw
  refine ⟨R, hRP, hR.mono hP.le, ?_⟩
  intro haR
  have hamem : a ∈ ({w} : Set α) := hinter ▸ ⟨hL.left_mem, haR⟩
  have haw := mem_singleton_iff.mp hamem
  exact hwa haw.symm

/-- The connection used in XVI (5.4), page 57. If a spoke meets a path
with two different ends that avoids the common start, its other end is
joined to a different end of that path after the common start is deleted. -/
theorem spoke_end_reaches_other_marked_end
    {α : Type u} {β : Type v} {G P Q : Graph α β} {v a s t : α}
    (hP : IsGraphPathWithEnds G P v a)
    (hQ : IsGraphPathWithEnds G Q s t) (hst : s ≠ t)
    (hvQ : v ∉ V(Q)) (hmeet : (V(P) ∩ V(Q)).Nonempty) :
    ∃ z ∈ ({s, t} : Set α), z ≠ a ∧
      Nonempty (GraphWalk (deleteVertices G {v}) a z) := by
  classical
  obtain ⟨w, hwP, hwQ⟩ := hmeet
  have hwv : w ≠ v := fun h => hvQ (h ▸ hwQ)
  obtain ⟨R, _, hR, hvR⟩ := path_suffix_avoids_start hP hwP hwv
  have hRD : IsGraphPathWithEnds (deleteVertices G {v}) R w a :=
    hR.in_deleteVertices (Set.disjoint_singleton_left.mpr hvR)
  have hQD : IsGraphPathWithEnds (deleteVertices G {v}) Q s t :=
    hQ.in_deleteVertices (Set.disjoint_singleton_left.mpr hvQ)
  have hreach : ∀ z ∈ V(Q), Nonempty (GraphWalk (deleteVertices G {v}) a z) := by
    intro z hz
    obtain ⟨L, _, _, hL⟩ := hQD.exists_subpath hwQ hz
    obtain ⟨W₁⟩ := graphPath_exists_walk hRD.symm
    obtain ⟨W₂⟩ := graphPath_exists_walk hL
    exact ⟨W₁.append W₂⟩
  by_cases hsa : s = a
  · refine ⟨t, mem_insert_of_mem s (mem_singleton t), ?_, hreach t hQ.right_mem⟩
    exact fun hta => hst (hsa.trans hta.symm)
  · exact ⟨s, mem_insert s {t}, hsa, hreach s hQ.left_mem⟩

end GraphMinor.GM16
