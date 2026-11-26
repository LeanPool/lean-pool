/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM16.Section3
import LeanPool.GraphMinor.Menger.Basic
import LeanPool.GraphMinor.GM10.Defs
import LeanPool.GraphMinor.GM11.Walks

/-!
# The path-separator alternative used in XVI (8.1)

For Claim (5), apply Menger to two boundary sets. Trim each of the
disjoint paths at its first and last visits to those sets. If the
packing does not exist, the vertices of the resulting separation
meet every path between the sets.
-/

public section
namespace GraphMinor.GM16
open Set Graph SimpleGraph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM10
universe u v

private theorem skeleton_walk_meets_separation {α : Type u} {β : Type v}
    {G A B : Hypergraph α β} (hsep : G.IsSeparation A B)
    {x y : α} (w : G.skeleton.Walk x y) (hx : x ∈ A.vertexSet) (hy : y ∈ B.vertexSet) :
    ∃ z ∈ w.support, z ∈ A.vertexSet ∩ B.vertexSet := by
  induction w with
  | nil => exact ⟨_, Walk.start_mem_support _, hx, hy⟩
  | @cons x x' y hadj rest ih =>
    by_cases hx' : x' ∈ A.vertexSet
    · obtain ⟨z, hz, hzAB⟩ := ih hx' hy
      exact ⟨z, List.mem_cons_of_mem _ hz, hzAB⟩
    · obtain ⟨_, e, hex, hex'⟩ := id hadj
      have he : e ∈ (A ∪ B).edgeSet := by
        rw [hsep.union_eq]
        exact G.edge_mem_of_inc hex
      rcases he with heA | heB
      · have hinc : A.Inc e x' := by
          change x' ∈ A.ends e
          rw [← hsep.left_le.ends_eq e heA]
          exact hex'
        exact False.elim (hx' (A.vertex_mem_of_inc hinc))
      · have hinc : B.Inc e x := by
          change x ∈ B.ends e
          rw [← hsep.right_le.ends_eq e heB]
          exact hex
        exact ⟨x, Walk.start_mem_support _, hx, B.vertex_mem_of_inc hinc⟩

/-- Menger's theorem in the path form used by XVI (8.1), Claim (5),
page 72. The separator has size strictly below the requested packing. -/
theorem disjoint_fromToPaths_or_separator {α : Type u} {β : Type v}
    (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (X Y : Set α) (hX : X ⊆ V(G)) (hY : Y ⊆ V(G)) (k : ℕ) :
    (∃ P : Fin k → Graph α β,
      (∀ i, IsFromToPath G (P i) X Y) ∧ Pairwise (fun i j => Disjoint V(P i) V(P j))) ∨
    (∃ Z ⊆ V(G), Z.ncard < k ∧
      ∀ P x y, IsGraphPathWithEnds G P x y → x ∈ X → y ∈ Y → (V(P) ∩ Z).Nonempty) := by
  classical
  let GH := Hypergraph.ofGraph G hV hE
  by_cases hPack : HasDisjointPaths GH.skeleton X Y k
  · obtain ⟨p, hp⟩ := hPack
    have hex : ∀ i : Fin k, ∃ Q : Graph α β, IsFromToPath G Q X Y ∧
        V(Q) ⊆ {z | z ∈ (p i).walk.support} := by
      intro i
      obtain ⟨R, hR, hRV⟩ := exists_isGraphPathWithEnds_of_skeleton_isPath hV hE
        (hX (p i).first_mem) (p i).walk (p i).isPath
      obtain ⟨x, hx, y, hy, Q, hQR, hQ⟩ := hR.exists_isFromToPathWithEnds (p i).first_mem
        (p i).last_mem
      exact ⟨Q, ⟨x, y, hQ⟩, hQR.vertexSet_mono.trans (le_of_eq hRV)⟩
    choose Q hQ hQV using hex
    exact Or.inl ⟨Q, hQ, fun i j hij => (hp hij).mono (hQV i) (hQV j)⟩
  · have hnot : ¬ ∀ A B : Hypergraph α β, GH.IsSeparation A B → X ⊆ A.vertexSet →
        Y ⊆ B.vertexSet → k ≤ Hypergraph.separationOrder A B :=
      fun hall => hPack ((GraphMinor.menger GH X Y hX hY k).mp hall)
    push Not at hnot
    obtain ⟨A, B, hsep, hXA, hYB, hlt⟩ := hnot
    refine Or.inr ⟨A.vertexSet ∩ B.vertexSet,
      inter_subset_left.trans hsep.left_le.1, hlt, ?_⟩
    intro P x y hP hx hy
    obtain ⟨W, _, hPV, _⟩ := hP.2
    have hConvert : ∀ {a b : α} (W : GraphWalk P a b),
        ∃ w : GH.skeleton.Walk a b, ∀ z ∈ w.support, z ∈ W.support := by
      intro a b W
      induction W with
      | @nil a ha => exact ⟨.nil, fun _ h => h⟩
      | @cons a b c e hl rest ih =>
        obtain ⟨w, hw⟩ := ih
        by_cases hab : a = b
        · subst b
          exact ⟨w, fun z hz => List.mem_cons_of_mem _ (hw z hz)⟩
        · have hlG := hP.1.isLink_mono hl
          have hadj : GH.skeleton.Adj a b := ⟨hab, e, ⟨b, hlG⟩, ⟨a, hlG.symm⟩⟩
          refine ⟨.cons hadj w, ?_⟩
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hw z hz)
    obtain ⟨w, hw⟩ := hConvert W
    obtain ⟨z, hzw, hzAB⟩ := skeleton_walk_meets_separation hsep w (hXA hx) (hYB hy)
    exact ⟨z, hPV.symm ▸ hw z hzw, hzAB⟩

end GraphMinor.GM16
