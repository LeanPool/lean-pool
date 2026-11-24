/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Minor.Model
public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM09.Basic

/-!
# Three paths from one branch vertex

For the subcubic-minor step of XVI (4.2), page 54, a branch set has
at most three attachment vertices. Join two by a path. Join the third
to that path, stopping at its first meeting, and split the first path
there. The three resulting arms meet only at that vertex. Attachment
vertices may coincide, in which case some arms have one vertex.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09
universe u v

/-- A connected graph has a path between each pair of its vertices. -/
theorem GraphConnected.exists_path {α : Type u} {β : Type v} {G : Graph α β}
    (hG : GraphConnected G) {a b : α} (ha : a ∈ V(G)) (hb : b ∈ V(G)) :
    ∃ P : Graph α β, IsGraphPathWithEnds G P a b := by
  have hwalk : ∀ {x y : α}, Relation.ReflTransGen G.Adj x y → x ∈ V(G) →
      Nonempty (GraphWalk G x y) := by
    intro x y h
    induction h with
    | refl => intro hx; exact ⟨.nil hx⟩
    | @tail z w _ hzw ih =>
      intro hx
      obtain ⟨W⟩ := ih hx
      obtain ⟨e, hlink⟩ := hzw
      exact ⟨W.append (.cons hlink (.nil hlink.right_mem))⟩
  obtain ⟨W⟩ := hwalk (hG.2 a ha b hb) ha
  obtain ⟨P, hP, _, _⟩ := exists_isGraphPathWithEnds_of_walk W
  exact ⟨P, hP⟩

/-- The branch-set construction in the subcubic-minor step of XVI
(4.2), page 54: three attachment vertices can be joined to one vertex
by arms that meet pairwise only at that vertex. -/
theorem exists_connected_tripod {α : Type u} {β : Type v} {G : Graph α β}
    (hG : GraphConnected G) {a b c : α}
    (ha : a ∈ V(G)) (hb : b ∈ V(G)) (hc : c ∈ V(G)) :
    ∃ (m : α) (P₁ P₂ P₃ : Graph α β), m ∈ V(G) ∧
      IsGraphPathWithEnds G P₁ m a ∧ IsGraphPathWithEnds G P₂ m b ∧
      IsGraphPathWithEnds G P₃ m c ∧
      V(P₁) ∩ V(P₂) = {m} ∧ V(P₁) ∩ V(P₃) = {m} ∧ V(P₂) ∩ V(P₃) = {m} := by
  obtain ⟨P, hP⟩ := GraphConnected.exists_path hG ha hb
  obtain ⟨Q, hQ⟩ := GraphConnected.exists_path hG hc ha
  obtain ⟨x, hx, m, hm, R, _, hR⟩ := hQ.exists_isFromToPathWithEnds
    (show c ∈ ({c} : Set α) from mem_singleton _) hP.left_mem
  have hxc : x = c := hx
  subst x
  obtain ⟨P₁, P₂, hP₁, hP₂, hPath₁, hPath₂, _, hInter, _⟩ := hP.exists_split_at hm
  have hRpath : IsGraphPathWithEnds G R c m := hR.1
  have hMeet : V(R) ∩ V(P) = {m} := hR.2.2
  have hIntersect (L : Graph α β) (hL : L ≤ P) (hmL : m ∈ V(L)) :
      V(L) ∩ V(R) = {m} := by
    apply Subset.antisymm
    · rintro z ⟨hzL, hzR⟩
      exact hMeet ▸ ⟨hzR, hL.vertexSet_mono hzL⟩
    · rintro z rfl
      exact ⟨hmL, hRpath.right_mem⟩
  refine ⟨m, P₁, P₂, R, hP.le.vertexSet_mono hm,
    (hPath₁.mono hP.le).symm, hPath₂.mono hP.le, hRpath.symm, hInter, ?_, ?_⟩
  · exact hIntersect P₁ hP₁ hPath₁.right_mem
  · exact hIntersect P₂ hP₂ hPath₂.left_mem

end GraphMinor.GM16
