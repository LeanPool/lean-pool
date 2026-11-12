/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileTouching
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.P3161T2IncidentBoundary
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathVertexIncidentEdge
public import Mathlib.Data.List.Chain

-- [TABLET NODE: P4677T2TouchingWalk]

/-!
# P4677T2TouchingWalk

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4677T2TouchingWalk (T U : ProtoTile) (x y : GaussianInt)
    (h : TileTouching T U)
    (hx : x ∈ FootprintVertices T ∩ FootprintVertices U)
    (hy : y ∈ FootprintVertices T ∩ FootprintVertices U) :
    ∃ p : List GaussianInt,
      p.head? = some x ∧ p.getLast? = some y ∧
      (∀ z ∈ p, z ∈ FootprintVertices T ∩ FootprintVertices U) ∧
      ∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
        p = l₁ ++ a :: b :: l₂ →
        {a, b} ∈ FootprintEdges T ∩ FootprintEdges U := by
-- BODY
  classical
  have edge_raw (V : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges V) : e ∈ FootprintEdges V := by
    rcases he with ⟨z, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
    · rcases h with ⟨hz, _⟩ | ⟨_, hz⟩
      · exact ⟨z, hz, Or.inl rfl⟩
      · refine ⟨z - ⟨0, 1⟩, hz, Or.inr (Or.inr (Or.inr ?_))⟩
        congr 1 <;> simp [Zsqrtd.ext_iff]
    · rcases h with ⟨hz, _⟩ | ⟨_, hz⟩
      · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
      · refine ⟨z - 1, hz, Or.inr (Or.inr (Or.inl ?_))⟩
        congr 1 <;> simp []
  have edge_vertex (V : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ FootprintEdges V) (z : GaussianInt) (hz : z ∈ e) :
      z ∈ FootprintVertices V := by
    rcases he with ⟨c, hc, rfl | rfl | rfl | rfl⟩
    all_goals
      simp only [FootprintVertices, ite_eq_left (show V.cells.Nonempty from ⟨c, hc⟩),
        Set.mem_ofPred_eq]
      refine ⟨c, hc, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> simp
  have incident (V : ProtoTile) (z : GaussianInt) (hn : V.cells.Nonempty)
      (hz : z ∈ FootprintVertices V) :
      ∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ V.cells := by
    simp only [FootprintVertices, ite_eq_left hn, Set.mem_ofPred_eq] at hz
    rcases hz with ⟨c, hc, rfl | rfl | rfl | rfl⟩
    · exact ⟨0, by simpa [LatticeVertexIncidentCell] using hc⟩
    · exact ⟨1, by simpa [LatticeVertexIncidentCell] using hc⟩
    · exact ⟨3, by simpa [LatticeVertexIncidentCell] using hc⟩
    · exact ⟨2, by simpa [LatticeVertexIncidentCell, sub_eq_add_neg,
        add_assoc, add_comm, add_left_comm] using hc⟩
  rcases h with h | h | h
  · rcases h with ⟨hT, hU, hd, hp⟩
    let V := BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U
    let E := BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U
    have raw_boundary (z : GaussianInt)
        (hz : z ∈ FootprintVertices T ∩ FootprintVertices U) : z ∈ V := by
      obtain ⟨j, hj⟩ := incident T z hT hz.1
      obtain ⟨k, hk⟩ := incident U z hU hz.2
      exact ⟨P3161T2IncidentBoundary T z ⟨j, hj⟩
          ⟨k, fun h => Finset.disjoint_left.mp hd h hk⟩,
        P3161T2IncidentBoundary U z ⟨k, hk⟩
          ⟨j, fun h => Finset.disjoint_left.mp hd hj h⟩⟩
    have boundary_raw (z : GaussianInt) (hz : z ∈ V) :
        z ∈ FootprintVertices T ∩ FootprintVertices U := by
      obtain ⟨e, hze, he⟩ := SimpleGridPathVertexIncidentEdge V E hp z hz
      exact ⟨edge_vertex T e (edge_raw T e he.1) z hze,
        edge_vertex U e (edge_raw U e he.2) z hze⟩
    let R : GaussianInt → GaussianInt → Prop :=
      fun a b => a ∈ V ∧ b ∈ V ∧ {a, b} ∈ E
    have symmR (a b : GaussianInt) (h : R a b) : R b a :=
      ⟨h.2.1, h.1, by simpa [Finset.pair_comm] using h.2.2⟩
    have reverse {a b : GaussianInt} (h : Relation.ReflTransGen R a b) :
        Relation.ReflTransGen R b a := by
      induction h with
      | refl => exact .refl
      | @tail b c hbc hstep ih => exact ih.head (symmR _ _ hstep)
    have head_reach (a : GaussianInt) (l : List GaussianInt)
        (hc : List.IsChain R (a :: l)) :
        ∀ z ∈ a :: l, Relation.ReflTransGen R a z := by
      induction l generalizing a with
      | nil =>
        intro z hz
        have heq : z = a := by simpa using hz
        subst z
        exact .refl
      | cons b l ih =>
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact .refl
        · exact (Relation.ReflTransGen.single (List.isChain_cons_cons.mp hc).1).trans
            (ih b (List.isChain_cons_cons.mp hc).2 z hz)
    have hxV := raw_boundary x hx
    have hyV := raw_boundary y hy
    rcases hp with ⟨q, hnodup, hlen, hv, hstep, he⟩
    have qmem (z : GaussianInt) (hz : z ∈ q) : z ∈ V := by
      change z ∈ BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U
      rw [hv]
      simpa using hz
    have chain : List.IsChain R q := by
      apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
      intro a b l₁ l₂ hab
      refine ⟨qmem a (by simp [hab]), qmem b (by simp [hab]), ?_⟩
      exact (he _).mpr ⟨a, b, l₁, l₂, hab, rfl⟩
    have hxq : x ∈ q := by
      have hh : x ∈ (q.toFinset : Set GaussianInt) := hv ▸ hxV
      simpa using hh
    have hyq : y ∈ q := by
      have hh : y ∈ (q.toFinset : Set GaussianInt) := hv ▸ hyV
      simpa using hh
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil
      (show q ≠ [] by intro h; simp [h] at hlen)
    have route := (reverse (head_reach a l chain x hxq)).trans
      (head_reach a l chain y hyq)
    obtain ⟨p, hc, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen route
    refine ⟨x :: p, rfl, ?_, ?_, ?_⟩
    · rw [List.getLast?_eq_some_getLast (List.cons_ne_nil x p), hlast]
    · have inside : ∀ z ∈ x :: p, z ∈ V :=
        hc.induction (fun z => z ∈ V) (x :: p)
          (fun {_ _} h _ => h.2.1) (fun _ => hxV)
      intro z hz
      exact boundary_raw z (inside z hz)
    · intro a b l₁ l₂ hab
      have hed := (List.isChain_iff_forall_rel_of_append_cons_cons.mp hc hab).2.2
      exact ⟨edge_raw T _ hed.1, edge_raw U _ hed.2⟩
  · have heq : x = y := by
      have hx' : x = T.anchor := by simpa [FootprintVertices, h.1] using hx.1
      have hy' : y = T.anchor := by simpa [FootprintVertices, h.1] using hy.1
      exact hx'.trans hy'.symm
    subst y
    refine ⟨[x], rfl, rfl, ?_, ?_⟩
    · intro z hz
      simpa only [List.mem_singleton.mp hz] using hx
    · intro a b l₁ l₂ h
      have hh := congrArg List.length h
      simp at hh
      omega
  · have heq : x = y := by
      have hx' : x = U.anchor := by simpa [FootprintVertices, h.1] using hx.2
      have hy' : y = U.anchor := by simpa [FootprintVertices, h.1] using hy.2
      exact hx'.trans hy'.symm
    subst y
    refine ⟨[x], rfl, rfl, ?_, ?_⟩
    · intro z hz
      simpa only [List.mem_singleton.mp hz] using hx
    · intro a b l₁ l₂ h
      have hh := congrArg List.length h
      simp at hh
      omega

end ApollonianSuperharmonic

end
