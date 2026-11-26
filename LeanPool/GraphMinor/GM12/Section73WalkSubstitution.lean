/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Walks
import Mathlib.Data.List.Count
import LeanPool.GraphMinor.GM12.Section73WalkPointSets

/-!
# The length of a walk after replacing spokes

In XII (7.3), page 261, replace each spoke at the merged hub by a
two-edge path and every other edge by one edge. Each occurrence of
the hub in a closed walk has one arriving and one departing edge.
The replacement therefore adds twice the number of occurrences.
Count occurrences by departure positions, excluding the repeated
last vertex of a closed walk.
-/

public section

namespace GraphMinor.GM12

open Set Graph Surface GM11

open Classical in
/-- Count the occurrences of a vertex before the final position of
a walk. On closed walks this is the occurrence count used in XII
(7.3), page 261. -/
@[expose] noncomputable def walkVertexCount
    {α β : Type*} {G : Graph α β} (v : α) {a b : α} : GraphWalk G a b → ℕ
  | .nil _ => 0
  | .cons (u := x) _ W => (if x = v then 1 else 0) + walkVertexCount v W

open Classical in
/-- The departure count is the count in the support list with its
last position removed. -/
theorem walkVertexCount_eq_count_dropLast
    {α β : Type*} {G : Graph α β} (v : α) {a b : α} (W : GraphWalk G a b) :
    walkVertexCount v W = (W.support.dropLast).count v := by
  induction W with
  | nil h => rfl
  | @cons x y z e h W ih =>
    rw [walkVertexCount, GraphWalk.support_cons, List.dropLast_cons_of_ne_nil W.support_ne_nil,
      List.count_cons, ← ih]
    by_cases hx : x = v
    · simp [hx, Nat.add_comm]
    · simp [hx]

open Classical in
private theorem replacement_edge_length {α : Type*} {x y v : α} (hxy : x ≠ y) :
    (if x = v ∨ y = v then 2 else 1) =
      1 + (if x = v then 1 else 0) + (if y = v then 1 else 0) := by
  by_cases hx : x = v <;> by_cases hy : y = v
  · exact False.elim (hxy (hx.trans hy.symm))
  · simp only [hx, hy, true_or, ite_true, ite_false]
  · simp only [hx, hy, or_true, ite_true, ite_false]
  · simp only [hx, hy, false_or, ite_false]

open Classical in
/-- The length identity for extending an already substituted walk by its first edge. -/
theorem replacement_append_length {α β γ : Type*}
    {G : Graph α β} {G' : Graph α γ} {v x y z : α} {e : β}
    {h : G.IsLink e x y} {Q : GraphWalk G y z}
    {P : GraphWalk G' x y} {Q' : GraphWalk G' y z} (hxy : x ≠ y)
    (hP : P.length = if x = v ∨ y = v then 2 else 1)
    (hQ : Q'.length + (if y = v then 1 else 0) =
      Q.length + 2 * walkVertexCount v Q + (if z = v then 1 else 0)) :
    (P.append Q').length + (if x = v then 1 else 0) =
      (GraphWalk.cons h Q).length + 2 * walkVertexCount v (GraphWalk.cons h Q) +
        (if z = v then 1 else 0) := by
  have hlength := hP.trans (replacement_edge_length hxy)
  rw [GraphWalk.length_append, GraphWalk.length_cons, walkVertexCount]
  omega

open Classical in
/-- Replacing each edge at a vertex by two edges adds twice the
number of vertex occurrences to a closed walk's length. This is the
length identity for the lifted walk in XII (7.3), page 261. -/
theorem exists_closed_walk_substitution
    {α β γ : Type*} {G : Graph α β} {G' : Graph α γ} {v : α}
    (hV : ∀ x ∈ V(G), x ∈ V(G'))
    (hloopless : ∀ e x y, G.IsLink e x y → x ≠ y)
    (hpaths : ∀ e x y, G.IsLink e x y →
      ∃ P : GraphWalk G' x y, P.length = if x = v ∨ y = v then 2 else 1)
    {a : α} (W : GraphWalk G a a) :
    ∃ W' : GraphWalk G' a a, W'.length = W.length + 2 * walkVertexCount v W := by
  let I : α → ℕ := fun x => if x = v then 1 else 0
  have hlift : ∀ {x y : α} (R : GraphWalk G x y), ∃ R' : GraphWalk G' x y,
      R'.length + I x = R.length + 2 * walkVertexCount v R + I y := by
    intro x y R
    induction R with
    | nil h => exact ⟨.nil (hV _ h), by rfl⟩
    | @cons x y z e h R ih =>
      obtain ⟨P, hP⟩ := hpaths e x y h
      obtain ⟨R', hR'⟩ := ih
      refine ⟨P.append R', ?_⟩
      exact replacement_append_length (h := h) (hloopless e x y h) hP hR'
  obtain ⟨W', hW'⟩ := hlift W
  exact ⟨W', Nat.add_right_cancel hW'⟩

open Classical in
/-- The lifted walk contains the specified old edges of every
new edge that it replaces. This records the edge containment
needed for the old circuit in XII (7.3), Claim (1), page 262. -/
theorem exists_closed_walk_substitution_with_edge_sets
    {S : Type*} [TopologicalSpace S] [T2Space S] {J K : Drawing S} {v : S} {R : Set S}
    (B : Set S → Set (Set S))
    (f : S → S) (hfixV : ∀ x ∈ J.V, f x = x)
    (hV : J.V ⊆ K.V)
    (hloopless : ∀ e x y, J.toGraph.IsLink e x y → x ≠ y)
    (hpaths : ∀ e x y, J.toGraph.IsLink e x y →
      ∃ P : GraphWalk K.toGraph x y,
        P.length = (if x = v ∨ y = v then 2 else 1) ∧
        f '' (walkDrawing K P).U = closure e ∧
        (walkDrawing K P).U \ R = closure e \ R ∧
        ∀ g ∈ B e, g ∈ P.edges)
    {a : S} (W : GraphWalk J.toGraph a a) :
    ∃ W' : GraphWalk K.toGraph a a,
      W'.length = W.length + 2 * walkVertexCount v W ∧
      f '' (walkDrawing K W').U = (walkDrawing J W).U ∧
      (walkDrawing K W').U \ R = (walkDrawing J W).U \ R ∧
      ∀ e ∈ W.edges, ∀ g ∈ B e, g ∈ W'.edges := by
  let I : S → ℕ := fun x => if x = v then 1 else 0
  have hlift : ∀ {x y : S} (Q : GraphWalk J.toGraph x y), ∃ Q' : GraphWalk K.toGraph x y,
      (Q'.length + I x = Q.length + 2 * walkVertexCount v Q + I y) ∧
      f '' (walkDrawing K Q').U = (walkDrawing J Q).U ∧
      (walkDrawing K Q').U \ R = (walkDrawing J Q).U \ R ∧
      ∀ e ∈ Q.edges, ∀ g ∈ B e, g ∈ Q'.edges := by
    intro x y Q
    induction Q with
    | nil h =>
      refine ⟨.nil (hV h), by rfl, ?_, ?_, ?_⟩
      · calc
          f '' (walkDrawing K (.nil (hV h))).U = f '' {_} :=
            congrArg (image f) (walkDrawing_nil_points (K := K) (hV h))
          _ = {_} := by rw [image_singleton, hfixV _ h]
          _ = (walkDrawing J (.nil h)).U := (walkDrawing_nil_points (K := J) h).symm
      · exact congrArg (fun A : Set S => A \ R)
          ((walkDrawing_nil_points (K := K) (hV h)).trans (walkDrawing_nil_points (K := J) h).symm)
      · intro e he
        exact (List.not_mem_nil he).elim
    | @cons x y z e h Q ih =>
      obtain ⟨P, hP, hPimage, hPpts, hPB⟩ := hpaths e x y h
      obtain ⟨Q', hQ', hQimage, hQpts, hQB⟩ := ih
      refine ⟨P.append Q', ?_, ?_, ?_, ?_⟩
      · exact replacement_append_length (h := h) (hloopless e x y h) hP hQ'
      · rw [walkDrawing_append_points, image_union, hPimage, hQimage, walkDrawing_cons_points]
      · rw [walkDrawing_append_points, union_sdiff_distrib, hPpts, hQpts,
          ← union_sdiff_distrib, walkDrawing_cons_points]
      · intro d hd g hg
        rw [GraphWalk.edges_append]
        rcases List.mem_cons.mp hd with rfl | hd
        · exact List.mem_append_left _ (hPB g hg)
        · exact List.mem_append_right _ (hQB d hd g hg)
  obtain ⟨W', hWlen, hWimage, hWpts, hWB⟩ := hlift W
  exact ⟨W', Nat.add_right_cancel hWlen, hWimage, hWpts, hWB⟩

open Classical in
/-- The walk substitution also preserves the point set outside a
specified region when every edge replacement does so. This is the
point-set part of the lifted walk in XII (7.3), page 261. -/
theorem exists_closed_walk_substitution_with_points
    {S : Type*} [TopologicalSpace S] [T2Space S] {J K : Drawing S} {v : S} {R : Set S}
    (f : S → S) (hfixV : ∀ x ∈ J.V, f x = x)
    (hV : J.V ⊆ K.V)
    (hloopless : ∀ e x y, J.toGraph.IsLink e x y → x ≠ y)
    (hpaths : ∀ e x y, J.toGraph.IsLink e x y →
      ∃ P : GraphWalk K.toGraph x y,
        P.length = (if x = v ∨ y = v then 2 else 1) ∧
        f '' (walkDrawing K P).U = closure e ∧
        (walkDrawing K P).U \ R = closure e \ R)
    {a : S} (W : GraphWalk J.toGraph a a) :
    ∃ W' : GraphWalk K.toGraph a a,
      W'.length = W.length + 2 * walkVertexCount v W ∧
      f '' (walkDrawing K W').U = (walkDrawing J W).U ∧
      (walkDrawing K W').U \ R = (walkDrawing J W).U \ R := by
  have hpaths' : ∀ e x y, J.toGraph.IsLink e x y →
      ∃ P : GraphWalk K.toGraph x y,
        P.length = (if x = v ∨ y = v then 2 else 1) ∧
        f '' (walkDrawing K P).U = closure e ∧
        (walkDrawing K P).U \ R = closure e \ R ∧
        ∀ g ∈ (∅ : Set (Set S)), g ∈ P.edges := by
    intro e x y h
    obtain ⟨P, hlen, himage, hpoints⟩ := hpaths e x y h
    exact ⟨P, hlen, himage, hpoints, fun _ hg => hg.elim⟩
  obtain ⟨W', hlen, himage, hpoints, -⟩ :=
    exists_closed_walk_substitution_with_edge_sets (fun _ => ∅)
      f hfixV hV hloopless hpaths' W
  exact ⟨W', hlen, himage, hpoints⟩

end GraphMinor.GM12
