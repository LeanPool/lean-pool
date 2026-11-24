/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73WalkSubstitution
import LeanPool.GraphMinor.GM12.Section73WalkPointSets

/-!
# Edge containment in a substituted walk

The circuit comparison in XII (7.3), Claim (1), page 262,
uses the old edges of each replaced spoke inside the lifted walk.
The substitution induction records these edges as well as the
length and point sets. Any set of old edges retained by every
replacement of a new edge is retained by the whole lifted walk.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

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
      · have hedge : (if x = v ∨ y = v then 2 else 1) =
            1 + I x + I y := by
          dsimp only [I]
          have hxy := hloopless e x y h
          by_cases hx : x = v <;> by_cases hy : y = v
          · exact (hxy (hx.trans hy.symm)).elim
          · simp only [hx, hy, true_or, ite_true, ite_false]
          · simp only [hx, hy, or_true, ite_true, ite_false]
          · simp only [hx, hy, false_or, ite_false]
        have hPlen : P.length = 1 + I x + I y := hP.trans hedge
        rw [GraphWalk.length_append, GraphWalk.length_cons, walkVertexCount]
        change P.length + Q'.length + I x = Q.length + 1 + 2 * (I x + walkVertexCount v Q) + I z
        omega
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

end GraphMinor.GM12
