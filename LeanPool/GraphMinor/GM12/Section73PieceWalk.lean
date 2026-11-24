/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73CircuitJoin
public import LeanPool.GraphMinor.GM11.Section92

/-!
# Normalizing the walks of XI (9.2)

The proof of XI (9.2), used in XII (7.3), page 262, constructs
pieces bounded by a circuit, by one edge traversed twice, or by
one vertex. Normalize their walks accordingly. Each normalized
walk visits every ambient vertex at most once, and its length
is no greater than any closed walk with the same drawing. This
keeps the perimeter budget supplied by XI (9.2) when a different
attachment vertex is chosen.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

private theorem two_le_closed_walk_length_of_vertices
    {α β : Type*} {G : Graph α β} {a b c : α} (W : GraphWalk G c c)
    (ha : a ∈ W.support) (hb : b ∈ W.support) (hab : a ≠ b) : 2 ≤ W.length := by
  cases W with
  | nil _ =>
    have ha' : a = c := List.mem_singleton.mp ha
    have hb' : b = c := List.mem_singleton.mp hb
    exact (hab (ha'.trans hb'.symm)).elim
  | cons _ R =>
    cases R with
    | nil _ =>
      have ha' : a = c := by simpa [GraphWalk.support] using ha
      have hb' : b = c := by simpa [GraphWalk.support] using hb
      exact (hab (ha'.trans hb'.symm)).elim
    | cons _ R => simp only [GraphWalk.length_cons]; omega

/-- Normalize the boundary walk of a piece constructed in the
proof of XI (9.2), at any vertex of the piece. The three defining
shapes give a circuit walk, a two-edge return walk, or a nil walk. -/
theorem exists_piece_walk_with_visit_bound
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {K G : Drawing S} {ins : Drawing S → Set S} {k : ℕ} {Y A : Set S}
    (hP : IsPiece K ins k Y A G) {p z : S} (hp : p ∈ G.V)
    (Z : GraphWalk K.toGraph z z) (hZ : walkDrawing K Z = G) :
    ∃ W : GraphWalk K.toGraph p p, walkDrawing K W = G ∧
      W.length ≤ Z.length ∧ ∀ v, walkVertexCount v W ≤ 1 := by
  have hGK : G.IsSubdrawing K := hP.sub.trans interSet_isSub
  rcases hP.kind with ⟨hC, _⟩ | ⟨e, u, v, huv, he, hcap, hGV, hGE, _, _⟩ |
      ⟨v, hGV, hGE, _, _⟩
  · obtain ⟨W, hW, hlen, hcount⟩ := exists_circuit_walk_at_with_visit_bound hC hGK hp
    refine ⟨W, hW, ?_, hcount⟩
    rw [hlen]
    change G.E.ncard ≤ Z.edges.length
    rw [← hZ, walkDrawing_E]
    exact ncard_mem_list_le Z.edges
  · have huCap : u ∈ closure e ∩ K.V := hcap.symm ▸ (Or.inl rfl : u ∈ ({u, v} : Set S))
    have hvCap : v ∈ closure e ∩ K.V := hcap.symm ▸ (Or.inr rfl : v ∈ ({u, v} : Set S))
    have hu : u ∈ K.V := huCap.2
    have hv : v ∈ K.V := hvCap.2
    have hl : K.toGraph.IsLink e u v := ⟨he, hu, hv, hcap⟩
    have hZlen : 2 ≤ Z.length := by
      have huZ : u ∈ Z.support := by
        have hh : u ∈ (walkDrawing K Z).V := hZ.symm ▸ (hGV.symm ▸ (Or.inl rfl : u ∈
          ({u, v} : Set S)))
        rwa [walkDrawing_V] at hh
      have hvZ : v ∈ Z.support := by
        have hh : v ∈ (walkDrawing K Z).V := hZ.symm ▸ (hGV.symm ▸ (Or.inr rfl : v ∈
          ({u, v} : Set S)))
        rwa [walkDrawing_V] at hh
      exact two_le_closed_walk_length_of_vertices Z huZ hvZ huv
    have hmake : ∀ {a b : S}, a ≠ b → K.toGraph.IsLink e a b → G.V = {a, b} →
        ∃ W : GraphWalk K.toGraph a a, walkDrawing K W = G ∧
          W.length ≤ Z.length ∧ ∀ w, walkVertexCount w W ≤ 1 := by
      intro a b hab hl hV
      let W : GraphWalk K.toGraph a a := .cons hl (.cons hl.symm (.nil hl.2.1))
      refine ⟨W, ?_, hZlen, ?_⟩
      · apply Drawing.ext_of_V_E
        · rw [walkDrawing_V, hV]
          ext w
          simp only [W, GraphWalk.support, List.mem_cons, List.not_mem_nil, or_false, mem_ofPred_eq,
            mem_insert_iff, mem_singleton_iff]
          tauto
        · rw [walkDrawing_E, hGE]
          ext f
          simp [W, GraphWalk.edges]
      · intro w
        classical
        change (if a = w then 1 else 0) + ((if b = w then 1 else 0) + 0) ≤ 1
        by_cases ha : a = w
        · have hb : b ≠ w := fun hb => hab (ha.trans hb.symm)
          simp [ha, hb]
        · by_cases hb : b = w <;> simp [ha, hb]
    rw [hGV] at hp
    rcases hp with hp | hp
    · subst p
      exact hmake huv hl hGV
    · have hpv : p = v := hp
      subst p
      exact hmake huv.symm hl.symm (hGV.trans (pair_comm u v))
  · have hpv : p = v := by rw [hGV] at hp; exact hp
    subst p
    let W : GraphWalk K.toGraph v v := .nil (hGK.1 hp)
    refine ⟨W, ?_, Nat.zero_le _, ?_⟩
    · apply Drawing.ext_of_V_E
      · rw [walkDrawing_V, hGV]
        ext x
        simp [W, GraphWalk.support]
      · rw [walkDrawing_E, hGE]
        ext e
        simp [W, GraphWalk.edges]
    · intro w
      exact Nat.zero_le 1

end GraphMinor.GM12
