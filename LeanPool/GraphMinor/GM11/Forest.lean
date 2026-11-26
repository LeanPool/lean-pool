/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Regions
public import LeanPool.GraphMinor.GM11.Cited

/-!
# Drawings without circuits: graph theory

Graph Minors XI uses in the proof of (4.4) that a drawing without circuits has only one region. This
file has the combinatorial part: a drawing with an edge and no circuit has a leaf (`exists_leaf`),
found at the end of a longest path. It also has `isPreconnected_sdiff_of_local`, the connectedness
principle used to remove a piece of a drawing from a connected open set, and the basic facts on
`deleteEdge`.
-/

public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- To see that `G - T` is connected, for an open connected set `G` and a set `T` closed in `G`, it
suffices that every component of `G - T` with a point of `T` in its closure contains a fixed set. -/
theorem isPreconnected_sdiff_of_local [LocallyConnectedSpace S] {G T : Set S} (_hG : IsOpen G)
    (hGc : IsPreconnected G) (hT : IsClosed (Gᶜ ∪ T)) (hTG : (G ∩ T).Nonempty) {a : S}
    (_ha : a ∈ G \ T)
    (hloc : ∀ x ∈ G \ T, ((G ∩ T) ∩ closure (connectedComponentIn (G \ T) x)).Nonempty →
      a ∈ connectedComponentIn (G \ T) x) : IsPreconnected (G \ T) := by
  have hopen : IsOpen (G \ T) := by
    have : G \ T = (Gᶜ ∪ T)ᶜ := by
      ext y
      simp
    rw [this]
    exact hT.isOpen_compl
  have hcomp : ∀ x ∈ G \ T, a ∈ connectedComponentIn (G \ T) x := by
    intro x hx
    refine hloc x hx ?_
    by_contra hcon
    set C := connectedComponentIn (G \ T) x with hC
    have hCo : IsOpen C := hopen.connectedComponentIn
    have hxC : x ∈ C := mem_connectedComponentIn hx
    obtain ⟨t, ht⟩ := hTG
    have htC : t ∉ closure C := fun h => hcon ⟨t, ht, h⟩
    have hcov : G ⊆ C ∪ (closure C)ᶜ := by
      intro y hy
      by_cases hyc : y ∈ closure C
      · refine Or.inl ?_
        by_cases hyT : y ∈ T
        · exact absurd ⟨y, ⟨hy, hyT⟩, hyc⟩ hcon
        have hy' : y ∈ G \ T := ⟨hy, hyT⟩
        have hop : IsOpen (connectedComponentIn (G \ T) y) := hopen.connectedComponentIn
        obtain ⟨z, hz, hzC⟩ := mem_closure_iff.mp hyc _ hop (mem_connectedComponentIn hy')
        rw [hC, connectedComponentIn_eq hzC, ← connectedComponentIn_eq hz]
        exact mem_connectedComponentIn hy'
      · exact Or.inr hyc
    obtain ⟨y, -, hy₁, hy₂⟩ := hGc C (closure C)ᶜ hCo isClosed_closure.isOpen_compl hcov
      ⟨x, (connectedComponentIn_subset _ _ hxC).1, hxC⟩ ⟨t, ht.1, htC⟩
    exact hy₂ (subset_closure hy₁)
  have hEq : G \ T = connectedComponentIn (G \ T) a := by
    refine subset_antisymm (fun x hx => ?_) (connectedComponentIn_subset _ _)
    rw [← connectedComponentIn_eq (hcomp x hx)]
    exact mem_connectedComponentIn hx
  rw [hEq]
  exact isPreconnected_connectedComponentIn

variable [T2Space S]

/-- The drawing `Γ` with an edge deleted has the point set `U(Γ) - e`. -/
theorem deleteEdge_U (Γ : Drawing S) {e : Set S} (he : e ∈ Γ.E) :
    (Γ.deleteEdge e).U = Γ.U \ e := by
  have hV : (Γ.deleteEdge e).V = Γ.V := by
    apply subset_antisymm (Drawing.span_isSubdrawing Γ _ _).1
    intro x hx
    exact Or.inl ⟨hx, hx⟩
  have hE : (Γ.deleteEdge e).E = Γ.E \ {e} := by
    rw [Drawing.deleteEdge, Γ.span_E]
    ext f
    exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩
  rw [Drawing.U_eq, hV, hE]
  ext x
  constructor
  · rintro (hx | hx)
    · exact ⟨Γ.V_subset_U hx, fun hxe => (he.2.1 hxe).2 hx⟩
    · obtain ⟨f, ⟨hf, hfe⟩, hxf⟩ := mem_iUnion₂.mp hx
      refine ⟨Γ.closure_subset_U hf hxf, fun hxe => ?_⟩
      have hxV : x ∉ Γ.V := (he.2.1 hxe).2
      have hxf' : x ∈ f := by rw [← Γ.closure_diff_V hf]; exact ⟨hxf, hxV⟩
      exact hfe (Γ.edge_eq_of_mem hf he hxf' hxe)
  · rintro ⟨hx, hxe⟩
    rw [Γ.U_eq] at hx
    rcases hx with hx | hx
    · exact Or.inl hx
    obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
    by_cases hfe : f = e
    · subst hfe
      refine Or.inl ?_
      by_contra hxV
      exact hxe (by rw [← Γ.closure_diff_V hf]; exact ⟨hxf, hxV⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hfe⟩, hxf⟩)

theorem deleteEdge_E (Γ : Drawing S) (e : Set S) : (Γ.deleteEdge e).E = Γ.E \ {e} := by
  rw [Drawing.deleteEdge, Γ.span_E]
  ext f
  exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩

theorem deleteEdge_isSubdrawing (Γ : Drawing S) (e : Set S) : (Γ.deleteEdge e).IsSubdrawing Γ :=
  Drawing.span_isSubdrawing Γ _ _

/-- A drawing without circuits has no loops: every edge has two distinct ends. -/
theorem exists_ends_of_noCircuit {Γ : Drawing S}
    (hno : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ → False) {e : Set S} (he : e ∈ Γ.E) :
    ∃ u v : S, u ≠ v ∧ closure e ∩ Γ.V = {u, v} ∧ IsLineWithEnds (closure e) u v := by
  rcases Γ.edge_cond e he with ⟨u, v, huv, hcap, hL⟩ | ⟨u, hcap, -⟩
  · exact ⟨u, v, huv, hcap, hL⟩
  · exfalso
    have hu : u ∈ Γ.V := by
      have : u ∈ closure e ∩ Γ.V := by rw [hcap]; simp
      exact this.2
    have hl : Γ.toGraph.IsLink e u u := ⟨he, hu, hu, by simpa using hcap⟩
    let W : GraphWalk Γ.toGraph u u := .cons hl (.nil hu)
    have hsub := walkDrawing_isSubdrawing Γ W
    obtain ⟨W', hs, hed⟩ := hsub.exists_walk_down W
      (fun x hx => by rw [walkDrawing_V]; exact hx) (fun f hf => by rw [walkDrawing_E]; exact hf)
    refine hno _ ⟨u, W', ⟨?_, ?_⟩, ?_, ?_, ?_⟩ hsub
    · rw [hs]
      exact List.nodup_singleton u
    · rw [hed]
      exact List.nodup_singleton e
    · have : W'.edges ≠ [] := by
        rw [hed]
        simp [W]
      exact List.length_pos_iff.mpr this
    · rw [walkDrawing_V, hs]
    · rw [walkDrawing_E, hed]

omit [T2Space S] in
theorem length_support {α β : Type*} {G : Graph α β} {a b : α} (W : GraphWalk G a b) :
    W.support.length = W.length + 1 := by
  induction W with
  | nil _ => simp
  | cons h r ih => simp [ih]

omit [T2Space S] in
theorem IsLineWithEnds.symm {L : Set S} {u v : S} (h : IsLineWithEnds L u v) :
    IsLineWithEnds L v u := by
  obtain ⟨f, h₀, h₁⟩ := h
  refine ⟨unitInterval.symmHomeomorph.trans f, ?_, ?_⟩
  · simpa using h₁
  · simpa using h₀

/-- A drawing with an edge and without circuits has a leaf: an edge `e` with ends `u ≠ v`, such
that no other edge has `v` as an end. We take `v` to be the start of a longest path. -/
theorem exists_leaf {Γ : Drawing S}
    (hno : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ → False) (hE : Γ.E.Nonempty) :
    ∃ e ∈ Γ.E, ∃ u v : S, u ≠ v ∧ closure e ∩ Γ.V = {u, v} ∧ IsLineWithEnds (closure e) u v ∧
      ∀ f ∈ Γ.E, f ≠ e → v ∉ closure f := by
  classical
  -- A longest simple walk.
  let P : ℕ → Prop := fun n => ∃ (a b : S) (W : GraphWalk Γ.toGraph a b), W.IsSimple ∧ W.length = n
  have hbound : ∀ n, P n → n ≤ Γ.finite_V.toFinset.card := by
    rintro n ⟨a, b, W, hW, rfl⟩
    have hsub : W.support.toFinset ⊆ Γ.finite_V.toFinset := by
      intro x hx
      simp only [List.mem_toFinset] at hx
      have : x ∈ Γ.V := W.mem_vertexSet_of_mem_support hx
      simpa using this
    have h₁ := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hW, length_support] at h₁
    omega
  -- Every edge gives a link between two distinct vertices.
  have hlink : ∀ f ∈ Γ.E, ∀ x ∈ Γ.V, x ∈ closure f → ∃ y, x ≠ y ∧ Γ.toGraph.IsLink f x y := by
    intro f hf x hxV hxf
    obtain ⟨u, v, huv, hcap, -⟩ := exists_ends_of_noCircuit hno hf
    have hx : x ∈ closure f ∩ Γ.V := ⟨hxf, hxV⟩
    have hu : u ∈ Γ.V := by
      have : u ∈ closure f ∩ Γ.V := by rw [hcap]; simp
      exact this.2
    have hv : v ∈ Γ.V := by
      have : v ∈ closure f ∩ Γ.V := by rw [hcap]; simp
      exact this.2
    rw [hcap] at hx
    rcases hx with rfl | hx
    · exact ⟨v, huv, hf, hu, hv, by simpa using hcap⟩
    · rw [mem_singleton_iff.mp hx]
      exact ⟨u, huv.symm, hf, hv, hu, by simpa [pair_comm] using hcap⟩
  obtain ⟨e₀, he₀⟩ := hE
  obtain ⟨u₀, v₀, huv₀, hcap₀, -⟩ := exists_ends_of_noCircuit hno he₀
  have hu₀ : u₀ ∈ closure e₀ ∩ Γ.V := by rw [hcap₀]; simp
  obtain ⟨y₀, hne₀, hl₀⟩ := hlink e₀ he₀ u₀ hu₀.2 hu₀.1
  have hP1 : P 1 := by
    refine ⟨u₀, y₀, .cons hl₀ (.nil hl₀.right_mem), ?_, rfl⟩
    exact List.nodup_cons.mpr ⟨by simpa using hne₀, List.nodup_singleton _⟩
  let N := Nat.findGreatest P Γ.finite_V.toFinset.card
  have hmax : ∀ n, P n → n ≤ N := fun n hn => Nat.le_findGreatest (hbound n hn) hn
  have hN : P N := Nat.findGreatest_spec (hbound 1 hP1) hP1
  obtain ⟨a, b, W, hW, hlen⟩ := hN
  have hN1 := hmax 1 hP1
  cases W with
  | nil _ => simp at hlen; omega
  | @cons _ w _ e h r =>
    have hnd := List.nodup_cons.mp hW
    have hrem : ∀ f ∈ Γ.E, f ≠ e → a ∉ closure f := by
      intro f hf hfe haf
      obtain ⟨y, hay, hl⟩ := hlink f hf a h.left_mem haf
      by_cases hy : y ∈ (GraphWalk.cons h r).support
      · obtain ⟨W₁, W₂, hsplit⟩ := (GraphWalk.cons h r).exists_append_of_mem hy
        have hsimple : (W₁.append W₂).IsSimple := by rw [← hsplit]; exact hW
        have hW₁ := (isSimple_of_append hsimple).1
        have hfW : f ∉ W₁.edges := by
          intro hfW
          have h₁ : f ∈ (GraphWalk.cons h r).edges := by
            rw [hsplit, GraphWalk.edges_append]
            exact List.mem_append_left _ hfW
          rcases List.mem_cons.mp h₁ with h₂ | h₂
          · exact hfe h₂
          · exact hnd.1 (r.left_mem_support_of_mem_edges h₂ hl)
        let Q : GraphWalk Γ.toGraph a y := .cons hl (.nil hl.right_mem)
        have hQ : Q.IsSimple :=
          List.nodup_cons.mpr ⟨by simpa [Q] using hay, List.nodup_singleton _⟩
        have hPs := walkDrawing_isSubdrawing Γ W₁
        have hQs := walkDrawing_isSubdrawing Γ Q
        have hV : (walkDrawing Γ W₁).V ∩ (walkDrawing Γ Q).V = {a, y} := by
          rw [walkDrawing_V, walkDrawing_V]
          ext x
          constructor
          · rintro ⟨-, hx⟩
            simpa [Q] using hx
          · rintro (rfl | hx)
            · exact ⟨W₁.start_mem_support, by simp [Q]⟩
            · rw [mem_singleton_iff.mp hx]
              exact ⟨W₁.end_mem_support, by simp [Q]⟩
        have hEd : Disjoint (walkDrawing Γ W₁).E (walkDrawing Γ Q).E := by
          rw [walkDrawing_E, walkDrawing_E]
          refine disjoint_left.mpr fun x hx hxQ => ?_
          have hxf : x = f := by simpa [Q] using hxQ
          exact hfW (hxf ▸ hx)
        exact hno _ (Drawing.isCircuit_sup (walkDrawing_isPathBetween Γ hW₁)
          (walkDrawing_isPathBetween Γ hQ) hPs hQs hay hV hEd) (Drawing.sup_isSubdrawing _ _ _)
      · have := hmax (N + 1) ⟨y, b, .cons hl.symm (.cons h r), List.nodup_cons.mpr ⟨hy, hW⟩, by
          simp only [GraphWalk.length_cons] at hlen ⊢
          omega⟩
        omega
    obtain ⟨u, v, huv, hcap, hL⟩ := exists_ends_of_noCircuit hno h.1
    have ha : a ∈ closure e ∩ Γ.V := ⟨by
      have : a ∈ closure e ∩ Γ.V := by rw [h.2.2.2]; simp
      exact this.1, h.left_mem⟩
    rw [hcap] at ha
    rcases ha with rfl | ha
    · exact ⟨e, h.1, v, a, huv.symm, by rw [hcap, pair_comm], GraphMinor.GM11.IsLineWithEnds.symm
      hL, hrem⟩
    · rw [mem_singleton_iff.mp ha] at hrem
      exact ⟨e, h.1, u, v, huv, hcap, hL, hrem⟩

end GraphMinor.GM11
