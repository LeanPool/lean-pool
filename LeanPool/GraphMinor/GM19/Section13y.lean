/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13x

/-!
# Graph Minors XIX, Section 13: tools for (13.7)

The proof of (13.7) applies Graph Minors VI, (3.6), to `sk(Γ)` inside a closed disc. Here we cut a
drawing down to a closed set whose frontier it meets only in vertices, and find the
vertex of a walk at a given position. We also show that two vertices on the closure of a cell of
size 3 have a common region.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- The vertex of a walk at position `p`. -/
noncomputable def GraphWalk.vertexAt {G : Drawing Shat} {a b : Shat} (K : GraphWalk G.toGraph a b)
  (p : ℕ) : Shat := K.support.getD p b

omit [T2Space Shat] in
/-- A walk splits at each position. -/
theorem GraphWalk.exists_split_at {G : Drawing Shat} {a b : Shat} (K : GraphWalk G.toGraph a b) {p
  : ℕ} (hp : p ≤ K.length) :
    ∃ (P : GraphWalk G.toGraph a (GraphWalk.vertexAt K p)) (Q : GraphWalk G.toGraph
      (GraphWalk.vertexAt K p) b), K = P.append Q ∧ P.length = p := by
  induction K generalizing p with
  | nil h =>
    have : p = 0 := by simpa [GraphWalk.length] using hp
    subst this
    exact ⟨.nil h, .nil h, rfl, rfl⟩
  | @cons a y b e hl t ih =>
    cases p with
    | zero => exact ⟨.nil (GraphWalk.mem_vertexSet_of_mem_support _ (GraphWalk.start_mem_support
      (.cons hl t))), .cons hl t, rfl, rfl⟩
    | succ p =>
      obtain ⟨P, Q, h₁, h₂⟩ := ih (p := p) (by simpa [GraphWalk.length] using hp)
      have hv : GraphWalk.vertexAt (.cons hl t) (p + 1) = GraphWalk.vertexAt t p := by
        simp [GraphWalk.vertexAt, GraphWalk.support]
      rw [hv]
      refine ⟨.cons hl P, Q, congrArg (GraphWalk.cons hl) h₁, ?_⟩
      simp only [GraphWalk.length, GraphWalk.edges_cons, List.length_cons]
      simp only [GraphWalk.length] at h₂
      omega

omit [T2Space Shat] in
/-- The vertex of `P.append Q` at the length of `P` is the end of `P`. -/
theorem GraphWalk.vertexAt_append {G : Drawing Shat} {a b c : Shat} (P : GraphWalk G.toGraph a b)
  (Q : GraphWalk G.toGraph b c) : GraphWalk.vertexAt (P.append Q) P.length = b := by
  induction P with
  | nil h =>
    cases Q <;> simp [GraphWalk.vertexAt, GraphWalk.length, GraphWalk.append]
  | @cons a y b e hl t ih =>
    have := ih Q
    simpa [GraphWalk.vertexAt, GraphWalk.support, GraphWalk.length, GraphWalk.append] using this

/-- A drawing, cut down to a closed set whose frontier it meets only in vertices. -/
theorem exists_restrict {T : Type} [TopologicalSpace T] (D : Drawing T) {Y : Set T}
  (hY : IsClosed Y) (hfr : D.U ∩ frontier Y ⊆ D.V) :
    ∃ D' : Drawing T, D'.U = D.U ∩ Y ∧ D'.V = D.V ∩ Y ∧ ∀ e, e ∈ D'.E ↔ e ∈ D.E ∧ e ⊆ Y := by
  have hside : ∀ e ∈ D.E, e ⊆ Y ∨ Disjoint e Y := fun e he ↦
    subset_or_disjoint_of_frontier hY he.2.2.1.isConnected.isPreconnected
      (disjoint_left.mpr fun x hx hxf ↦ (he.2.1 hx).2 (hfr ⟨(he.2.1 hx).1, hxf⟩))
  have hset : (D.U ∩ Y) \ (D.V ∩ Y) = (D.U \ D.V) ∩ Y := by
    ext x
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩
      exact ⟨⟨h₁, fun h₄ ↦ h₃ ⟨h₄, h₂⟩⟩, h₂⟩
    · rintro ⟨⟨h₁, h₃⟩, h₂⟩
      exact ⟨⟨h₁, h₂⟩, fun h₄ ↦ h₃ h₄.1⟩
  have hA : ∀ C, C ∈ arcComponentsIn ((D.U ∩ Y) \ (D.V ∩ Y)) ↔ C ∈ D.E ∧ C ⊆ Y := fun C ↦ by
    rw [hset]
    constructor
    · intro hC
      obtain ⟨x, hx⟩ := hC.1
      have hxF := hC.2.1 hx
      obtain ⟨e, he, hxe⟩ := exists_mem_arcComponent (F := D.U \ D.V) hxF.1
      have heC : C ⊆ e := by
        have hu := he.2.2.2 _ (union_subset he.2.1 fun y hy ↦ (hC.2.1 hy).1)
          (he.2.2.1.union hC.2.2.1 ⟨x, hxe, hx⟩) subset_union_left
        exact hu ▸ subset_union_right
      have heY : e ⊆ Y := (hside e he).resolve_right fun hd ↦ disjoint_left.mp hd hxe hxF.2
      have := hC.2.2.2 e (fun y hy ↦ ⟨he.2.1 hy, heY hy⟩) he.2.2.1 heC
      exact ⟨this ▸ he, this ▸ heY⟩
    · rintro ⟨he, hY'⟩
      exact ⟨he.1, fun y hy ↦ ⟨he.2.1 hy, hY' hy⟩, he.2.2.1, fun X hX hc hs ↦ he.2.2.2 X
        (fun y hy ↦ (hX hy).1) hc hs⟩
  have hE : ∀ e ∈ arcComponentsIn ((D.U ∩ Y) \ (D.V ∩ Y)), (∃ u v : T, u ≠ v ∧ closure e ∩
    (D.V ∩ Y) = {u, v} ∧ IsLineWithEnds (closure e) u v) ∨
      (∃ u : T, closure e ∩ (D.V ∩ Y) = {u} ∧ IsOArc (closure e)) := fun e he ↦ ?_
  · exact ⟨⟨D.U ∩ Y, D.V ∩ Y, fun x hx ↦ ⟨D.V_subset_U hx.1, hx.2⟩, D.isClosed_U.inter hY,
      D.finite_V.subset inter_subset_left, D.finite_edges.subset fun e he ↦
        ((hA e).mp he).1, hE⟩, rfl, rfl, hA⟩
  obtain ⟨he₁, he₂⟩ := (hA e).mp he
  have hcl : closure e ∩ (D.V ∩ Y) = closure e ∩ D.V := by
    ext x
    exact ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, closure_minimal he₂ hY h.1⟩⟩
  rw [hcl]
  exact D.edge_cond e he₁

/-- Two ends of an edge of size 3 are on the closure of one side of the edge. -/
theorem Painting.exists_side_of_ends (Γ : Painting S) {c : Set S} (hc : c ∈ Γ.E) (h3 :
  (tilde c).ncard = 3) {a b : S} (ha : a ∈ tilde c) (hb : b ∈ tilde c) (hab : a ≠ b) :
    ∃ f, Γ.IsSkEdgeIn f c ∧ a ∈ closure f ∧ b ∈ closure f := by
  obtain ⟨hdisc, hT, hfin⟩ := Γ.isDisc_of_three hc h3
  have hO := hdisc.isOArc_discBd
  obtain ⟨d, hda, hdb, hd⟩ : ∃ d, d ≠ a ∧ d ≠ b ∧ d ∈ tilde c := by
    by_contra hn
    push Not at hn
    have hsub : tilde c ⊆ {a, b} := fun d hd ↦ by
      by_cases h₁ : d = a
      · exact .inl h₁
      · exact .inr (by_contra fun h₂ ↦ hn d h₁ h₂ hd)
    have := Set.ncard_le_ncard hsub (by simp)
    rw [h3, Set.ncard_pair hab] at this
    omega
  obtain ⟨A, B, hA, hB, hun, hin⟩ := hO.lines (hT ha) (hT hb) hab
  obtain ⟨L, hL, hdL⟩ : ∃ L, IsLineWithEnds L a b ∧ L ⊆ discBd (closure c) ∧ d ∉ L := by
    by_cases hdA : d ∈ A
    · refine ⟨B, hB, hun ▸ subset_union_right, fun hdB ↦ ?_⟩
      have : d ∈ A ∩ B := ⟨hdA, hdB⟩
      rw [hin] at this
      rcases this with h | h
      · exact hda h
      · exact hdb h
    · exact ⟨A, hA, hun ▸ subset_union_left, hdA⟩
  have hpc : IsPathConnected (L \ {a, b}) := GM11.isPathConnected_sdiff_pair hL
  obtain ⟨p, hp⟩ := hpc.nonempty
  have hsub : L \ {a, b} ⊆ discBd (closure c) \ tilde c := fun x hx ↦ ⟨hdL.1 hx.1, fun ht ↦ by
    have heq : ({a, b, d} : Set S) = tilde c := Set.eq_of_subset_of_ncard_le (by
      rintro y (rfl | rfl | rfl)
      · exact ha
      · exact hb
      · exact hd) (by
      rw [h3, Set.ncard_insert_of_notMem (by simp [hab, hda.symm]), Set.ncard_pair hdb.symm]) hfin
    rw [← heq] at ht
    rcases ht with rfl | rfl | rfl
    · exact hx.2 (.inl rfl)
    · exact hx.2 (.inr rfl)
    · exact hdL.2 hx.1⟩
  obtain ⟨f, hf, hpf⟩ := exists_mem_arcComponent (hsub hp)
  have hLf : L \ {a, b} ⊆ f := by
    have hu := hf.2.2.2 _ (union_subset hf.2.1 hsub) (hf.2.2.1.union hpc ⟨p, hpf, hp⟩)
      subset_union_left
    exact hu ▸ subset_union_right
  have hcl : L ⊆ closure f := hL.subset_closure_diff.trans (closure_mono hLf)
  exact ⟨f, ⟨hc, .inr ⟨h3, hf⟩⟩, hcl hL.left_mem, hcl hL.right_mem⟩

end GraphMinor.GM19
