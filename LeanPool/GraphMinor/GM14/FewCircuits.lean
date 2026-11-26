/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Section8a
public import LeanPool.GraphMinor.GM09.Basic
public import LeanPool.GraphMinor.GM09.Section2c
public import LeanPool.GraphMinor.GM09.Section3a
public import LeanPool.GraphMinor.GM09.Section9

/-!
# Graphs with at most one circuit

In the proof of Graph Minors XIV, (8.4) (page 42), the paper uses the fact that "every graph with
at most one circuit can be drawn in the plane with all its vertices incident with the infinite
region". We build this drawing one vertex at a time. This file finds the vertex to add last: a
finite graph with at most one circuit is either that circuit, or it has a vertex with at most one
edge at it.
-/


@[expose] public section

namespace GraphMinor.GM14

open Set Graph GraphMinor GraphMinor.GM09 GraphMinor.Surface

universe u v

variable {α : Type u} {β : Type v}

/-- A finite graph has finitely many subgraphs. -/
theorem finite_subgraphs {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite) :
    {C : Graph α β | C ≤ G}.Finite := by
  have hfin := Set.Finite.prod hV.finite_subsets hE.finite_subsets
  refine Set.Finite.of_finite_image (f := fun C : Graph α β => (V(C), E(C)))
    (hfin.subset ?_) ?_
  · rintro _ ⟨C, hC, rfl⟩
    have hC' : C ≤ G := hC
    exact ⟨hC'.vertexSet_mono, hC'.edgeSet_mono⟩
  · intro C hC D hD h
    have h' : V(C) = V(D) ∧ E(C) = E(D) := by simpa using h
    exact (Compatible.of_le_le hC hD).ext h'.1 h'.2

/-- Two circuits of a finite graph with at most one circuit are equal. -/
theorem eq_of_isGraphCircuit {G C D : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (hc : {C | IsGraphCircuit G C}.ncard ≤ 1) (hC : IsGraphCircuit G C)
    (hD : IsGraphCircuit G D) : C = D := by
  have hfin : {C | IsGraphCircuit G C}.Finite :=
    (finite_subgraphs hV hE).subset fun _ h => h.1
  by_contra hne
  have h2 : 2 ≤ {C | IsGraphCircuit G C}.ncard := by
    rw [← ncard_pair hne]
    refine ncard_le_ncard ?_ hfin
    rintro x (rfl | rfl)
    · exact hC
    · exact hD
  omega

/-- A loop is a circuit. -/
theorem isGraphCircuit_of_isLoop {G : Graph α β} {e : β} {a : α} (hl : G.IsLink e a a) :
    IsGraphCircuit G (walkSubgraph (GraphWalk.cons hl (GraphWalk.nil hl.left_mem))) := by
  refine ⟨walkSubgraph_le _, ?_⟩
  have hl' : (walkSubgraph (GraphWalk.cons hl (GraphWalk.nil hl.left_mem))).IsLink e a a := by
    exact (walkSubgraph_isLink _).mpr ⟨by simp [GraphWalk.edges], hl⟩
  refine ⟨a, GraphWalk.cons hl' (GraphWalk.nil hl'.left_mem), ?_, ?_, ?_, ?_⟩
  · simp [GraphWalk.IsSimpleClosed, GraphWalk.support, GraphWalk.edges]
  · simp [GraphWalk.length, GraphWalk.edges]
  · rw [vertexSet_walkSubgraph]
    simp [GraphWalk.support]
  · rw [edgeSet_walkSubgraph]
    simp [GraphWalk.edges]

/-- An edge between two distinct vertices is a path. -/
theorem isGraphPathWithEnds_edge {G : Graph α β} {e : β} {a b : α} (hl : G.IsLink e a b)
    (hab : a ≠ b) :
    IsGraphPathWithEnds G (walkSubgraph (GraphWalk.cons hl (GraphWalk.nil hl.right_mem))) a b :=
  isGraphPathWithEnds_walkSubgraph (by simpa [GraphWalk.IsSimple, GraphWalk.support] using hab)

/-- At an end of a longest path of a graph with no circuit, every edge lies on the path. -/
theorem mem_edgeSet_of_longest {F Q : Graph α β} {a b : α}
    (hno : ¬ ∃ C : Graph α β, IsGraphCircuit F C) (hVF : V(F).Finite)
    (hQ : IsGraphPathWithEnds F Q a b)
    (hmax : ∀ (Q' : Graph α β) (a' b' : α), IsGraphPathWithEnds F Q' a' b' →
      V(Q').ncard ≤ V(Q).ncard)
    {f : β} {y : α} (hl : F.IsLink f a y) : f ∈ E(Q) := by
  by_contra hf
  by_cases hy : y ∈ V(Q)
  · by_cases hay : a = y
    · subst hay
      exact hno ⟨_, isGraphCircuit_of_isLoop hl⟩
    · obtain ⟨R, hRQ, -, hR⟩ := hQ.exists_subpath hQ.left_mem hy
      refine hno ⟨_, isGraphCircuit_subgraphUnion hR (isGraphPathWithEnds_edge hl hay) hay ?_ ?_⟩
      · refine subset_antisymm ?_ ?_
        · rintro x ⟨-, hx⟩
          rw [vertexSet_walkSubgraph] at hx
          simpa [GraphWalk.support] using hx
        · rintro x (rfl | rfl)
          · exact ⟨hR.left_mem, by simp [vertexSet_walkSubgraph, GraphWalk.support]⟩
          · exact ⟨hR.right_mem, by simp [vertexSet_walkSubgraph, GraphWalk.support]⟩
      · rw [edgeSet_walkSubgraph]
        refine disjoint_left.mpr fun e he h => ?_
        have : e = f := by simpa [GraphWalk.edges] using h
        exact hf (this ▸ hRQ.edgeSet_mono he)
  · obtain ⟨hQF, W, hW, hVQ, -⟩ := hQ
    obtain ⟨W', hs, -⟩ := exists_walk_up_of_le hQF W
    have hs' : (GraphWalk.cons hl.symm W').IsSimple := by
      unfold GraphWalk.IsSimple
      rw [GraphWalk.support_cons, hs]
      refine List.nodup_cons.mpr ⟨fun h => hy ?_, hW⟩
      rw [hVQ]
      exact h
    have hle := hmax _ _ _ (isGraphPathWithEnds_walkSubgraph hs')
    have hV' : V(walkSubgraph (GraphWalk.cons hl.symm W')) = insert y V(Q) := by
      rw [vertexSet_walkSubgraph, GraphWalk.support_cons, hs, hVQ]
      ext x
      simp
    rw [hV', ncard_insert_of_notMem hy (hVF.subset hQF.vertexSet_mono)] at hle
    omega

/-- A graph with an edge and no circuit has a path with two distinct ends that is as long as
possible. -/
theorem exists_longest_path {F : Graph α β} (hVF : V(F).Finite) (hno : ¬ ∃ C, IsGraphCircuit F C)
    (hE : E(F).Nonempty) :
    ∃ (Q : Graph α β) (a b : α), IsGraphPathWithEnds F Q a b ∧ a ≠ b ∧
      ∀ (Q' : Graph α β) (a' b' : α), IsGraphPathWithEnds F Q' a' b' →
        V(Q').ncard ≤ V(Q).ncard := by
  classical
  obtain ⟨e, he⟩ := hE
  obtain ⟨p, q, hl⟩ := F.exists_isLink_of_mem_edgeSet he
  have hpq : p ≠ q := by
    rintro rfl
    exact hno ⟨_, isGraphCircuit_of_isLoop hl⟩
  have hbd : ∀ (Q' : Graph α β) (a' b' : α), IsGraphPathWithEnds F Q' a' b' →
      V(Q').ncard ≤ V(F).ncard := fun Q' _ _ h => ncard_le_ncard h.le.vertexSet_mono hVF
  let s : Set ℕ := {n | ∃ (Q : Graph α β) (a b : α), IsGraphPathWithEnds F Q a b ∧ a ≠ b ∧
    V(Q).ncard = n}
  have hs : s.Finite := (Set.finite_Iic V(F).ncard).subset fun n ⟨Q, a, b, h, _, hn⟩ =>
    hn ▸ hbd Q a b h
  have hne : s.Nonempty := ⟨_, _, p, q, isGraphPathWithEnds_edge hl hpq, hpq, rfl⟩
  obtain ⟨n, hn, hmax⟩ := hs.exists_maximal hne
  obtain ⟨Q, a, b, hQ, hab, rfl⟩ := hn
  refine ⟨Q, a, b, hQ, hab, fun Q' a' b' h => ?_⟩
  by_cases heq : a' = b'
  · subst heq
    have h1 : V(Q') = {a'} := by
      obtain ⟨-, W, hW, hV, -⟩ := h
      cases W with
      | nil hv => rw [hV]; ext x; simp [GraphWalk.support]
      | cons hlink W' =>
        have := List.nodup_cons.mp (show (_ :: W'.support).Nodup from hW)
        exact (this.1 W'.end_mem_support).elim
    rw [h1, ncard_singleton]
    exact Nat.succ_le_of_lt ((ncard_pos (hVF.subset hQ.le.vertexSet_mono)).mpr ⟨a, hQ.left_mem⟩)
  · by_contra hlt
    exact absurd (hmax ⟨Q', a', b', h, heq, rfl⟩ (not_le.mp hlt).le) (by omega)

/-- **A vertex to add last.** A finite graph with a vertex and at most one circuit is either a
circuit, or it has a vertex with no edge at it, or a vertex with just one edge at it, not a loop. -/
theorem isGraphCircuit_self_or_exists_leaf {K : Graph α β} (hV : V(K).Finite) (hE : E(K).Finite)
    (hc : {C | IsGraphCircuit K C}.ncard ≤ 1) (hne : V(K).Nonempty) :
    IsGraphCircuit K K ∨ ∃ r ∈ V(K), (∀ e x, ¬ K.IsLink e r x) ∨
      ∃ e u, u ≠ r ∧ K.IsLink e r u ∧ ∀ e' x, K.IsLink e' r x → e' = e := by
  classical
  -- `Z` is the edge set of the circuit of `K`, if it has one.
  obtain ⟨Z, Y, hZK, hZ⟩ : ∃ (Z : Set β) (Y : Set α), Z ⊆ E(K) ∧
      ((Z = ∅ ∧ Y = ∅ ∧ ¬ ∃ C, IsGraphCircuit K C) ∨
        ∃ C, IsGraphCircuit K C ∧ Z = E(C) ∧ Y = V(C)) := by
    by_cases h : ∃ C, IsGraphCircuit K C
    · obtain ⟨C, hC⟩ := h
      exact ⟨E(C), V(C), hC.1.edgeSet_mono, Or.inr ⟨C, hC, rfl, rfl⟩⟩
    · exact ⟨∅, ∅, empty_subset _, Or.inl ⟨rfl, rfl, h⟩⟩
  let F : Graph α β := K.restrict (E(K) \ Z)
  have hFK : F ≤ K := restrict_le
  have hVF : V(F) = V(K) := rfl
  have hEF : E(F) = E(K) \ Z := by
    change E(K) ∩ (E(K) \ Z) = _
    exact inter_eq_right.mpr sdiff_subset
  -- A circuit of `F` would be a second circuit of `K`.
  have hno : ¬ ∃ C, IsGraphCircuit F C := by
    rintro ⟨C, hC⟩
    have hC' : IsGraphCircuit K C := ⟨hC.1.trans hFK, hC.2⟩
    rcases hZ with ⟨-, -, h⟩ | ⟨C₀, hC₀, rfl, -⟩
    · exact h ⟨C, hC'⟩
    · have heq := eq_of_isGraphCircuit hV hE hc hC' hC₀
      subst heq
      have hCF := hC.1
      obtain ⟨-, u, W, -, hpos, -, hEC⟩ := hC
      cases W with
      | nil _ => simp [GraphWalk.length, GraphWalk.edges] at hpos
      | @cons x y z e hl W' =>
        have heC : e ∈ E(C) := by rw [hEC]; simp [GraphWalk.edges]
        have : e ∈ E(F) := hCF.edgeSet_mono heC
        rw [hEF] at this
        exact this.2 heC
  have hYedge : ∀ {e x y}, K.IsLink e x y → x ∉ Y → e ∉ Z := by
    intro e x y hl hx heZ
    rcases hZ with ⟨rfl, -, -⟩ | ⟨C, hC, rfl, rfl⟩
    · exact heZ
    · exact hx (hC.1.vertexSet_mono |> fun _ => ((hC.1.isLink_iff heZ).mpr hl).left_mem)
  by_cases hEF' : E(F).Nonempty
  · obtain ⟨Q, a, b, hQ, hab, hmax⟩ := exists_longest_path (hVF ▸ hV) hno hEF'
    -- An end of `Q` off the circuit has only one edge at it.
    have hleaf : ∀ {a b : α}, IsGraphPathWithEnds F Q a b → a ≠ b → a ∉ Y →
        ∃ r ∈ V(K), (∀ e x, ¬ K.IsLink e r x) ∨
          ∃ e u, u ≠ r ∧ K.IsLink e r u ∧ ∀ e' x, K.IsLink e' r x → e' = e := by
      intro a b hQ hab ha
      obtain ⟨e, heQ, hinc⟩ := hQ.exists_inc_left_of_ne hab
      obtain ⟨u, hu⟩ := hinc
      refine ⟨a, hVF ▸ hQ.le.vertexSet_mono hQ.left_mem, Or.inr ⟨e, u, ?_,
        (hu.mono (hQ.le.trans hFK)), ?_⟩⟩
      · rintro rfl
        exact hno ⟨_, isGraphCircuit_of_isLoop (hu.mono hQ.le)⟩
      · intro e' x hl
        have hlF : F.IsLink e' a x := by
          refine (hFK.isLink_iff ?_).mpr hl
          rw [hEF]
          exact ⟨hl.edge_mem, hYedge hl ha⟩
        have he' := mem_edgeSet_of_longest hno (hVF ▸ hV) hQ hmax hlF
        have hinc' : Q.Inc e' a := ⟨x, (hQ.le.isLink_iff he').mpr hlF⟩
        exact hQ.inc_left_unique he' heQ hinc' ⟨u, hu⟩
    by_cases ha : a ∈ Y
    · by_cases hb : b ∈ Y
      · -- Both ends on the circuit: the path gives a second circuit.
        exfalso
        rcases hZ with ⟨-, rfl, -⟩ | ⟨C, hC, rfl, rfl⟩
        · exact ha
        · have hne' : (V(Q) ∩ (V(C) \ {a})).Nonempty :=
            ⟨b, hQ.right_mem, hb, fun h => hab h.symm⟩
          obtain ⟨u, ⟨-, huC, hua⟩, P₁, P₂, hP₁Q, -, hP₁, -, -, -, -, hdis⟩ :=
            hQ.exists_first_split_at_mem hne'
          have hau : a ≠ u := fun h => hua h.symm
          obtain ⟨R, -, hRC, -, hR, -, -, -, -, -, -⟩ :=
            IsGraphCircuit.exists_two_paths hC ha huC hau
          have hP₁K : IsGraphPathWithEnds K P₁ a u :=
            hP₁.mono (hQ.le.trans hFK)
          have hEP₁ : Disjoint E(P₁) E(C) := by
            refine disjoint_left.mpr fun e he heC => ?_
            have : e ∈ E(F) := (hP₁Q.trans hQ.le).edgeSet_mono he
            rw [hEF] at this
            exact this.2 heC
          have hVP₁ : V(P₁) ∩ V(R) = {a, u} := by
            refine subset_antisymm ?_ ?_
            · rintro x ⟨hx₁, hxR⟩
              by_cases hxa : x = a
              · exact Or.inl hxa
              by_cases hxu : x = u
              · exact Or.inr hxu
              exact (disjoint_left.mp hdis ⟨hx₁, hxu⟩ ⟨hRC.vertexSet_mono hxR, hxa⟩).elim
            · rintro x (rfl | rfl)
              · exact ⟨hP₁.left_mem, hR.left_mem⟩
              · exact ⟨hP₁.right_mem, hR.right_mem⟩
          have hC₂ := isGraphCircuit_subgraphUnion hP₁K hR hau hVP₁
            (hEP₁.mono_right hRC.edgeSet_mono)
          have heq := eq_of_isGraphCircuit hV hE hc hC₂ hC
          obtain ⟨e, he, -⟩ := hP₁.exists_inc_left_of_ne hau
          have heC : e ∈ E(C) := by
            rw [← heq, edgeSet_subgraphUnion hP₁K.le hR.le]
            exact Or.inl he
          exact disjoint_left.mp hEP₁ he heC
      · exact Or.inr (hleaf hQ.symm hab.symm hb)
    · exact Or.inr (hleaf hQ hab ha)
  · -- All edges of `K` lie on the circuit.
    have hEK : E(K) ⊆ Z := by
      intro e he
      by_contra heZ
      exact hEF' ⟨e, hEF ▸ ⟨he, heZ⟩⟩
    by_cases hall : V(K) ⊆ Y
    · rcases hZ with ⟨-, rfl, -⟩ | ⟨C, hC, rfl, rfl⟩
      · obtain ⟨x, hx⟩ := hne
        exact (hall hx).elim
      · left
        have heq : C = K :=
          (Compatible.of_le_le hC.1 le_rfl).ext (subset_antisymm hC.1.vertexSet_mono hall)
            (subset_antisymm hC.1.edgeSet_mono hEK)
        exact heq ▸ hC
    · obtain ⟨r, hr, hrY⟩ := not_subset.mp hall
      exact Or.inr ⟨r, hr, Or.inl fun e x hl => hYedge hl hrY (hEK hl.edge_mem)⟩

end GraphMinor.GM14
