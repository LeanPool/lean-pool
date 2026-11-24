/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffWalk
public import LeanPool.GraphMinor.Menger.SimpleGraph

/-!
# Graph Minors VII, (4.3)

We prove (4.3) of Graph Minors VII (pages 222 and 223). Let `G` be a proper graph in a connected
surface `Σ` with at least two cuffs, such that every `G`-normal `O`-arc off `bd(Σ)` with at most `v`
vertices of `G` is null-homotopic.
Then for each cuff `C` there are `v + 1` paths of `G` from `C` to the rest of `bd(Σ)`, disjoint
except for their ends.

We follow the paper. Let `X` be a set of at most `v` vertices off `bd(Σ)`. The first step
(`exists_walk_avoiding`) is that `G - X` has a path from `C` to the rest of `bd(Σ)`. The set
`Z`, which is `Σ - (U(G) ∪ bd(Σ))` with `X` added, is flat by hypothesis. It stays flat when we add
the edges at `X` (`IsFlat.union_edge`). Now take a smallest subgraph `K` of `G - X` with `offSet K`
flat, and apply `exists_walk_between_cuffs`.

The second step (`exists_paths_of_walks`) is the form of Menger's theorem that the paper cites. Let
`A` and `B` be the vertices on `C` and on the rest of `bd(Σ)`. If an edge joins `A` to `B`, then we
take this one-edge path `v + 1` times. The statement
allows that, because the paths need to be disjoint only except for their ends. Otherwise we use
Menger's theorem between the neighbours of `A` and of `B` in `G - (A ∪ B)`, and add one edge at each
end of each path.

The file ends with the first step of the proof of (4.6) (`exists_paths_from_vertex`), which applies
(4.3) to the graph `G'` obtained
from `G` by deleting the vertices of a cuff `C` other than one vertex `z`, as the paper does on
pages 224 and 225.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S : Type} [TopologicalSpace S] [T1Space S]

omit [T1Space S] in
/-- A flat set off `U(G)` and `bd(Σ)`, with a set `X` of vertices added, stays flat when we add
every edge of `G` whose closure
meets `X` (`IsFlat.union_edge`, one edge at a time). This is a step of the proof of (4.3) of Graph
Minors VII (page 222). -/
theorem isFlat_union_edges (hS : IsSurface S) {G : Drawing S} (hG : G.IsProper) {X : Set S}
  (hXV : X ⊆ G.V)
    (hZ : IsFlat (offSet G ∪ X)) :
    IsFlat (offSet G ∪ X ∪ ⋃₀ {e | e ∈ G.E ∧ ¬ Disjoint (closure e) X}) := by
  classical
  let Z : Set S := offSet G ∪ X
  let Es : Set (Set S) := {e | e ∈ G.E ∧ ¬ Disjoint (closure e) X}
  have hEf : Es.Finite := G.finite_edges.subset fun e he => he.1
  have hF : ∀ T : Set (Set S), T.Finite → T ⊆ Es → IsFlat (Z ∪ ⋃₀ T) := by
    intro T hT
    induction T, hT using Set.Finite.induction_on with
    | empty =>
      intro _
      simpa using hZ
    | @insert e T _ _ ih =>
      intro hs
      have h1 := ih (fun f hf => hs (.inr hf))
      obtain ⟨he, hd⟩ := hs (mem_insert e T)
      obtain ⟨x, hxe, hxX⟩ := not_disjoint_iff.mp hd
      have h2 := IsFlat.union_edge hS hG h1 (fun z h3 h4 => .inl (.inl
        (mem_offSet.mpr ⟨h3, h4⟩))) he hxe (hXV hxX) (.inl (.inr hxX))
      refine IsFlat.mono h2 fun z hz => ?_
      rcases hz with h | ⟨f, hf, hzf⟩
      · exact .inl (.inl h)
      · rcases hf with rfl | hf
        · exact .inr hzf
        · exact .inl (.inr ⟨f, hf, hzf⟩)
  exact hF Es hEf subset_rfl

/-- **From a flat set to a walk between cuffs.** Let `X` be a set of vertices of a proper graph `G`,
possibly on `bd(Σ)`. If the set off `U(G)` and `bd(Σ)`, with `X` added, is flat, then `G - X` has a
walk from the cuff `C` to the
rest of `bd(Σ)`. This is the core of the proof of (4.3) of Graph Minors VII (pages 222 and 223). -/
theorem exists_walk_of_flat (hS : IsSurface S) [ConnectedSpace S] {G : Drawing S}
  (hG : G.IsProper) {C C' : Set S} (hC : C ∈ cuffs S) (hC' : C' ∈ cuffs S) (hne : C ≠ C')
    {X : Set S} (hXV : X ⊆ G.V) (hZ : IsFlat (offSet G ∪ X)) :
    ∃ a ∈ G.V ∩ C, ∃ b ∈ G.V ∩ (bd S \ C), ∃ W : GraphWalk G.toGraph a b, ∀ z ∈ W.support, z ∉ X
      := by
  classical
  have ht2 : T2Space S := hS.2.1
  let Es : Set (Set S) := {e | e ∈ G.E ∧ ¬ Disjoint (closure e) X}
  obtain ⟨K₀, hK₀s, hK₀V, hK₀E⟩ := exists_sub (K := G) (V' := G.V \ X) (E' := {e | e ∈ G.E
    ∧ Disjoint (closure e) X}) sdiff_subset (fun e he => he.1) fun e he z hz => ⟨hz.2, fun hzX
      => disjoint_left.mp he.2 hz.1 hzX⟩
  have hK₀ : IsFlatSub G X K₀ := by
    refine ⟨hK₀s, hK₀V ▸ disjoint_sdiff_left, IsFlat.mono (isFlat_union_edges hS hG hXV hZ) fun z
      hz => ?_⟩
    have h := mem_offSet.mp hz
    by_cases hzU : z ∈ G.U
    · rw [G.U_eq] at hzU
      rcases hzU with h1 | h1
      · refine .inl (.inr ?_)
        by_contra hzX
        exact h.1 (K₀.V_subset_U (hK₀V ▸ ⟨h1, hzX⟩))
      · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp h1
        by_cases hd : Disjoint (closure e) X
        · exact (h.1 (K₀.closure_subset_U (hK₀E ▸ ⟨he, hd⟩) hze)).elim
        · by_cases hzV : z ∈ G.V
          · refine .inl (.inr ?_)
            by_contra hzX
            exact h.1 (K₀.V_subset_U (hK₀V ▸ ⟨hzV, hzX⟩))
          · refine .inr ⟨e, ⟨he, hd⟩, ?_⟩
            rw [← G.closure_diff_V he]
            exact ⟨hze, hzV⟩
    · exact .inl (.inl (mem_offSet.mpr ⟨hzU, h.2⟩))
  obtain ⟨K, hK, hmin⟩ := exists_smallest_flatSub ⟨K₀, hK₀⟩
  have hKp : K.IsProper := fun z hz => by
    have hzG : z ∈ G.V := hG ⟨hz.1, hK.1.U_subset hz.2⟩
    have h := hz.2
    rw [K.U_eq] at h
    rcases h with h | h
    · exact h
    · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp h
      by_contra hzK
      have h1 : z ∈ e := by
        rw [← K.closure_diff_V he]
        exact ⟨hze, hzK⟩
      have h2 : z ∈ closure e \ G.V := by
        rw [G.closure_diff_V (hK.1.2 he)]
        exact h1
      exact h2.2 hzG
  have hconn := isPreconnected_offSet hS hKp hK.2.2 fun e he => not_isFlat_union_edge hK hmin he
  obtain ⟨a, ha, b, hb, ⟨W⟩⟩ := exists_walk_between_cuffs hS hC hC' hne hKp hconn
    (offSet_nonempty hS hC hC' hne hKp) hK.2.2 fun Δ hΔ h => disc_subset_offSet hS hK hmin hΔ h
  obtain ⟨W', hs, -⟩ := hK.1.exists_walk_up W
  refine ⟨a, ⟨hK.1.1 ha.1, ha.2⟩, b, ⟨hK.1.1 hb.1, hb.2⟩, W', fun z hz hzX => ?_⟩
  rw [hs] at hz
  exact disjoint_left.mp hK.2.1 (W.mem_vertexSet_of_mem_support hz) hzX

/-- The first step of the proof of (4.3) (Graph Minors VII, pages 222 and 223). -/
theorem exists_walk_avoiding (hS : IsSurface S) [ConnectedSpace S] {G : Drawing S}
  (hG : G.IsProper) {v : ℕ}
    (hnull : ∀ F : Set S, G.IsNormal F → IsOArc F → F ∩ bd S = ∅ → (G.V ∩ F).ncard ≤ v
      → IsNullHomotopicOArc F) {C C' : Set S} (hC : C ∈ cuffs S) (hC' : C' ∈ cuffs S) (hne : C ≠ C')
    {X : Set S} (hXV : X ⊆ G.V) (hXb : Disjoint X (bd S)) (hXc : X.ncard ≤ v) :
    ∃ a ∈ G.V ∩ C, ∃ b ∈ G.V ∩ (bd S \ C), ∃ W : GraphWalk G.toGraph a b, ∀ z ∈ W.support, z ∉ X
      := by
  have hXf : X.Finite := G.finite_V.subset hXV
  refine exists_walk_of_flat hS hG hC hC' hne hXV (isFlat_of_forall_isNullHomotopicOArc hS fun F hF
    hO => hnull F ?_ hO ?_ ?_)
  · rintro z ⟨hzF, hzU⟩
    rcases hF hzF with h | h
    · exact ((mem_offSet.mp h).1 hzU).elim
    · exact hXV h
  · refine eq_empty_of_forall_notMem fun z hz => ?_
    rcases hF hz.1 with h | h
    · exact (mem_offSet.mp h).2 hz.2
    · exact disjoint_left.mp hXb h hz.2
  · refine (ncard_le_ncard (fun z hz => ?_) hXf).trans hXc
    rcases hF hz.2 with h | h
    · exact ((mem_offSet.mp h).1 (G.V_subset_U hz.1)).elim
    · exact h

/-- The form of Menger's theorem in the proof of (4.3) of Graph Minors VII (page 222): paths from
`A` to `B` that are disjoint except for their ends. -/
theorem exists_paths_of_walks (G : Drawing S) {A B : Set S} (hAB : Disjoint A B) {v : ℕ}
    (h : ∀ X : Set S, X ⊆ G.V → Disjoint X (A ∪ B) → X.ncard ≤ v → ∃ a ∈ A, ∃ b ∈ B, ∃ W :
      GraphWalk G.toGraph a b, ∀ z ∈ W.support, z ∉ X) :
    ∃ (P : Fin (v + 1) → Drawing S) (s t : Fin (v + 1) → S), (∀ i, (P i).IsSubdrawing G ∧ s i ∈ A
      ∧ t i ∈ B ∧ (P i).IsPathBetween (s i) (t i)) ∧
      ∀ i j, i ≠ j → Disjoint ((P i).V \ {s i, t i}) ((P j).V \ {s j, t j}) := by
  classical
  by_cases hdirect : ∃ a ∈ A, ∃ b ∈ B, ∃ e, G.toGraph.IsLink e a b
  · obtain ⟨a, ha, b, hb, e, hl⟩ := hdirect
    have hab : a ≠ b := fun h => disjoint_left.mp hAB ha (h ▸ hb)
    let W : GraphWalk G.toGraph a b := .cons hl (.nil hl.2.2.1)
    have hW : W.IsSimple := by
      simp [GraphWalk.IsSimple, W, GraphWalk.support, hab]
    refine ⟨fun _ => walkDrawing G W, fun _ => a, fun _ => b, fun _ => ⟨walkDrawing_isSubdrawing G
      W, ha, hb, walkDrawing_isPathBetween G hW⟩, fun i j _ => ?_⟩
    have : (walkDrawing G W).V \ {a, b} = ∅ := by
      rw [walkDrawing_V]
      ext z
      simp [W, GraphWalk.support]
      tauto
    simp only [this, empty_disjoint]
  -- There is no edge from `A` to `B`.
  let H : SimpleGraph G.V :=
    { Adj := fun x y => x ≠ y ∧ x.1 ∉ A ∪ B ∧ y.1 ∉ A ∪ B ∧ ∃ e, G.toGraph.IsLink e x.1 y.1
      symm := ⟨fun x y h => ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.imp fun _ hl => hl.symm⟩⟩
      loopless := ⟨fun x h => h.1 rfl⟩ }
  let NA : Set G.V := {x | x.1 ∉ A ∪ B ∧ ∃ a ∈ A, ∃ e, G.toGraph.IsLink e a x.1}
  let NB : Set G.V := {x | x.1 ∉ A ∪ B ∧ ∃ b ∈ B, ∃ e, G.toGraph.IsLink e x.1 b}
  have hfin : Finite G.V := G.finite_V
  have hoff : ∀ {p q : G.V} (w : H.Walk p q), p.1 ∉ A ∪ B → ∀ u ∈ w.support, u.1 ∉ A ∪ B := by
    intro p q w
    induction w with
    | nil =>
      intro hp u hu
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hu
      exact hu ▸ hp
    | cons h' _ ih =>
      intro hp u hu
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact hp
      · exact ih h'.2.2.1 u hu
  have key : ∀ {x y : S} (W : GraphWalk G.toGraph x y), y ∈ B →
      (x ∉ A ∪ B → (∃ (hx : x ∈ G.V) (z : G.V), z ∈ NB ∧ ∃ w : H.Walk ⟨x, hx⟩ z, ∀ u ∈ w.support,
        u.1 ∈ W.support) ∨
        ∃ x₁ ∈ NA, ∃ z ∈ NB, ∃ w : H.Walk x₁ z, ∀ u ∈ w.support, u.1 ∈ W.support) ∧
      (x ∈ A → ∃ x₁ ∈ NA, ∃ z ∈ NB, ∃ w : H.Walk x₁ z, ∀ u ∈ w.support, u.1 ∈ W.support) := by
    intro x y W
    induction W with
    | nil hv =>
      intro hy
      exact ⟨fun h1 => (h1 (.inr hy)).elim, fun h1 => (disjoint_left.mp hAB h1 hy).elim⟩
    | @cons p q r e hl rest ih =>
      intro hy
      obtain ⟨ih1, ih2⟩ := ih hy
      have hup : ∀ u : S, u ∈ rest.support → u ∈ (GraphWalk.cons hl rest).support := fun u hu => by
        simp [GraphWalk.support, hu]
      have hpV : p ∈ G.V := hl.2.1
      have hqV : q ∈ G.V := hl.2.2.1
      have hE : (∃ x₁ ∈ NA, ∃ z ∈ NB, ∃ w : H.Walk x₁ z, ∀ u ∈ w.support, u.1 ∈ rest.support)
        → ∃ x₁ ∈ NA, ∃ z ∈ NB, ∃ w : H.Walk x₁ z, ∀ u ∈ w.support, u.1 ∈
          (GraphWalk.cons hl rest).support := by
        rintro ⟨x₁, h1, z, h2, w, hw⟩
        exact ⟨x₁, h1, z, h2, w, fun u hu => hup _ (hw u hu)⟩
      by_cases hqB : q ∈ B
      · refine ⟨fun hp => .inl ⟨hpV, ⟨p, hpV⟩, ⟨hp, q, hqB, e, hl⟩, .nil, fun u hu => ?_⟩,
          fun hp => (hdirect ⟨p, hp, q, hqB, e, hl⟩).elim⟩
        rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hu
        subst hu
        simp [GraphWalk.support]
      by_cases hqA : q ∈ A
      · exact ⟨fun _ => .inr (hE (ih2 hqA)), fun _ => hE (ih2 hqA)⟩
      have hq : q ∉ A ∪ B := fun h => h.elim hqA hqB
      constructor
      · intro hp
        rcases ih1 hq with ⟨hq', z, hz, w, hw⟩ | hE'
        · left
          by_cases hpq : p = q
          · subst hpq
            exact ⟨hpV, z, hz, w, fun u hu => hup _ (hw u hu)⟩
          · have hadj : H.Adj ⟨p, hpV⟩ ⟨q, hqV⟩ := ⟨fun h => hpq (congrArg Subtype.val h), hp, hq,
              e, hl⟩
            refine ⟨hpV, z, hz, .cons hadj w, fun u hu => ?_⟩
            rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hu
            rcases hu with rfl | hu
            · simp [GraphWalk.support]
            · exact hup _ (hw u hu)
        · exact .inr (hE hE')
      · intro hp
        rcases ih1 hq with ⟨hq', z, hz, w, hw⟩ | hE'
        · exact ⟨⟨q, hqV⟩, ⟨hq, p, hp, e, hl⟩, z, hz, w, fun u hu => hup _ (hw u hu)⟩
        · exact hE hE'
  have hMenger : HasDisjointPaths H NA NB (v + 1) := by
    refine Menger.exists_disjointPaths H NA NB hfin (v + 1) fun T hT => ?_
    by_contra hlt
    have hTc : T.ncard ≤ v := by omega
    let T' : Set G.V := T ∩ {x | x.1 ∉ A ∪ B}
    have hT'c : (Subtype.val '' T').ncard ≤ v := by
      rw [ncard_image_of_injective _ Subtype.val_injective]
      exact (ncard_le_ncard inter_subset_left (toFinite T)).trans hTc
    obtain ⟨a, ha, b, hb, W, hW⟩ := h (Subtype.val '' T')
      (by rintro _ ⟨x, -, rfl⟩; exact x.2) (disjoint_left.mpr fun z hz => by
      obtain ⟨x, hx, rfl⟩ := hz
      exact hx.2) hT'c
    obtain ⟨x₁, hx₁, z, hz, w, hw⟩ := (key W hb).2 ha
    obtain ⟨u, hu, huT⟩ := hT ⟨x₁, z, w.bypass, w.bypass_isPath, hx₁, hz⟩
    have hu' := w.support_bypass_subset_support hu
    exact hW u.1 (hw u hu') ⟨u, ⟨huT, hoff w hx₁.1 u hu'⟩, rfl⟩
  have hlift : ∀ {p q : G.V} (w : H.Walk p q), ∃ W : GraphWalk G.toGraph p.1 q.1, W.support
    = w.support.map Subtype.val := by
    intro p q w
    induction w with
    | nil => exact ⟨.nil (Subtype.prop _), by simp [GraphWalk.support]⟩
    | cons h' _ ih =>
      obtain ⟨W, hW⟩ := ih
      obtain ⟨e, he⟩ := h'.2.2.2
      exact ⟨.cons he W, by simp [GraphWalk.support, hW]⟩
  obtain ⟨Q, hQ⟩ := hMenger
  have hbuild : ∀ i, ∃ (s t : S) (W : GraphWalk G.toGraph s t), s ∈ A ∧ t ∈ B ∧ W.IsSimple
    ∧ ∀ z ∈ W.support, z = s ∨ z = t ∨ ∃ u ∈ (Q i).walk.support, u.1 = z := by
    intro i
    obtain ⟨hx₁, a, ha, e, he⟩ := (Q i).first_mem
    obtain ⟨hz₁, b, hb, f, hf⟩ := (Q i).last_mem
    obtain ⟨W, hW⟩ := hlift (Q i).walk
    have hnd : W.support.Nodup := by
      rw [hW]
      exact (Q i).isPath.support_nodup.map Subtype.val_injective
    have hmem : ∀ z ∈ W.support, ∃ u ∈ (Q i).walk.support, u.1 = z := fun z hz => by
      rw [hW, List.mem_map] at hz
      exact hz
    have hnot : ∀ c, c ∈ A ∪ B → c ∉ W.support := fun c hc hc' => by
      obtain ⟨u, hu, rfl⟩ := hmem c hc'
      exact hoff (Q i).walk hx₁ u hu hc
    have hab : a ≠ b := fun h => disjoint_left.mp hAB ha (h ▸ hb)
    let W₁ : GraphWalk G.toGraph (Q i).last.1 b := .cons hf (.nil hf.2.2.1)
    have hsup : (GraphWalk.cons he (W.append W₁)).support = a :: (W.support ++ [b]) := by
      change a :: (W.append W₁).support = _
      rw [GraphWalk.support_append]
      rfl
    refine ⟨a, b, .cons he (W.append W₁), ha, hb, ?_, fun z hz => ?_⟩
    · rw [GraphWalk.IsSimple, hsup, List.nodup_cons, List.nodup_append]
      refine ⟨fun h => ?_, hnd, by simp, fun x hx y hy e => ?_⟩
      · rcases List.mem_append.mp h with h | h
        · exact hnot a (.inl ha) h
        · exact hab (List.mem_singleton.mp h)
      · rw [List.mem_singleton] at hy
        exact hnot b (.inr hb) ((e.trans hy) ▸ hx)
    · rw [hsup, List.mem_cons, List.mem_append, List.mem_singleton] at hz
      rcases hz with h | h | h
      · exact .inl h
      · exact .inr (.inr (hmem z h))
      · exact .inr (.inl h)
  choose s t W hs ht hW hWm using hbuild
  refine ⟨fun i => walkDrawing G (W i), s, t, fun i => ⟨walkDrawing_isSubdrawing G _, hs i, ht i,
    walkDrawing_isPathBetween G (hW i)⟩, fun i j hij => ?_⟩
  rw [disjoint_left]
  rintro z ⟨h1, h2⟩ ⟨h3, h4⟩
  rw [walkDrawing_V] at h1 h3
  have hne1 : z ≠ s i ∧ z ≠ t i := ⟨fun h => h2 (.inl h), fun h => h2 (.inr h)⟩
  have hne2 : z ≠ s j ∧ z ≠ t j := ⟨fun h => h4 (.inl h), fun h => h4 (.inr h)⟩
  obtain ⟨u, hu, e⟩ := ((hWm i z h1).resolve_left hne1.1).resolve_left hne1.2
  obtain ⟨u', hu', e'⟩ := ((hWm j z h3).resolve_left hne2.1).resolve_left hne2.2
  obtain rfl : u = u' := Subtype.ext (e.trans e'.symm)
  exact disjoint_left.mp (hQ hij) hu hu'

/-- **Graph Minors VII, (4.3)** (pages 222 and 223). -/
theorem cuffToRestDisjointPaths : CuffToRestDisjointPathsStatement.{0} := by
  intro S _ _ hS hconn hcuff G v hG hnull C hC
  have hfin : (cuffs S).Finite := (cuff_statement.{0} S hS).2.1
  obtain ⟨C', hC', hne⟩ : ∃ C' ∈ cuffs S, C' ≠ C := exists_ne_of_one_lt_ncard hcuff C
  have hsubC : C ⊆ bd S := by
    obtain ⟨x, -, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  have hdis : Disjoint (G.V ∩ C) (G.V ∩ (bd S \ C)) := disjoint_left.mpr fun z h1 h2 => h2.2.2 h1.2
  obtain ⟨P, s, t, h1, h2⟩ := exists_paths_of_walks G hdis (v := v) fun X hXV hX hXc => by
    have hXb : Disjoint X (bd S) := disjoint_left.mpr fun z hz hb => by
      by_cases hzC : z ∈ C
      · exact disjoint_left.mp hX hz (.inl ⟨hXV hz, hzC⟩)
      · exact disjoint_left.mp hX hz (.inr ⟨hXV hz, hb, hzC⟩)
    exact exists_walk_avoiding hS hG hnull hC hC' hne.symm hXV hXb hXc
  exact ⟨P, s, t, fun i => ⟨(h1 i).1, (h1 i).2.1.2, (h1 i).2.2.1.2, (h1 i).2.2.2⟩, h2⟩

/-- Graph Minors VII, (4.3) (pages 222–223):
"(4.3) *Let $\Sigma$ be a connected surface with at least two cuffs, and let $G$ be a proper graph
in $\Sigma$. Let $v \ge 0$ be an integer, and suppose that every $G$-normal $O$-arc $F$ with
$F \cap bd(\Sigma) = \emptyset$ and $|V(G) \cap F| \le v$ is null-homotopic. Let $C$ be a cuff.
Then there are at least $v + 1$ paths of $G$, each with one end in $C$ and the other in
$bd(\Sigma) - C$, mutually vertex-disjoint except for their ends.*" -/
theorem theorem_4_3_proof {S : Type} [TopologicalSpace S] [T1Space S]
  (hS : IsSurface S) [hConn : ConnectedSpace S]
    (hcuffs : 2 ≤ (cuffs S).ncard) (G : Drawing S) (v : ℕ) (hG : G.IsProper)
    (hNull : ∀ F : Set S, G.IsNormal F → IsOArc F → F ∩ bd S = ∅ → (G.V ∩ F).ncard ≤ v →
      IsNullHomotopicOArc F)
    {C : Set S} (hC : C ∈ cuffs S) :
    ∃ (P : Fin (v + 1) → Drawing S) (s t : Fin (v + 1) → S),
      (∀ i : Fin (v + 1), (P i).IsSubdrawing G ∧ s i ∈ C ∧ t i ∈ bd S \ C ∧
        (P i).IsPathBetween (s i) (t i)) ∧
      (∀ i j : Fin (v + 1), i ≠ j →
        Disjoint ((P i).V \ {s i, t i}) ((P j).V \ {s j, t j})) :=
  cuffToRestDisjointPaths S hS hConn hcuffs G v hG hNull C hC

/-- The first step of the proof of (4.6) of Graph Minors VII (pages 224 and 225): for a vertex `z`
on a cuff `C` there are many
paths from `z` to the rest of `bd(Σ)`, disjoint except for their ends. As in the paper, let `G'` be
the graph obtained from `G` by
deleting every vertex of `G` in `C` except `z`, and apply (4.3) to `G'`. Its hypothesis holds for
`G'`: a `G'`-normal `O`-arc `F'`
off `bd(Σ)` that meets few vertices of `G'` is null-homotopic. The paper shows this by moving `F'`
to a `G`-normal `O`-arc `F`
with `V(G) ∩ F ⊆ (V(G') ∩ F') ∪ ((V(G) ∩ C) - {z})` and applying hypothesis (ii) of (4.6) to `F`; it
says the move "is easy to
see". We do not move `F'`. The set off `U(G)` and `bd(Σ)`, with these vertices added, is flat, since
each `O`-arc in it is such
an `F`, and the paper's last lines apply to it. It stays flat when the edges at these vertices are
added
(`isFlat_union_edges`), and that set contains `F'`. -/
theorem exists_paths_from_vertex (hS : IsSurface S) [ConnectedSpace S] {G : Drawing S}
  (hG : G.IsProper) {n : ℕ}
    (hnull : ∀ B : Set S, G.IsNormal B → IsOArc B → (G.V ∩ B).ncard ≤ n → IsNullHomotopicOArc B
      ∨ ∃ C ∈ cuffs S, IsNullHomotopicOArcInCappedCuff C B ∧ G.V ∩ C ⊆ B)
    (hthree : ∀ C ∈ cuffs S, (G.V ∩ C).Nonempty) {C C' : Set S} (hC : C ∈ cuffs S)
      (hC' : C' ∈ cuffs S) (hne : C ≠ C') {z : S} (hzV : z ∈ G.V) (hzC : z ∈ C) {m : ℕ} (hm : m +
        (G.V ∩ C).ncard ≤ n) :
    ∃ (P : Fin (m + 1) → Drawing S) (s t : Fin (m + 1) → S), (∀ i, (P i).IsSubdrawing G ∧ s i = z
      ∧ t i ∈ G.V ∩ (bd S \ C) ∧ (P i).IsPathBetween (s i) (t i)) ∧
      ∀ i j, i ≠ j → Disjoint ((P i).V \ {s i, t i}) ((P j).V \ {s j, t j}) := by
  classical
  have hsubC : C ⊆ bd S := by
    obtain ⟨x, -, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  -- `G'`: delete every vertex of `G` in `C` except `z`.
  let D : Set S := (G.V ∩ C) \ {z}
  obtain ⟨G', hG's, hG'V, hG'E⟩ := exists_sub (K := G) (V' := G.V \ D)
    (E' := {e | e ∈ G.E ∧ Disjoint (closure e) D}) sdiff_subset (fun e he => he.1)
    fun e he y hy => ⟨hy.2, fun hyD => disjoint_left.mp he.2 hy.1 hyD⟩
  have hG'p : G'.IsProper := fun y hy => by
    have hyG : y ∈ G.V := hG ⟨hy.1, hG's.U_subset hy.2⟩
    have h := hy.2
    rw [G'.U_eq] at h
    rcases h with h | h
    · exact h
    · obtain ⟨e, he, hye⟩ := mem_iUnion₂.mp h
      have he' : e ∈ G.E ∧ Disjoint (closure e) D := by
        rw [hG'E] at he
        exact he
      rw [hG'V]
      exact ⟨hyG, fun hyD => disjoint_left.mp he'.2 hye hyD⟩
  -- The hypothesis of (4.3) for `G'` with `m` in place of `v`.
  have hnull' : ∀ F : Set S, G'.IsNormal F → IsOArc F → F ∩ bd S = ∅ → (G'.V ∩ F).ncard ≤ m →
      IsNullHomotopicOArc F := by
    intro F' hF'n hF'O hF'b hF'c
    let X : Set S := G'.V ∩ F'
    have hXG : X ⊆ G.V := fun y hy => by
      have h := hy.1
      rw [hG'V] at h
      exact h.1
    let X' : Set S := X ∪ D
    have hX'V : X' ⊆ G.V := union_subset hXG fun y hy => hy.1.1
    have hX'f : X'.Finite := G.finite_V.subset hX'V
    have hzX' : z ∉ X' := by
      rintro (h | h)
      · exact (eq_empty_iff_forall_notMem.mp hF'b) z ⟨h.2, hsubC hzC⟩
      · exact h.2 rfl
    have hflat : IsFlat (offSet G ∪ X') := by
      refine isFlat_of_forall_isNullHomotopicOArc hS fun F hF hO => ?_
      have hsub : G.V ∩ F ⊆ X' := fun y hy => by
        rcases hF hy.2 with h | h
        · exact ((mem_offSet.mp h).1 (G.V_subset_U hy.1)).elim
        · exact h
      have hnorm : G.IsNormal F := by
        rintro y ⟨hyF, hyU⟩
        rcases hF hyF with h | h
        · exact ((mem_offSet.mp h).1 hyU).elim
        · exact hX'V h
      have hcard : (G.V ∩ F).ncard ≤ n := by
        refine (ncard_le_ncard hsub hX'f).trans ?_
        have h3 : X'.ncard ≤ X.ncard + D.ncard := ncard_union_le _ _
        have h4 : D.ncard ≤ (G.V ∩ C).ncard := ncard_le_ncard sdiff_subset
          (G.finite_V.subset inter_subset_left)
        have h5 : X.ncard ≤ m := hF'c
        omega
      -- The last lines of the paper's argument on page 225.
      rcases hnull F hnorm hO hcard with h | ⟨C₁, hC₁, -, hsubF⟩
      · exact h
      · exfalso
        by_cases heq : C₁ = C
        · subst heq
          exact hzX' (hsub ⟨hzV, hsubF ⟨hzV, hzC⟩⟩)
        · obtain ⟨y, hyV, hyC⟩ := hthree C₁ hC₁
          have hyb : y ∈ bd S \ C := by
            refine ⟨?_, fun h => heq (GM17.cuffs_disjoint_eq hC₁ hC hyC h)⟩
            obtain ⟨x, -, rfl⟩ := hC₁
            exact connectedComponentIn_subset _ _ hyC
          rcases hsub ⟨hyV, hsubF ⟨hyV, hyC⟩⟩ with h | h
          · exact (eq_empty_iff_forall_notMem.mp hF'b) y ⟨h.2, hyb.1⟩
          · exact hyb.2 h.1.2
    have hflat2 := isFlat_union_edges hS hG hX'V hflat
    obtain ⟨φ⟩ := hF'O
    refine ⟨φ, hflat2 ⟨fun x => (φ x).1, continuous_subtype_val.comp φ.continuous⟩ ?_⟩
    rintro _ ⟨x, rfl⟩
    have hyF : (φ x).1 ∈ F' := (φ x).2
    set y := (φ x).1
    have hyb : y ∉ bd S := fun h => (eq_empty_iff_forall_notMem.mp hF'b) y ⟨hyF, h⟩
    by_cases hyU : y ∈ G.U
    · rw [G.U_eq] at hyU
      by_cases hyV : y ∈ G.V
      · by_cases hyD : y ∈ D
        · exact .inl (.inr (.inr hyD))
        · have hyG' : y ∈ G'.V := by
            rw [hG'V]
            exact ⟨hyV, hyD⟩
          exact .inl (.inr (.inl ⟨hyG', hyF⟩))
      · rcases hyU with h | h
        · exact (hyV h).elim
        obtain ⟨e, he, hye⟩ := mem_iUnion₂.mp h
        have hye' : y ∈ e := by
          rw [← G.closure_diff_V he]
          exact ⟨hye, hyV⟩
        by_cases hd : Disjoint (closure e) D
        · have heG' : e ∈ G'.E := by
            rw [hG'E]
            exact ⟨he, hd⟩
          have hyG'V := hF'n ⟨hyF, G'.closure_subset_U heG' hye⟩
          exact (hyV (hG's.1 hyG'V)).elim
        · refine .inr ⟨e, ⟨he, fun hd' => hd (hd'.mono_right subset_union_right)⟩, hye'⟩
    · exact .inl (.inl (mem_offSet.mpr ⟨hyU, hyb⟩))
  -- (4.3) applied to `G'`.
  have hcuffs : 2 ≤ (cuffs S).ncard := by
    have hfin : (cuffs S).Finite := (cuff_statement.{0} S hS).2.1
    calc 2 = ({C, C'} : Set (Set S)).ncard := (ncard_pair hne).symm
      _ ≤ (cuffs S).ncard := ncard_le_ncard (insert_subset hC (singleton_subset_iff.mpr hC')) hfin
  obtain ⟨P, s, t, h1, h2⟩ := theorem_4_3_proof hS hcuffs G' m hG'p hnull' hC
  refine ⟨P, s, t, fun i => ?_, h2⟩
  obtain ⟨hPs, hsC, htC, hpath⟩ := h1 i
  obtain ⟨W, hWs, hWV, hWE⟩ := hpath
  have hsP : s i ∈ (P i).V := hWV ▸ W.start_mem_support
  have htP : t i ∈ (P i).V := hWV ▸ W.end_mem_support
  have hsG' : s i ∈ G'.V := hPs.1 hsP
  have htG' : t i ∈ G'.V := hPs.1 htP
  rw [hG'V] at hsG' htG'
  refine ⟨IsSubdrawing.trans' hPs hG's, ?_, ⟨htG'.1, htC⟩, ⟨W, hWs, hWV, hWE⟩⟩
  by_contra hsz
  exact hsG'.2 ⟨⟨hsG'.1, hsC⟩, hsz⟩

end GraphMinor.GM07
