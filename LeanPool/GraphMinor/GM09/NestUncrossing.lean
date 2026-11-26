/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.GM09.Basic
public import LeanPool.GraphMinor.GM09.NestEdgeCount
public import LeanPool.GraphMinor.GM09.PlanarNests
public import LeanPool.GraphMinor.GM09.GraphCircuits
import LeanPool.GraphMinor.GM09.Section3a
import LeanPool.GraphMinor.GM09.Section11b
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.PlaneDisc

/-!
# The Nest-and-Paths Uncrossing Argument (Graph Minors III, Theorem (4.1))

This file formalizes the uncrossing argument from the proof of **Graph Minors III, Theorem (4.1)**
(pages 59–61), which is used both in **Graph Minors IX, (10.1)** (page 64: *"The proof of (10.1) is
very similar to the proof of [2, Theorem (4.1)], and we omit it."*) and in **Graph Minors XIV,
(9.5), Claim (3)** (page 46: *"By [1, theorem (4.1)], or rather by the proof of that theorem, we
deduce from (1) and (2) that (3)..."*).

Following the proof of Graph Minors III, (4.1) step by step:
1. **Circuit splitting and joining (`IsGraphCircuit.exists_two_paths`,
   `isGraphCircuit_subgraphUnion`)**: any circuit `C` and distinct vertices `v, v' ∈ V(C)` decompose
   `C` into two edge-disjoint paths `Q₁, Q₂` between `v` and `v'` with `V(Q₁) ∩ V(Q₂) = {v, v'}` and
   `Q₁ ∪ Q₂ = C`; conversely, two internally vertex-disjoint and edge-disjoint paths between `v` and
   `v'` form a circuit.
2. **Walk and path intersection decomposition (`path_inter_isPath_or_exists_shorter_subpath`,
   `exists_detour_of_inter_not_path`)**:
   - If a path `P` starts at `a ∈ V(C)` and `C ∩ P` is not a path, then taking the first edge
     `e ∈ E(P) \ E(C)` (whose left endpoint lies in `V(C)`) yields a shorter subpath `P' ≤ P` from
     `V(C)` to the other end of `P` that avoids `e`.
   - More generally, if `(V(C) ∩ V(P)).Nonempty` and `C ∩ P` is not a path, then there is a detour
     subpath `P_sub ≤ P` between distinct vertices `v, v' ∈ V(C) ∩ V(P)` with
     `V(P_sub) ∩ V(C) = {v, v'}`, `Disjoint E(P_sub) E(C)`, and a first edge `e ∈ E(P_sub)` incident
     with `v ∈ V(C)`.
3. **Edge-count minimization (`totalUnionEdges`, `exists_min_totalUnionEdges`)**: among all valid
   pairs `(C, P)` of an `s`-nest `C` and a family `P` of `r` vertex-disjoint paths, choose `(C, P)`
   minimizing `|E(C₁ ∪ ⋯ ∪ C_s ∪ P₁ ∪ ⋯ ∪ P_r)|` (Condition `(1)`).
4. **Boundary shortening move (`totalUnionEdges_lt_of_replace_subpath`)**: replacing `P_i` by a
   subpath `P'_i ≤ P_i` omitting an edge `e ∈ E(P_i)` incident with `V(C_j)` and not in `E(C_j)`
   strictly decreases `totalUnionEdges C P`.
5. **Outer detour move (`totalUnionEdges_lt_of_replace_circuit`)**: replacing `C_j` by
   `P_sub ∪ Q₁` when `P_sub ≤ P_i` is an outer detour between `v, v' ∈ V(C_j)` and `Q₂` has an edge
   `e₀` not in `⋃_k E(P_k)` strictly decreases `totalUnionEdges C P`, establishing Property `(2)`
   (`subpath_to_outer_no_edges_outside`).
6. **Inner detour move (`reroute_path_along_arc`, `disjoint_other_paths_of_no_escape_from_arc`,
   `totalUnionEdges_lt_of_reroute_path`)**: when `P_sub ≤ P_i` is an inner detour between
   `v, v' ∈ V(C_j)` and no path inside `C_j` avoiding `V(P_sub)` connects `V(Q_k)` to the
   inner/outer
   target, Property `(2)` implies `Disjoint V(Q_k) V(P_{i'})` for all `i' ≠ i`; rerouting `P_i`
   through `Q_k` without `E(P_sub)` preserves pairwise vertex-disjointness of `P` and omits the
   first
   edge `e₁ ∈ E(P_sub)` (which lies in no `E(C_m)`), strictly decreasing `totalUnionEdges C P`.
7. **Master uncrossing theorem (`nest_uncrossing`, `theorem_10_1`)**: combining these steps proves
   that at a minimum-edge configuration `(C, P)`, every intersection `P_i ∩ C_j` is a path.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Graph GraphMinor GraphMinor.Surface
open PlanarNests (exists_first_hit_split not_isLink_self_of_mem_edges_of_isSimple)

universe u v

variable {α : Type u} {β : Type v}

/-! ## 2. Combinatorial Structure of `C ∩ P`: Prefix Paths, Shorter Subpaths, and Detours -/

/-- If `e` is an edge of `G` with an endpoint `u ∈ V(C j)`, `e ∉ E(C j)`, and `C` is a pairwise
vertex-disjoint family of subgraphs of `G`, then `e ∉ E(C m)` for all `m`. -/
theorem not_mem_edgeSet_of_endpoint_mem_disjoint_family {s : ℕ} {G : Graph α β}
    {C : Fin s → Graph α β} (hCG : ∀ m, C m ≤ G)
    (hC_disj : Pairwise (fun m₁ m₂ => Disjoint V(C m₁) V(C m₂)))
    {j : Fin s} {e : β} {u w : α} (hl : G.IsLink e u w)
    (hu : u ∈ V(C j)) (he_not : e ∉ E(C j)) :
    ∀ m : Fin s, e ∉ E(C m) := by
  intro m hm
  by_cases hmj : m = j
  · exact he_not (hmj ▸ hm)
  · have hCm_link : (C m).IsLink e u w := ((hCG m).isLink_iff hm).mpr hl
    exact disjoint_left.mp (hC_disj hmj) hCm_link.left_mem hu

private theorem inter_walk_nil_path {G C : Graph α β} (hCG : C ≤ G)
    {a : α} (ha : a ∈ V(C)) (haG : a ∈ V(G)) :
    IsGraphPathWithEnds G (subgraphInter G C (walkSubgraph (GraphWalk.nil haG))) a a := by
  have heq : subgraphInter G C (walkSubgraph (GraphWalk.nil haG)) =
      walkSubgraph (GraphWalk.nil haG) := by
    refine (Compatible.of_le_le (subgraphInter_le hCG) (walkSubgraph_le _)).ext ?_ ?_
    · rw [vertexSet_subgraphInter, vertexSet_walkSubgraph]
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.support_nil, List.mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ ha, h⟩⟩
    · rw [edgeSet_subgraphInter hCG (walkSubgraph_le _), edgeSet_walkSubgraph]
      simp
  rw [heq]
  exact isGraphPathWithEnds_walkSubgraph (List.nodup_singleton a)

private theorem inter_walk_cons_path {G C : Graph α β} (hCG : C ≤ G)
    {a w b u : α} {e : β} {hl : G.IsLink e a w} {r : GraphWalk G w b}
    (ha : a ∈ V(C)) (heC : e ∈ E(C)) (ha_not_r : a ∉ r.support)
    (hpath_r : IsGraphPathWithEnds G (subgraphInter G C (walkSubgraph r)) w u) :
    IsGraphPathWithEnds G (subgraphInter G C (walkSubgraph (GraphWalk.cons hl r))) a u := by
  obtain ⟨hsub_r, W_r, hW_r_s, hV_r, hE_r⟩ := hpath_r
  obtain ⟨W_r_G, hs_r, he_r⟩ := exists_walk_up_of_le hsub_r W_r
  have ha_not_Wr : a ∉ W_r_G.support := by
    intro ha_in
    rw [hs_r] at ha_in
    have ha_mem : a ∈ V(subgraphInter G C (walkSubgraph r)) := by
      rw [hV_r]; exact ha_in
    rw [vertexSet_subgraphInter, vertexSet_walkSubgraph] at ha_mem
    exact ha_not_r ha_mem.2
  have hW_cons_s : (GraphWalk.cons hl W_r_G).IsSimple :=
    List.nodup_cons.mpr ⟨ha_not_Wr, by rw [hs_r]; exact hW_r_s⟩
  have heq : subgraphInter G C (walkSubgraph (GraphWalk.cons hl r)) =
      walkSubgraph (GraphWalk.cons hl W_r_G) := by
    refine (Compatible.of_le_le (subgraphInter_le hCG) (walkSubgraph_le _)).ext ?_ ?_
    · rw [vertexSet_subgraphInter, vertexSet_walkSubgraph, vertexSet_walkSubgraph]
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.support_cons, List.mem_cons]
      constructor
      · rintro ⟨hxC, rfl | hxr⟩
        · exact Or.inl rfl
        · right
          rw [hs_r]
          have hx_in : x ∈ V(subgraphInter G C (walkSubgraph r)) := by
            rw [vertexSet_subgraphInter, vertexSet_walkSubgraph]
            exact ⟨hxC, hxr⟩
          rwa [hV_r] at hx_in
      · rintro (rfl | hxWr)
        · exact ⟨ha, Or.inl rfl⟩
        · rw [hs_r] at hxWr
          have hx_in : x ∈ V(subgraphInter G C (walkSubgraph r)) := by
            rw [hV_r]; exact hxWr
          rw [vertexSet_subgraphInter, vertexSet_walkSubgraph] at hx_in
          exact ⟨hx_in.1, Or.inr hx_in.2⟩
    · rw [edgeSet_subgraphInter hCG (walkSubgraph_le _), edgeSet_walkSubgraph,
        edgeSet_walkSubgraph]
      ext f
      simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.edges_cons, List.mem_cons]
      constructor
      · rintro ⟨hfC, rfl | hfr⟩
        · exact Or.inl rfl
        · right
          rw [he_r]
          have hf_in : f ∈ E(subgraphInter G C (walkSubgraph r)) := by
            rw [edgeSet_subgraphInter hCG (walkSubgraph_le r), edgeSet_walkSubgraph]
            exact ⟨hfC, hfr⟩
          rwa [hE_r] at hf_in
      · rintro (rfl | hfWr)
        · exact ⟨heC, Or.inl rfl⟩
        · rw [he_r] at hfWr
          have hf_in : f ∈ E(subgraphInter G C (walkSubgraph r)) := by
            rw [hE_r]; exact hfWr
          rw [edgeSet_subgraphInter hCG (walkSubgraph_le r), edgeSet_walkSubgraph] at hf_in
          exact ⟨hf_in.1, Or.inr hf_in.2⟩
  rw [heq]
  exact isGraphPathWithEnds_walkSubgraph hW_cons_s

private theorem inter_walk_first_vertex_path {G C : Graph α β} (hCG : C ≤ G)
    {a w b : α} {e : β} {hl : G.IsLink e a w} {r : GraphWalk G w b}
    (ha : a ∈ V(C)) (heC : e ∉ E(C)) (hhit' : ∀ x ∈ r.support, x ∉ V(C)) :
    IsGraphPathWithEnds G (subgraphInter G C (walkSubgraph (GraphWalk.cons hl r))) a a := by
  have haG : a ∈ V(G) := hl.left_mem
  have heq : subgraphInter G C (walkSubgraph (GraphWalk.cons hl r)) =
      walkSubgraph (GraphWalk.nil haG) := by
    refine (Compatible.of_le_le (subgraphInter_le hCG) (walkSubgraph_le _)).ext ?_ ?_
    · rw [vertexSet_subgraphInter, vertexSet_walkSubgraph, vertexSet_walkSubgraph]
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.support_cons, List.mem_cons,
        GraphWalk.support_nil, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨hxC, rfl | hxr⟩
        · rfl
        · exact (hhit' x hxr hxC).elim
      · rintro rfl
        exact ⟨ha, Or.inl rfl⟩
    · rw [edgeSet_subgraphInter hCG (walkSubgraph_le _), edgeSet_walkSubgraph,
        edgeSet_walkSubgraph]
      ext f
      simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.edges_cons, List.mem_cons,
        GraphWalk.edges_nil, List.not_mem_nil, iff_false, not_and]
      rintro hfC (rfl | hfr)
      · exact heC hfC
      · obtain ⟨x, y, hxyC⟩ := C.exists_isLink_of_mem_edgeSet hfC
        have hxyG : G.IsLink f x y := hxyC.mono hCG
        have hx_r : x ∈ r.support := r.left_mem_support_of_mem_edges hfr hxyG
        exact hhit' x hx_r hxyC.left_mem
  rw [heq]
  exact isGraphPathWithEnds_walkSubgraph (List.nodup_singleton a)

/-- Along a simple walk `W` in `G` starting at `a ∈ V(C)` (where `C ≤ G`), either:
1. `subgraphInter G C (walkSubgraph W)` is a path in `G` from `a` to some `u ∈ V(C)`, or
2. there is a first edge `e ∈ W.edges \ E(C)` whose left endpoint `u` lies in `V(C)` and after
   which `W` visits `V(C)` again at some vertex `v ∈ V(C)`, yielding a simple subwalk `W'` from `v`
   to `b` that does not use `e`. -/
theorem walk_inter_isPath_or_exists_shorter_subwalk {G C : Graph α β} (hCG : C ≤ G)
    {a b : α} (W : GraphWalk G a b) (hW : W.IsSimple) (ha : a ∈ V(C)) :
    (∃ u ∈ V(C), IsGraphPathWithEnds G (subgraphInter G C (walkSubgraph W)) a u) ∨
      (∃ u ∈ V(C), ∃ w : α, ∃ e ∈ W.edges, G.IsLink e u w ∧ e ∉ E(C) ∧
        ∃ v ∈ V(C), ∃ W' : GraphWalk G v b, W'.IsSimple ∧
          (∀ x ∈ W'.support, x ∈ W.support) ∧
          (∀ f ∈ W'.edges, f ∈ W.edges) ∧ e ∉ W'.edges) := by
  induction W with
  | @nil a haG =>
    left
    refine ⟨a, ha, ?_⟩
    exact inter_walk_nil_path hCG ha haG
  | @cons a w b e hl r ih =>
    have ha_not_r : a ∉ r.support := (List.nodup_cons.mp hW).1
    have hr_simple : r.IsSimple := (List.nodup_cons.mp hW).2
    have he_not_r : e ∉ r.edges := fun he_in =>
      ha_not_r (r.left_mem_support_of_mem_edges he_in hl)
    by_cases heC : e ∈ E(C)
    · have hlC : C.IsLink e a w := (hCG.isLink_iff heC).mpr hl
      have hwC : w ∈ V(C) := hlC.right_mem
      rcases ih hr_simple hwC with ⟨u, huC, hpath_r⟩ |
        ⟨u, huC, w', e', he'r, hl', he'C, v, hvC, W', hW's, hW'V, hW'E, he'W'⟩
      · left
        refine ⟨u, huC, ?_⟩
        exact inter_walk_cons_path hCG ha heC ha_not_r hpath_r
      · right
        exact ⟨u, huC, w', e', List.mem_cons_of_mem e he'r, hl', he'C, v, hvC, W', hW's,
          fun x hx => List.mem_cons_of_mem a (hW'V x hx),
          fun f hf => List.mem_cons_of_mem e (hW'E f hf), he'W'⟩
    · by_cases hhit : ∃ v ∈ r.support, v ∈ V(C)
      · right
        obtain ⟨v, hvr, hvC⟩ := hhit
        obtain ⟨r₁, r₂, hsplit⟩ := r.exists_append_of_mem hvr
        have hr₂_s : r₂.IsSimple := (isSimple_of_append (hsplit ▸ hr_simple)).2
        have hr₂_V : ∀ x ∈ r₂.support, x ∈ r.support := fun x hx => by
          rw [hsplit, GraphWalk.mem_support_append]
          exact Or.inr hx
        have hr₂_E : ∀ f ∈ r₂.edges, f ∈ r.edges := fun f hf => by
          rw [hsplit, GraphWalk.edges_append, List.mem_append]
          exact Or.inr hf
        refine ⟨a, ha, w, e, List.mem_cons_self, hl, heC, v, hvC, r₂, hr₂_s,
          fun x hx => List.mem_cons_of_mem a (hr₂_V x hx),
          fun f hf => List.mem_cons_of_mem e (hr₂_E f hf),
          fun he_in => he_not_r (hr₂_E e he_in)⟩
      · left
        have hhit' : ∀ x ∈ r.support, x ∉ V(C) := fun x hx hxC => hhit ⟨x, hx, hxC⟩
        refine ⟨a, ha, ?_⟩
        exact inter_walk_first_vertex_path hCG ha heC hhit'

/-- Path version of `walk_inter_isPath_or_exists_shorter_subwalk` (Graph Minors III, (4.1),
paragraph 2, page 60): if `P` is a path in `G` from `a ∈ V(C)` to `b` and `C ∩ P` is not a path,
then taking the first edge `e` of `P` not in `C` yields a subpath `P' ≤ P` from some `v ∈ V(C)` to
`b` not using `e`, where `e` has an endpoint `u ∈ V(C)`. -/
theorem path_inter_isPath_or_exists_shorter_subpath {G C P : Graph α β} (hCG : C ≤ G)
    {a b : α} (hP : IsGraphPathWithEnds G P a b) (ha : a ∈ V(C)) :
    (∃ u ∈ V(C), IsGraphPathWithEnds G (subgraphInter G C P) a u) ∨
      (∃ u ∈ V(C), ∃ w : α, ∃ e ∈ E(P), G.IsLink e u w ∧ e ∉ E(C) ∧
        ∃ v ∈ V(C), ∃ P' : Graph α β, P' ≤ P ∧ IsGraphPathWithEnds G P' v b ∧ e ∉ E(P')) := by
  obtain ⟨hPG, W, hW, hVP, hEP⟩ := hP
  obtain ⟨WG, hsG, heG⟩ := exists_walk_up_of_le hPG W
  have hWG_s : WG.IsSimple := by unfold GraphWalk.IsSimple; rw [hsG]; exact hW
  have hP_eq : P = walkSubgraph WG := by
    refine (Compatible.of_le_le hPG (walkSubgraph_le WG)).ext ?_ ?_
    · rw [hVP, vertexSet_walkSubgraph, hsG]
    · rw [hEP, edgeSet_walkSubgraph, heG]
  rcases walk_inter_isPath_or_exists_shorter_subwalk hCG WG hWG_s ha with
    ⟨u, huC, hpath⟩ | ⟨u, huC, w, e, heWG, hl, heC, v, hvC, W', hW's, hW'V, hW'E, heW'⟩
  · left
    exact ⟨u, huC, hP_eq.symm ▸ hpath⟩
  · right
    have heP : e ∈ E(P) := by rw [hEP, ← heG]; exact heWG
    let P' := walkSubgraph W'
    have hP'P : P' ≤ P := by
      rw [hP_eq, (Compatible.of_le_le (walkSubgraph_le W') (walkSubgraph_le WG)).le_iff,
        vertexSet_walkSubgraph, vertexSet_walkSubgraph, edgeSet_walkSubgraph, edgeSet_walkSubgraph]
      exact ⟨hW'V, hW'E⟩
    exact ⟨u, huC, w, e, heP, hl, heC, v, hvC, P', hP'P,
      isGraphPathWithEnds_walkSubgraph hW's, by rw [edgeSet_walkSubgraph]; exact heW'⟩

private theorem inter_or_detour_of_walk {G C : Graph α β} {v₀ b : α} (hCG : C ≤ G)
    (W₂ : GraphWalk G v₀ b) (hv₀C : v₀ ∈ V(C)) (hW₂s : W₂.IsSimple) :
    (∃ u ∈ V(C), IsGraphPathWithEnds G (subgraphInter G C (walkSubgraph W₂)) v₀ u) ∨
      ∃ v ∈ V(C), v ∈ W₂.support ∧ ∃ v' ∈ V(C), v' ∈ W₂.support ∧ v ≠ v' ∧
        ∃ P_sub : Graph α β, P_sub ≤ walkSubgraph W₂ ∧ IsGraphPathWithEnds G P_sub v v' ∧
          V(P_sub) ∩ V(C) = {v, v'} ∧ Disjoint E(P_sub) E(C) ∧
          ∃ e ∈ E(P_sub), ∃ w : α, G.IsLink e v w := by
  induction W₂ with
  | @nil a haG =>
    left
    refine ⟨a, hv₀C, ?_⟩
    exact inter_walk_nil_path hCG hv₀C haG
  | @cons a w b e hl r ih =>
    have ha_not_r : a ∉ r.support := (List.nodup_cons.mp hW₂s).1
    have hr_s : r.IsSimple := (List.nodup_cons.mp hW₂s).2
    by_cases heC : e ∈ E(C)
    · have hlC : C.IsLink e a w := (hCG.isLink_iff heC).mpr hl
      have hwC : w ∈ V(C) := hlC.right_mem
      rcases ih hwC hr_s with ⟨u, huC, hpath_r⟩ |
        ⟨v, hvC, hvr, v', hv'C, hv'r, hvv', P_sub, hP_sub_r, hP_sub_path, hVC, hEC, hex_e⟩
      · left
        refine ⟨u, huC, ?_⟩
        exact inter_walk_cons_path hCG hv₀C heC ha_not_r hpath_r
      · right
        have hr_le : walkSubgraph r ≤ walkSubgraph (GraphWalk.cons hl r) := by
          rw [(Compatible.of_le_le (walkSubgraph_le r) (walkSubgraph_le _)).le_iff,
            vertexSet_walkSubgraph, vertexSet_walkSubgraph,
            edgeSet_walkSubgraph, edgeSet_walkSubgraph]
          exact ⟨fun x hx => List.mem_cons_of_mem a hx, fun f hf => List.mem_cons_of_mem e hf⟩
        exact ⟨v, hvC, List.mem_cons_of_mem a hvr, v', hv'C, List.mem_cons_of_mem a hv'r,
          hvv', P_sub, hP_sub_r.trans hr_le, hP_sub_path, hVC, hEC, hex_e⟩
    · by_cases hhit : ∃ x ∈ r.support, x ∈ V(C)
      · right
        obtain ⟨v', hv'C, r₁, r₂, hsplit_r, hr₁_first⟩ := exists_first_hit_split r hhit
        have hr₁_s : r₁.IsSimple := (isSimple_of_append (hsplit_r ▸ hr_s)).1
        have ha_not_r₁ : a ∉ r₁.support := fun ha_in =>
          ha_not_r (hsplit_r ▸ (GraphWalk.mem_support_append r₁ r₂).mpr (Or.inl ha_in))
        have hcons_r₁_s : (GraphWalk.cons hl r₁).IsSimple :=
          List.nodup_cons.mpr ⟨ha_not_r₁, hr₁_s⟩
        have hav' : a ≠ v' := fun h => ha_not_r₁ (h ▸ r₁.end_mem_support)
        have hv'_r : v' ∈ r.support :=
          hsplit_r ▸ (GraphWalk.mem_support_append r₁ r₂).mpr (Or.inl r₁.end_mem_support)
        let P_sub := walkSubgraph (GraphWalk.cons hl r₁)
        have hP_sub_le : P_sub ≤ walkSubgraph (GraphWalk.cons hl r) := by
          rw [(Compatible.of_le_le (walkSubgraph_le _) (walkSubgraph_le _)).le_iff,
            vertexSet_walkSubgraph, vertexSet_walkSubgraph,
            edgeSet_walkSubgraph, edgeSet_walkSubgraph]
          refine ⟨fun x hx => ?_, fun f hf => ?_⟩
          · rcases List.mem_cons.mp hx with rfl | hx₁
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem a
                (hsplit_r ▸ (GraphWalk.mem_support_append r₁ r₂).mpr (Or.inl hx₁))
          · rcases List.mem_cons.mp hf with rfl | hf₁
            · exact List.mem_cons_self
            · refine List.mem_cons_of_mem e ?_
              rw [hsplit_r, GraphWalk.edges_append, List.mem_append]
              exact Or.inl hf₁
        have hr₁_no_edge : ∀ f ∈ r₁.edges, f ∉ E(C) := by
          intro f hf₁ hfC
          obtain ⟨x, y, hxyC⟩ := C.exists_isLink_of_mem_edgeSet hfC
          have hxyG : G.IsLink f x y := hxyC.mono hCG
          have hx_s : x ∈ r₁.support := r₁.left_mem_support_of_mem_edges hf₁ hxyG
          have hy_s : y ∈ r₁.support := r₁.left_mem_support_of_mem_edges hf₁ hxyG.symm
          have hxv' : x = v' := hr₁_first x hx_s hxyC.left_mem
          have hyv' : y = v' := hr₁_first y hy_s hxyC.right_mem
          subst hxv' hyv'
          exact not_isLink_self_of_mem_edges_of_isSimple r₁ hr₁_s hf₁ hxyG
        refine ⟨a, hv₀C, List.mem_cons_self, v', hv'C, List.mem_cons_of_mem a hv'_r, hav',
          P_sub, hP_sub_le, isGraphPathWithEnds_walkSubgraph hcons_r₁_s, ?_, ?_,
          ⟨e, by rw [edgeSet_walkSubgraph]; exact List.mem_cons_self, w, hl⟩⟩
        · rw [vertexSet_walkSubgraph]
          ext x
          simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.support_cons, List.mem_cons,
            mem_insert_iff, mem_singleton_iff]
          constructor
          · rintro ⟨rfl | hx₁, hxC⟩
            · exact Or.inl rfl
            · exact Or.inr (hr₁_first x hx₁ hxC)
          · rintro (rfl | rfl)
            · exact ⟨Or.inl rfl, hv₀C⟩
            · exact ⟨Or.inr r₁.end_mem_support, hv'C⟩
        · rw [edgeSet_walkSubgraph]
          refine disjoint_left.mpr fun f hf hfC => ?_
          rcases List.mem_cons.mp hf with rfl | hf₁
          · exact heC hfC
          · exact hr₁_no_edge f hf₁ hfC
      · left
        have hhit' : ∀ x ∈ r.support, x ∉ V(C) := fun x hx hxC => hhit ⟨x, hx, hxC⟩
        refine ⟨a, hv₀C, ?_⟩
        exact inter_walk_first_vertex_path hCG hv₀C heC hhit'

/-- If a path `P` in `G` meets `V(C)` (where `C ≤ G`), then either `subgraphInter G C P` is a path
in `G`, or there are distinct vertices `v, v' ∈ V(C) ∩ V(P)` and a detour subpath `P_sub ≤ P`
between `v` and `v'` such that `V(P_sub) ∩ V(C) = {v, v'}`, `Disjoint E(P_sub) E(C)`, and there is
an edge `e ∈ E(P_sub)` incident with `v`. -/
theorem isGraphPath_inter_or_exists_detour {G C P : Graph α β} (hCG : C ≤ G)
    {a b : α} (hP : IsGraphPathWithEnds G P a b) (hne : (V(C) ∩ V(P)).Nonempty) :
    IsGraphPath G (subgraphInter G C P) ∨
      ∃ v ∈ V(C) ∩ V(P), ∃ v' ∈ V(C) ∩ V(P), v ≠ v' ∧
        ∃ P_sub : Graph α β, P_sub ≤ P ∧ IsGraphPathWithEnds G P_sub v v' ∧
          V(P_sub) ∩ V(C) = {v, v'} ∧ Disjoint E(P_sub) E(C) ∧
          ∃ e ∈ E(P_sub), ∃ w : α, G.IsLink e v w := by
  obtain ⟨hPG, W, hW, hVP, hEP⟩ := hP
  obtain ⟨WG, hsG, heG⟩ := exists_walk_up_of_le hPG W
  have hWG_s : WG.IsSimple := by change WG.support.Nodup; rw [hsG]; exact hW
  have hP_eq : P = walkSubgraph WG := by
    refine (Compatible.of_le_le hPG (walkSubgraph_le WG)).ext ?_ ?_
    · rw [hVP, vertexSet_walkSubgraph, hsG]
    · rw [hEP, edgeSet_walkSubgraph, heG]
  have hne_W : ∃ x ∈ WG.support, x ∈ V(C) := by
    obtain ⟨x, hxC, hxP⟩ := hne
    rw [hVP, ← hsG] at hxP
    exact ⟨x, hxP, hxC⟩
  obtain ⟨v₀, hv₀C, W₁, W₂, hsplit, hW₁_first⟩ := exists_first_hit_split WG hne_W
  have hsp12 := isSimple_of_append (hsplit ▸ hWG_s)
  have hW₁_no_edge : ∀ f ∈ W₁.edges, f ∉ E(C) := by
    intro f hf hfC
    obtain ⟨x, y, hxyC⟩ := C.exists_isLink_of_mem_edgeSet hfC
    have hxyG : G.IsLink f x y := hxyC.mono hCG
    have hx_supp : x ∈ W₁.support := W₁.left_mem_support_of_mem_edges hf hxyG
    have hy_supp : y ∈ W₁.support := W₁.left_mem_support_of_mem_edges hf hxyG.symm
    have hxv₀ : x = v₀ := hW₁_first x hx_supp hxyC.left_mem
    have hyv₀ : y = v₀ := hW₁_first y hy_supp hxyC.right_mem
    subst hxv₀ hyv₀
    exact not_isLink_self_of_mem_edges_of_isSimple W₁ hsp12.1 hf hxyG
  have hinter_eq : subgraphInter G C P = subgraphInter G C (walkSubgraph W₂) := by
    rw [hP_eq, hsplit]
    refine (Compatible.of_le_le (subgraphInter_le hCG) (subgraphInter_le hCG)).ext ?_ ?_
    · rw [vertexSet_subgraphInter, vertexSet_subgraphInter, vertexSet_walkSubgraph,
        vertexSet_walkSubgraph]
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.mem_support_append]
      constructor
      · rintro ⟨hxC, hx₁ | hx₂⟩
        · rw [hW₁_first x hx₁ hxC]
          exact ⟨hv₀C, W₂.start_mem_support⟩
        · exact ⟨hxC, hx₂⟩
      · rintro ⟨hxC, hx₂⟩
        exact ⟨hxC, Or.inr hx₂⟩
    · rw [edgeSet_subgraphInter hCG (walkSubgraph_le _),
        edgeSet_subgraphInter hCG (walkSubgraph_le _), edgeSet_walkSubgraph, edgeSet_walkSubgraph]
      ext f
      simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.edges_append, List.mem_append]
      constructor
      · rintro ⟨hfC, hf₁ | hf₂⟩
        · exact (hW₁_no_edge f hf₁ hfC).elim
        · exact ⟨hfC, hf₂⟩
      · rintro ⟨hfC, hf₂⟩
        exact ⟨hfC, Or.inr hf₂⟩
  -- Now walk along `W₂` starting at `v₀ ∈ V(C)` until the first edge not in `E(C)` after which
  -- `W₂` hits `V(C)` again.
  suffices hW₂_claim :
      (∃ u ∈ V(C), IsGraphPathWithEnds G (subgraphInter G C (walkSubgraph W₂)) v₀ u) ∨
        ∃ v ∈ V(C), v ∈ W₂.support ∧ ∃ v' ∈ V(C), v' ∈ W₂.support ∧ v ≠ v' ∧
          ∃ P_sub : Graph α β, P_sub ≤ walkSubgraph W₂ ∧ IsGraphPathWithEnds G P_sub v v' ∧
            V(P_sub) ∩ V(C) = {v, v'} ∧ Disjoint E(P_sub) E(C) ∧
            ∃ e ∈ E(P_sub), ∃ w : α, G.IsLink e v w by
    rcases hW₂_claim with ⟨u, _, hpath⟩ |
      ⟨v, hvC, hvW₂, v', hv'C, hv'W₂, hvv', P_sub, hP_sub_W₂, hP_sub_path, hVC, hEC, hex_e⟩
    · left
      exact ⟨v₀, u, hinter_eq ▸ hpath⟩
    · right
      have hvP : v ∈ V(P) := by
        rw [hVP]
        change v ∈ W.support
        rw [← hsG, hsplit, GraphWalk.mem_support_append]
        exact Or.inr hvW₂
      have hv'P : v' ∈ V(P) := by
        rw [hVP]
        change v' ∈ W.support
        rw [← hsG, hsplit, GraphWalk.mem_support_append]
        exact Or.inr hv'W₂
      have hW₂_le_P : walkSubgraph W₂ ≤ P := by
        rw [hP_eq, hsplit,
          (Compatible.of_le_le (walkSubgraph_le W₂) (walkSubgraph_le (W₁.append W₂))).le_iff,
          vertexSet_walkSubgraph, vertexSet_walkSubgraph,
          edgeSet_walkSubgraph, edgeSet_walkSubgraph]
        refine ⟨fun x hx => ?_, fun e he => ?_⟩
        · change x ∈ (W₁.append W₂).support
          rw [GraphWalk.mem_support_append]
          exact Or.inr hx
        · change e ∈ (W₁.append W₂).edges
          rw [GraphWalk.edges_append, List.mem_append]
          exact Or.inr he
      exact ⟨v, ⟨hvC, hvP⟩, v', ⟨hv'C, hv'P⟩, hvv', P_sub, hP_sub_W₂.trans hW₂_le_P,
        hP_sub_path, hVC, hEC, hex_e⟩
  exact inter_or_detour_of_walk hCG W₂ hv₀C hsp12.2

/-! ## 3. Rerouting a Path Along a Circuit Arc -/

/-- If `P` is a path in `G` from `a` to `b`, `W_sub` is a contiguous subwalk of `P` between `v` and
`v'`, and `Q` is a path in `G` between `v` and `v'`, then `(P \ E(W_sub)) ∪ Q` contains a path `P'`
in `G` from `a` to `b` with `V(P') ⊆ V(P) ∪ V(Q)` and `E(P') ⊆ (E(P) \ E(P_sub)) ∪ E(Q)`. -/
theorem reroute_path_along_arc {G P P_sub Q : Graph α β} {a b v v' : α}
    (hP_decomp : ∃ P₁ P₂ : Graph α β,
      P₁ ≤ P ∧ P₂ ≤ P ∧
      IsGraphPathWithEnds G P₁ a v ∧ IsGraphPathWithEnds G P₂ v' b ∧
      Disjoint E(P₁) E(P_sub) ∧ Disjoint E(P₂) E(P_sub))
    (hQ : IsGraphPathWithEnds G Q v v') :
    ∃ P' : Graph α β,
      IsGraphPathWithEnds G P' a b ∧
      V(P') ⊆ V(P) ∪ V(Q) ∧
      E(P') ⊆ (E(P) \ E(P_sub)) ∪ E(Q) := by
  obtain ⟨P₁, P₂, hP₁P, hP₂P, hP₁, hP₂, hdisj₁, hdisj₂⟩ := hP_decomp
  obtain ⟨hP₁G, W₁, _, hV₁, hE₁⟩ := hP₁
  obtain ⟨hQG, WQ, _, hVQ, hEQ⟩ := hQ
  obtain ⟨hP₂G, W₂, _, hV₂, hE₂⟩ := hP₂
  obtain ⟨W₁G, hs₁, he₁⟩ := exists_walk_up_of_le hP₁G W₁
  obtain ⟨WQG, hsQ, heQ⟩ := exists_walk_up_of_le hQG WQ
  obtain ⟨W₂G, hs₂, he₂⟩ := exists_walk_up_of_le hP₂G W₂
  let W_all := W₁G.append (WQG.append W₂G)
  obtain ⟨P', hP'_path, hP'V, hP'E⟩ := exists_isGraphPathWithEnds_of_walk W_all
  refine ⟨P', hP'_path, ?_, ?_⟩
  · refine hP'V.trans fun x hx => ?_
    simp only [W_all, mem_ofPred_eq, GraphWalk.mem_support_append, hs₁, hsQ, hs₂] at hx
    rcases hx with hx₁ | hxQ | hx₂
    · exact Or.inl (hP₁P.vertexSet_mono (by rw [hV₁]; exact hx₁))
    · exact Or.inr (by rw [hVQ]; exact hxQ)
    · exact Or.inl (hP₂P.vertexSet_mono (by rw [hV₂]; exact hx₂))
  · refine hP'E.trans fun e he => ?_
    simp only [W_all, mem_ofPred_eq, GraphWalk.edges_append, List.mem_append,
      he₁, heQ, he₂] at he
    rcases he with he₁' | heQ' | he₂'
    · have heP₁ : e ∈ E(P₁) := by rw [hE₁]; exact he₁'
      exact Or.inl ⟨hP₁P.edgeSet_mono heP₁, disjoint_left.mp hdisj₁ heP₁⟩
    · exact Or.inr (by rw [hEQ]; exact heQ')
    · have heP₂ : e ∈ E(P₂) := by rw [hE₂]; exact he₂'
      exact Or.inl ⟨hP₂P.edgeSet_mono heP₂, disjoint_left.mp hdisj₂ heP₂⟩

/-! ## 4. From Circuit Intersections to Rerouting -/

/-- **Deduction from Property `(2)` (GM03 (4.1) paragraph 6, pages 60–61)**:
Suppose Property `(2)` holds at `j`: for every `i'` and every `v ∈ V(C j) ∩ V(P i')`, there is a
subpath `R ≤ P i'` from `v` to the target `Z` satisfying `InsidePred R`. If `Q_k ≤ C j` has the
property that no path `R` in `G` from `V(Q_k)` to `Z` avoiding `V(P_sub)` (where `P_sub ≤ P i`)
satisfies `InsidePred R`, then `V(Q_k)` is disjoint from `V(P i')` for every `i' ≠ i`. -/
theorem disjoint_other_paths_of_no_escape_from_arc {r : ℕ} {G C_j Q_k P_sub : Graph α β}
    {P : Fin r → Graph α β} {Z : Set α} {InsidePred : Graph α β → Prop}
    (hQ_k : Q_k ≤ C_j)
    {i : Fin r} (hP_sub : P_sub ≤ P i)
    (hP_disj : Pairwise (fun k₁ k₂ => Disjoint V(P k₁) V(P k₂)))
    (hProp2 : ∀ (i' : Fin r) (v : α), v ∈ V(C_j) ∩ V(P i') →
      ∃ z ∈ Z, ∃ R : Graph α β, R ≤ P i' ∧ IsGraphPathWithEnds G R v z ∧ InsidePred R)
    (hNoEscape : ¬ ∃ v ∈ V(Q_k), ∃ z ∈ Z, ∃ R : Graph α β,
      IsGraphPathWithEnds G R v z ∧ Disjoint V(R) V(P_sub) ∧ InsidePred R) :
    ∀ i' : Fin r, i' ≠ i → Disjoint V(Q_k) V(P i') := by
  intro i' hi'
  refine disjoint_left.mpr fun v hvQ hvPi' => ?_
  have hvCj : v ∈ V(C_j) := hQ_k.vertexSet_mono hvQ
  obtain ⟨z, hzZ, R, hR_le, hR_path, hR_in⟩ := hProp2 i' v ⟨hvCj, hvPi'⟩
  have hdisj_R : Disjoint V(R) V(P_sub) :=
    disjoint_of_subset hR_le.vertexSet_mono hP_sub.vertexSet_mono (hP_disj hi')
  exact hNoEscape ⟨v, hvQ, z, hzZ, R, hR_path, hdisj_R, hR_in⟩

/-- If `W₀` and `W` are simple walks in `G` with the same endpoints `a, b` and `W.edges ⊆ W₀.edges`,
then `W.support = W₀.support` and `W.edges = W₀.edges`. -/
theorem eq_of_isSimple_subwalk_edges {G : Graph α β} {a b : α}
    (W₀ W : GraphWalk G a b) (hW₀ : W₀.IsSimple) (hW : W.IsSimple)
    (hedges : ∀ e ∈ W.edges, e ∈ W₀.edges) :
    W.support = W₀.support ∧ W.edges = W₀.edges := by
  induction W₀ with
  | @nil a ha =>
    cases W with
    | nil _ => exact ⟨rfl, rfl⟩
    | @cons _ w _ e hl r =>
      exact (List.not_mem_nil (hedges e List.mem_cons_self)).elim
  | @cons a y b e₀ hl₀ r₀ ih =>
    have ha_not_r₀ : a ∉ r₀.support := (List.nodup_cons.mp hW₀).1
    have hr₀ : r₀.IsSimple := (List.nodup_cons.mp hW₀).2
    have hab : a ≠ b := fun h => ha_not_r₀ (h ▸ r₀.end_mem_support)
    cases W with
    | nil _ => exact (hab rfl).elim
    | @cons _ w _ e hl r =>
      have ha_not_r : a ∉ r.support := (List.nodup_cons.mp hW).1
      have hr : r.IsSimple := (List.nodup_cons.mp hW).2
      have he_mem : e ∈ (GraphWalk.cons hl₀ r₀).edges := hedges e List.mem_cons_self
      have he₀_mem : e₀ ∈ (GraphWalk.cons hl₀ r₀).edges := List.mem_cons_self
      have he_eq : e = e₀ :=
        unique_inc_first hW₀ he_mem he₀_mem ⟨w, hl⟩ ⟨y, hl₀⟩
      subst he_eq
      have hwy : w = y := by
        rcases hl.right_eq_or_eq hl₀ with rfl | rfl
        · exact (ha_not_r r.start_mem_support).elim
        · rfl
      subst hwy
      have hr_edges : ∀ f ∈ r.edges, f ∈ r₀.edges := by
        intro f hf
        have hf_mem := hedges f (List.mem_cons_of_mem _ hf)
        rcases List.mem_cons.mp hf_mem with rfl | hf_r₀
        · exact (ha_not_r (r.left_mem_support_of_mem_edges hf hl₀)).elim
        · exact hf_r₀
      obtain ⟨hsupp, hed⟩ := ih r hr₀ hr hr_edges
      exact ⟨congrArg (List.cons a) hsupp, congrArg (List.cons e) hed⟩

/-- If `W₁.append W₂` is a simple walk in `G` and `W` is a simple walk in `G` between `x, y ∈
W₂.support`
with `W.edges ⊆ (W₁.append W₂).edges`, then `W.edges ⊆ W₂.edges`. -/
theorem edges_subset_right_of_append {G : Graph α β} {a u b x y : α}
    (W₁ : GraphWalk G a u) (W₂ : GraphWalk G u b)
    (hW₁₂ : (W₁.append W₂).IsSimple)
    (W : GraphWalk G x y) (hW : W.IsSimple)
    (hx : x ∈ W₂.support) (hy : y ∈ W₂.support)
    (hedges : ∀ e ∈ W.edges, e ∈ (W₁.append W₂).edges) :
    ∀ e ∈ W.edges, e ∈ W₂.edges := by
  induction W₁ with
  | nil _ => exact hedges
  | @cons a w u e₀ hl₀ r₁ ih =>
    have hcons : ((GraphWalk.cons hl₀ r₁).append W₂) = GraphWalk.cons hl₀ (r₁.append W₂) := rfl
    rw [hcons] at hW₁₂ hedges
    have ha_not : a ∉ (r₁.append W₂).support := (List.nodup_cons.mp hW₁₂).1
    have hr₁₂ : (r₁.append W₂).IsSimple := (List.nodup_cons.mp hW₁₂).2
    have hx_r₁₂ : x ∈ (r₁.append W₂).support :=
      (GraphWalk.mem_support_append r₁ W₂).mpr (Or.inr hx)
    have hy_r₁₂ : y ∈ (r₁.append W₂).support :=
      (GraphWalk.mem_support_append r₁ W₂).mpr (Or.inr hy)
    have hxa : x ≠ a := fun h => ha_not (h ▸ hx_r₁₂)
    have hya : y ≠ a := fun h => ha_not (h ▸ hy_r₁₂)
    have he₀_not_W : e₀ ∉ W.edges := by
      intro he₀W
      have haW : a ∈ W.support := W.left_mem_support_of_mem_edges he₀W hl₀
      obtain ⟨W_l, W_r, hsplit⟩ := W.exists_append_of_mem haW
      have hnd_E : (W_l.edges ++ W_r.edges).Nodup := by
        have h1 : W.edges.Nodup := hW.edges_nodup
        rwa [hsplit, GraphWalk.edges_append] at h1
      have hd_E := List.nodup_append.mp hnd_E
      have hex_l : ∃ e₁ ∈ W_l.edges, G.Inc e₁ a := by
        have hrev : W_l.reverse.edges = W_l.edges.reverse := GraphWalk.edges_reverse W_l
        cases hWl_rev : W_l.reverse with
        | nil _ =>
          have hmem : x ∈ (W_l.reverse).support := by
            rw [GraphWalk.support_reverse, List.mem_reverse]
            exact W_l.start_mem_support
          rw [hWl_rev] at hmem
          exact (hxa (List.mem_singleton.mp hmem)).elim
        | @cons _ z _ e₁ hl₁ r_l =>
          refine ⟨e₁, ?_, z, hl₁⟩
          have : e₁ ∈ W_l.reverse.edges := by rw [hWl_rev]; exact List.mem_cons_self
          rwa [hrev, List.mem_reverse] at this
      have hex_r : ∃ e₂ ∈ W_r.edges, G.Inc e₂ a := by
        cases W_r with
        | nil _ => exact (hya rfl).elim
        | @cons _ z _ e₂ hl₂ r_r => exact ⟨e₂, List.mem_cons_self, z, hl₂⟩
      obtain ⟨e₁, he₁, hinc₁⟩ := hex_l
      obtain ⟨e₂, he₂, hinc₂⟩ := hex_r
      have he₁_in : e₁ ∈ (GraphWalk.cons hl₀ (r₁.append W₂)).edges :=
        hedges e₁ (by rw [hsplit, GraphWalk.edges_append, List.mem_append]; exact Or.inl he₁)
      have he₂_in : e₂ ∈ (GraphWalk.cons hl₀ (r₁.append W₂)).edges :=
        hedges e₂ (by rw [hsplit, GraphWalk.edges_append, List.mem_append]; exact Or.inr he₂)
      have he₁_eq : e₁ = e₀ :=
        unique_inc_first hW₁₂ he₁_in List.mem_cons_self hinc₁ ⟨w, hl₀⟩
      have he₂_eq : e₂ = e₀ :=
        unique_inc_first hW₁₂ he₂_in List.mem_cons_self hinc₂ ⟨w, hl₀⟩
      exact hd_E.2.2 e₀ (he₁_eq ▸ he₁) e₀ (he₂_eq ▸ he₂) rfl
    refine ih W₂ hr₁₂ hx hy (fun e he => ?_)
    rcases List.mem_cons.mp (hedges e he) with rfl | he'
    · exact (he₀_not_W he).elim
    · exact he'

theorem isSimple_reverse_append {G : Graph α β} {a u b : α}
    (W₁ : GraphWalk G a u) (W₂ : GraphWalk G u b)
    (hW₁₂ : (W₁.append W₂).IsSimple) :
    (W₂.reverse.append W₁.reverse).IsSimple := by
  have hsp := isSimple_of_append hW₁₂
  have hnd : (W₁.support ++ W₂.support.tail).Nodup := by
    have h' : (W₁.append W₂).support.Nodup := hW₁₂
    rwa [GraphWalk.support_append] at h'
  have hd := List.nodup_append.mp hnd
  unfold GraphWalk.IsSimple
  rw [GraphWalk.support_append]
  have h1 : W₂.reverse.support.Nodup := hsp.2.reverse
  have h2 : W₁.reverse.support.Nodup := hsp.1.reverse
  refine List.nodup_append.mpr ⟨h1, h2.tail, fun z hz₂ z' hz₁ hzz' => ?_⟩
  subst hzz'
  rw [GraphWalk.support_reverse, List.mem_reverse] at hz₂
  have hz₁_full : z ∈ W₁.reverse.support := by
    rw [W₁.reverse.support_eq_cons]
    exact List.mem_cons_of_mem _ hz₁
  have hz₁_mem : z ∈ W₁.support := by
    rwa [GraphWalk.support_reverse, List.mem_reverse] at hz₁_full
  rw [W₂.support_eq_cons] at hz₂
  rcases List.mem_cons.mp hz₂ with rfl | hz₂_tail
  · rw [W₁.reverse.support_eq_cons] at h2
    exact (List.nodup_cons.mp h2).1 hz₁
  · exact hd.2.2 z hz₁_mem z hz₂_tail rfl

/-- If `W₁.append W₂` is a simple walk in `G` and `W` is a simple walk in `G` between `x, y ∈
W₁.support`
with `W.edges ⊆ (W₁.append W₂).edges`, then `W.edges ⊆ W₁.edges`. -/
theorem edges_subset_left_of_append {G : Graph α β} {a u b x y : α}
    (W₁ : GraphWalk G a u) (W₂ : GraphWalk G u b)
    (hW₁₂ : (W₁.append W₂).IsSimple)
    (W : GraphWalk G x y) (hW : W.IsSimple)
    (hx : x ∈ W₁.support) (hy : y ∈ W₁.support)
    (hedges : ∀ e ∈ W.edges, e ∈ (W₁.append W₂).edges) :
    ∀ e ∈ W.edges, e ∈ W₁.edges := by
  have hrev := edges_subset_right_of_append W₂.reverse W₁.reverse
    (isSimple_reverse_append W₁ W₂ hW₁₂) W hW
    (by rw [GraphWalk.support_reverse, List.mem_reverse]; exact hx)
    (by rw [GraphWalk.support_reverse, List.mem_reverse]; exact hy)
    (fun e he => by
      have he' := hedges e he
      rw [GraphWalk.edges_append, List.mem_append] at he' ⊢
      rcases he' with h | h
      · exact Or.inr (by rw [GraphWalk.edges_reverse, List.mem_reverse]; exact h)
      · exact Or.inl (by rw [GraphWalk.edges_reverse, List.mem_reverse]; exact h))
  intro e he
  have he' := hrev e he
  rwa [GraphWalk.edges_reverse, List.mem_reverse] at he'

/-- Two subpaths `Q₁, Q₂ ≤ P` of a path `P` in `G` with the same ends `v, v'` are equal. -/
theorem eq_of_isGraphPathWithEnds_le {G P Q₁ Q₂ : Graph α β} {a b v v' : α}
    (hP : IsGraphPathWithEnds G P a b)
    (hQ₁ : IsGraphPathWithEnds G Q₁ v v') (hQ₁_le : Q₁ ≤ P)
    (hQ₂ : IsGraphPathWithEnds G Q₂ v v') (hQ₂_le : Q₂ ≤ P) :
    Q₁ = Q₂ := by
  suffices h_eq_walk : ∀ {x y : α} (WP : GraphWalk G x y), WP.IsSimple →
      ∀ {Q : Graph α β}, IsGraphPathWithEnds G Q v v' →
        V(Q) ⊆ {z | z ∈ WP.support} → E(Q) ⊆ {e | e ∈ WP.edges} →
      ∀ {Q' : Graph α β}, IsGraphPathWithEnds G Q' v v' →
        V(Q') ⊆ {z | z ∈ WP.support} → E(Q') ⊆ {e | e ∈ WP.edges} →
      Q = Q' by
    rcases hP with ⟨hPG, W, hW, hVP, hEP⟩
    obtain ⟨WG, hsG, heG⟩ := exists_walk_up_of_le hPG W
    have hWG : WG.IsSimple := by unfold GraphWalk.IsSimple; rw [hsG]; exact hW
    refine h_eq_walk WG hWG hQ₁ ?_ ?_ hQ₂ ?_ ?_
    · intro z hz
      have hzP : z ∈ V(P) := hQ₁_le.vertexSet_mono hz
      rw [hVP] at hzP
      change z ∈ WG.support
      rwa [hsG]
    · intro e he
      have heP : e ∈ E(P) := hQ₁_le.edgeSet_mono he
      rw [hEP] at heP
      change e ∈ WG.edges
      rwa [heG]
    · intro z hz
      have hzP : z ∈ V(P) := hQ₂_le.vertexSet_mono hz
      rw [hVP] at hzP
      change z ∈ WG.support
      rwa [hsG]
    · intro e he
      have heP : e ∈ E(P) := hQ₂_le.edgeSet_mono he
      rw [hEP] at heP
      change e ∈ WG.edges
      rwa [heG]
  intro x y WP hWP Q hQ hVQ hEQ Q' hQ' hVQ' hEQ'
  have hv_WP : v ∈ WP.support := hVQ hQ.left_mem
  have hv'_WP : v' ∈ WP.support := hVQ hQ.right_mem
  obtain ⟨W₁, W₂, rfl⟩ := WP.exists_append_of_mem hv_WP
  rcases (GraphWalk.mem_support_append W₁ W₂).mp hv'_WP with hv'_1 | hv'_2
  · obtain ⟨A₁, A₂, hA⟩ := W₁.exists_append_of_mem hv'_1
    subst hA
    have hsp1 := isSimple_of_append hWP
    have hsp2 := isSimple_of_append hsp1.1
    have hA₂_rev : A₂.reverse.IsSimple := hsp2.2.reverse
    have hsub_A₂ : ∀ {R : Graph α β}, IsGraphPathWithEnds G R v v' →
        E(R) ⊆ {e | e ∈ ((A₁.append A₂).append W₂).edges} → R = walkSubgraph A₂.reverse := by
      intro R hR hER
      rcases hR with ⟨hRG, WR, hWR, hVR, hER_eq⟩
      obtain ⟨WRG, hsR, heR⟩ := exists_walk_up_of_le hRG WR
      have hWRG : WRG.IsSimple := by unfold GraphWalk.IsSimple; rw [hsR]; exact hWR
      have hed1 : ∀ e ∈ WRG.reverse.edges, e ∈ ((A₁.append A₂).append W₂).edges := by
        intro e he
        rw [GraphWalk.edges_reverse, List.mem_reverse, heR] at he
        exact hER (by rw [hER_eq]; exact he)
      have hed2 := edges_subset_left_of_append (A₁.append A₂) W₂ hWP
        WRG.reverse hWRG.reverse
        ((GraphWalk.mem_support_append A₁ A₂).mpr (Or.inr A₂.start_mem_support))
        ((GraphWalk.mem_support_append A₁ A₂).mpr (Or.inr A₂.end_mem_support)) hed1
      have hed3 := edges_subset_right_of_append A₁ A₂ hsp1.1
        WRG.reverse hWRG.reverse A₂.start_mem_support A₂.end_mem_support hed2
      have hed4 : ∀ e ∈ WRG.edges, e ∈ A₂.reverse.edges := by
        intro e he
        rw [GraphWalk.edges_reverse, List.mem_reverse]
        exact hed3 e (by rw [GraphWalk.edges_reverse, List.mem_reverse]; exact he)
      obtain ⟨hsupp_eq, hed_eq⟩ := eq_of_isSimple_subwalk_edges A₂.reverse WRG hA₂_rev hWRG hed4
      refine (Compatible.of_le_le hRG (walkSubgraph_le A₂.reverse)).ext ?_ ?_
      · rw [hVR, vertexSet_walkSubgraph, ← hsR, hsupp_eq]
      · rw [hER_eq, edgeSet_walkSubgraph, ← heR, hed_eq]
    exact (hsub_A₂ hQ hEQ).trans (hsub_A₂ hQ' hEQ').symm
  · obtain ⟨B₁, B₂, hB⟩ := W₂.exists_append_of_mem hv'_2
    subst hB
    have hsp1 := isSimple_of_append hWP
    have hsp2 := isSimple_of_append hsp1.2
    have hB₁_s : B₁.IsSimple := hsp2.1
    have hsub_B₁ : ∀ {R : Graph α β}, IsGraphPathWithEnds G R v v' →
        E(R) ⊆ {e | e ∈ (W₁.append (B₁.append B₂)).edges} → R = walkSubgraph B₁ := by
      intro R hR hER
      rcases hR with ⟨hRG, WR, hWR, hVR, hER_eq⟩
      obtain ⟨WRG, hsR, heR⟩ := exists_walk_up_of_le hRG WR
      have hWRG : WRG.IsSimple := by unfold GraphWalk.IsSimple; rw [hsR]; exact hWR
      have hed1 : ∀ e ∈ WRG.edges, e ∈ (W₁.append (B₁.append B₂)).edges := by
        intro e he
        exact hER (by rw [hER_eq, ← heR]; exact he)
      have hed2 := edges_subset_right_of_append W₁ (B₁.append B₂) hWP WRG hWRG
        ((GraphWalk.mem_support_append B₁ B₂).mpr (Or.inl B₁.start_mem_support))
        ((GraphWalk.mem_support_append B₁ B₂).mpr (Or.inl B₁.end_mem_support)) hed1
      have hed3 := edges_subset_left_of_append B₁ B₂ hsp1.2 WRG hWRG
        B₁.start_mem_support B₁.end_mem_support hed2
      obtain ⟨hsupp_eq, hed_eq⟩ := eq_of_isSimple_subwalk_edges B₁ WRG hB₁_s hWRG hed3
      refine (Compatible.of_le_le hRG (walkSubgraph_le B₁)).ext ?_ ?_
      · rw [hVR, vertexSet_walkSubgraph, ← hsR, hsupp_eq]
      · rw [hER_eq, edgeSet_walkSubgraph, ← heR, hed_eq]
    exact (hsub_B₁ hQ hEQ).trans (hsub_B₁ hQ' hEQ').symm

/-- If `P` is a family of pairwise vertex-disjoint paths in `G`, `P_sub ≤ P i` is a subpath between
`v ≠ v'`, and `Q` is a path in `G` between `v` and `v'` edge-disjoint from `P_sub`, then `Q` has an
edge not in `⋃ k, E(P k)`. -/
theorem exists_edge_not_mem_iUnion_of_path {G : Graph α β} {r : ℕ}
    {P : Fin r → Graph α β} (hP_le : ∀ k, P k ≤ G)
    (hP_disj : Pairwise (fun i₁ i₂ => Disjoint V(P i₁) V(P i₂)))
    {i : Fin r} {P_sub Q : Graph α β} {a b v v' : α}
    (hP_i : IsGraphPathWithEnds G (P i) a b)
    (hP_sub : IsGraphPathWithEnds G P_sub v v') (hP_sub_le : P_sub ≤ P i)
    (hQ : IsGraphPathWithEnds G Q v v') (hvne : v ≠ v')
    (hdisj_E : Disjoint E(P_sub) E(Q)) :
    ∃ e₀ ∈ E(Q), e₀ ∉ ⋃ k, E(P k) := by
  by_contra hall
  push Not at hall
  have hQ_copy := hQ
  rcases hQ with ⟨hQG, W, hW_simple, hVQ, hEQ⟩
  obtain ⟨WG, hsG, heG⟩ := exists_walk_up_of_le hQG W
  have hwalk : ∀ {x y : α} (W₀ : GraphWalk G x y),
      x ∈ V(P i) → (∀ e ∈ W₀.edges, e ∈ ⋃ k, E(P k)) →
      (∀ z ∈ W₀.support, z ∈ V(P i)) ∧ (∀ e ∈ W₀.edges, e ∈ E(P i)) := by
    intro x y W₀ hx hedges
    induction W₀ with
    | nil _ =>
      refine ⟨fun z hz => ?_, fun e he => by simp [GraphWalk.edges] at he⟩
      rcases List.mem_singleton.mp hz with rfl
      exact hx
    | @cons u w y e hl r ih =>
      have he_mem : e ∈ ⋃ k, E(P k) := hedges e (List.mem_cons_self ..)
      obtain ⟨k, hek⟩ := mem_iUnion.mp he_mem
      obtain ⟨x₁, x₂, hx_link⟩ := (P k).exists_isLink_of_mem_edgeSet hek
      have hx_linkG : G.IsLink e x₁ x₂ := hx_link.mono (hP_le k)
      have hu_Pk : u ∈ V(P k) := by
        rcases hl.left_eq_or_eq hx_linkG with rfl | rfl
        · exact hx_link.left_mem
        · exact hx_link.right_mem
      have hki : k = i := by
        by_contra hne
        exact disjoint_left.mp (hP_disj hne) hu_Pk hx
      subst hki
      have hw_Pi : w ∈ V(P k) := by
        rcases hl.right_eq_or_eq hx_linkG with rfl | rfl
        · exact hx_link.left_mem
        · exact hx_link.right_mem
      obtain ⟨ih_V, ih_E⟩ := ih hw_Pi (fun f hf => hedges f (List.mem_cons_of_mem _ hf))
      refine ⟨fun z hz => ?_, fun f hf => ?_⟩
      · rcases List.mem_cons.mp hz with rfl | hz
        · exact hx
        · exact ih_V z hz
      · rcases List.mem_cons.mp hf with rfl | hf
        · exact hek
        · exact ih_E f hf
  have hv_Pi : v ∈ V(P i) := hP_sub_le.vertexSet_mono hP_sub.left_mem
  obtain ⟨hV_sub, hE_sub⟩ := hwalk WG hv_Pi (fun e he => hall e (by rw [hEQ, ← heG]; exact he))
  have hQ_le : Q ≤ P i := by
    rw [(Compatible.of_le_le hQG (hP_le i)).le_iff]
    exact ⟨fun z hz => hV_sub z (by rw [hsG]; rwa [hVQ] at hz),
      fun e he => hE_sub e (by rw [heG]; rwa [hEQ] at he)⟩
  have hQ_eq : Q = P_sub :=
    eq_of_isGraphPathWithEnds_le hP_i hQ_copy hQ_le hP_sub hP_sub_le
  obtain ⟨e₁, he₁, -⟩ := IsGraphPathWithEnds.exists_inc_left_of_ne hQ_copy hvne
  exact disjoint_left.mp hdisj_E (hQ_eq ▸ he₁) he₁

/-- Given a path `P` from `x` to `y` and a subpath `P_sub ≤ P` between `v` and `v'`, `P` decomposes
into `P₁`, `P_sub`, and `P₂` (in one of the two orientations of `{v, v'}`). -/
theorem exists_decomp_of_isGraphPathWithEnds_le {G P P_sub : Graph α β} {x y v v' : α}
    (hP : IsGraphPathWithEnds G P x y) (hP_sub : IsGraphPathWithEnds G P_sub v v')
    (hP_sub_le : P_sub ≤ P) :
    (∃ P₁ P₂ : Graph α β, P₁ ≤ P ∧ P₂ ≤ P ∧
      IsGraphPathWithEnds G P₁ x v ∧ IsGraphPathWithEnds G P₂ v' y ∧
      V(P₁) ∩ V(P_sub) = {v} ∧ Disjoint E(P₁) E(P_sub) ∧ Disjoint E(P₂) E(P_sub)) ∨
    (∃ P₁ P₂ : Graph α β, P₁ ≤ P ∧ P₂ ≤ P ∧
      IsGraphPathWithEnds G P₁ x v' ∧ IsGraphPathWithEnds G P₂ v y ∧
      V(P₁) ∩ V(P_sub) = {v'} ∧ Disjoint E(P₁) E(P_sub) ∧ Disjoint E(P₂) E(P_sub)) := by
  have hvP : v ∈ V(P) := hP_sub_le.vertexSet_mono hP_sub.left_mem
  have hv'P : v' ∈ V(P) := hP_sub_le.vertexSet_mono hP_sub.right_mem
  obtain ⟨A, B, hAP, hBP, hA, hB, hAB_union, hAB_inter, hAB_disjE⟩ := hP.exists_split_at hvP
  have hAG : IsGraphPathWithEnds G A x v := hA.mono hP.le
  have hBG : IsGraphPathWithEnds G B v y := hB.mono hP.le
  have hv'AB : v' ∈ V(A) ∪ V(B) := by
    rw [← vertexSet_subgraphUnion P A B, hAB_union]
    exact hv'P
  rcases hv'AB with hv'A | hv'B
  · right
    obtain ⟨A₁, A₂, hA₁A, hA₂A, hA₁, hA₂, _, hA_inter, hA_disjE⟩ := hAG.exists_split_at hv'A
    have hA₁G : IsGraphPathWithEnds G A₁ x v' := hA₁.mono hAG.le
    have hA₂G : IsGraphPathWithEnds G A₂ v' v := hA₂.mono hAG.le
    have hP_sub_eq : P_sub = A₂ :=
      eq_of_isGraphPathWithEnds_le hP hP_sub hP_sub_le hA₂G.symm (hA₂A.trans hAP)
    refine ⟨A₁, B, hA₁A.trans hAP, hBP, hA₁G, hBG, ?_, ?_, ?_⟩
    · rw [hP_sub_eq, hA_inter]
    · rw [hP_sub_eq]; exact hA_disjE
    · rw [hP_sub_eq]
      exact disjoint_of_subset_right hA₂A.edgeSet_mono hAB_disjE.symm
  · left
    obtain ⟨B₁, B₂, hB₁B, hB₂B, hB₁, hB₂, _, hB_inter, hB_disjE⟩ := hBG.exists_split_at hv'B
    have hB₁G : IsGraphPathWithEnds G B₁ v v' := hB₁.mono hBG.le
    have hB₂G : IsGraphPathWithEnds G B₂ v' y := hB₂.mono hBG.le
    have hP_sub_eq : P_sub = B₁ :=
      eq_of_isGraphPathWithEnds_le hP hP_sub hP_sub_le hB₁G (hB₁B.trans hBP)
    refine ⟨A, B₂, hAP, hB₂B.trans hBP, hAG, hB₂G, ?_, ?_, ?_⟩
    · apply subset_antisymm
      · intro u ⟨huA, huP_sub⟩
        have huB : u ∈ V(B) := hB₁B.vertexSet_mono (hP_sub_eq ▸ huP_sub)
        have huAB : u ∈ V(A) ∩ V(B) := ⟨huA, huB⟩
        rwa [hAB_inter] at huAB
      · rintro u rfl
        exact ⟨hAG.right_mem, hP_sub.left_mem⟩
    · rw [hP_sub_eq]
      exact disjoint_of_subset_right hB₁B.edgeSet_mono hAB_disjE
    · rw [hP_sub_eq]; exact hB_disjE.symm

/-- Given a path `P` from `x` to `y` and a subpath `P_sub ≤ P` between `v` and `v'`, there is a
prefix subpath `R₁ ≤ P` from `x` to `v₁ ∈ {v, v'}` that meets `P_sub` only at `v₁`. -/
theorem exists_prefix_disjoint_subpath {G P P_sub : Graph α β} {x y v v' : α}
    (hP : IsGraphPathWithEnds G P x y) (hP_sub : IsGraphPathWithEnds G P_sub v v')
    (hP_sub_le : P_sub ≤ P) :
    ∃ v₁ : α, (v₁ = v ∨ v₁ = v') ∧ ∃ R₁ : Graph α β,
      R₁ ≤ P ∧ IsGraphPathWithEnds G R₁ x v₁ ∧ V(R₁) ∩ V(P_sub) = {v₁} := by
  rcases exists_decomp_of_isGraphPathWithEnds_le hP hP_sub hP_sub_le with
    ⟨P₁, _, hP₁P, _, hP₁, _, hinter, _, _⟩ | ⟨P₁, _, hP₁P, _, hP₁, _, hinter, _, _⟩
  · exact ⟨v, Or.inl rfl, P₁, hP₁P, hP₁, hinter⟩
  · exact ⟨v', Or.inr rfl, P₁, hP₁P, hP₁, hinter⟩

/-- If `P ∩ C` is a path, `P_sub ≤ P` has ends `v, v' ∉ V(C)`, and a prefix `R₁ ≤ P` from `x` to
`v₁ ∈ {v, v'}` with `V(R₁) ∩ V(P_sub) = {v₁}` meets `V(C)`, then `Disjoint V(P_sub) V(C)`. -/
theorem disjoint_detour_of_isGraphPath_inter {G P P_sub R₁ C : Graph α β} {x y v v' v₁ : α}
    (hCG : C ≤ G)
    (hP : IsGraphPathWithEnds G P x y) (hP_sub : IsGraphPathWithEnds G P_sub v v')
    (hP_sub_le : P_sub ≤ P) (hv₁ : v₁ = v ∨ v₁ = v')
    (hR₁_le : R₁ ≤ P) (hR₁ : IsGraphPathWithEnds G R₁ x v₁)
    (hR₁_inter : V(R₁) ∩ V(P_sub) = {v₁})
    (hv_not : v ∉ V(C)) (hv'_not : v' ∉ V(C))
    (hinter : IsGraphPath G (subgraphInter G P C))
    (hR₁_meet : (V(R₁) ∩ V(C)).Nonempty) :
    Disjoint V(P_sub) V(C) := by
  by_contra hnd
  obtain ⟨w₂, hw₂P_sub, hw₂C⟩ := not_disjoint_iff.mp hnd
  obtain ⟨w₁, hw₁R₁, hw₁C⟩ := hR₁_meet
  obtain ⟨S₁, hS₁_le, _, hS₁⟩ := hR₁.exists_subpath hw₁R₁ hR₁.right_mem
  have hv₁_mem_P_sub : v₁ ∈ V(P_sub) := by
    rcases hv₁ with rfl | rfl
    · exact hP_sub.left_mem
    · exact hP_sub.right_mem
  have hP_sub_v₁ : ∃ v₂ : α, IsGraphPathWithEnds G P_sub v₁ v₂ := by
    rcases hv₁ with rfl | rfl
    · exact ⟨v', hP_sub⟩
    · exact ⟨v, hP_sub.symm⟩
  obtain ⟨v₂, hP_sub'⟩ := hP_sub_v₁
  obtain ⟨S₂, hS₂_le, _, hS₂⟩ := hP_sub'.exists_subpath hv₁_mem_P_sub hw₂P_sub
  have hS_V_inter : V(S₁) ∩ V(S₂) = {v₁} := by
    apply subset_antisymm
    · intro u ⟨hu₁, hu₂⟩
      have hu : u ∈ V(R₁) ∩ V(P_sub) := ⟨hS₁_le.vertexSet_mono hu₁, hS₂_le.vertexSet_mono hu₂⟩
      rwa [hR₁_inter] at hu
    · rintro u rfl
      exact ⟨hS₁.right_mem, hS₂.left_mem⟩
  have hS : IsGraphPathWithEnds G (subgraphUnion G S₁ S₂) w₁ w₂ :=
    hS₁.subgraphUnion hS₂ hS_V_inter
  have hS_le : subgraphUnion G S₁ S₂ ≤ P :=
    (subgraphUnion_le_iff hS₁.le hS₂.le hP.le).mpr ⟨hS₁_le.trans hR₁_le, hS₂_le.trans hP_sub_le⟩
  have hw₁_inter : w₁ ∈ V(subgraphInter G P C) := by
    rw [vertexSet_subgraphInter]
    exact ⟨hR₁_le.vertexSet_mono hw₁R₁, hw₁C⟩
  have hw₂_inter : w₂ ∈ V(subgraphInter G P C) := by
    rw [vertexSet_subgraphInter]
    exact ⟨hP_sub_le.vertexSet_mono hw₂P_sub, hw₂C⟩
  rcases hinter with ⟨p₀, q₀, hp₀q₀⟩
  obtain ⟨S', hS'_le, _, hS'⟩ := hp₀q₀.exists_subpath hw₁_inter hw₂_inter
  have hS'_le_P : S' ≤ P := hS'_le.trans (subgraphInter_le_left hP.le hCG)
  have hS_eq : subgraphUnion G S₁ S₂ = S' :=
    eq_of_isGraphPathWithEnds_le hP hS hS_le hS' hS'_le_P
  have hv₁_in_S' : v₁ ∈ V(S') := by
    rw [← hS_eq, vertexSet_subgraphUnion]
    exact Or.inl hS₁.right_mem
  have hv₁_in_inter : v₁ ∈ V(subgraphInter G P C) := hS'_le.vertexSet_mono hv₁_in_S'
  rw [vertexSet_subgraphInter] at hv₁_in_inter
  rcases hv₁ with rfl | rfl
  · exact hv_not hv₁_in_inter.2
  · exact hv'_not hv₁_in_inter.2

/-! ## 5. Plane Closed Discs and `GraphDrawing` Bridge Lemmas -/

open Topology Metric

private theorem IsLineWithEnds.isPreconnected_sdiff_left {L : Set EuclideanPlane}
    {a b : EuclideanPlane} (h : IsLineWithEnds L a b) : IsPreconnected (L \ {a}) := by
  obtain ⟨f, hf0, _⟩ := h
  have hEq : L \ {a} = (fun t => (f t).1) '' Ioc (0 : unitInterval) 1 := by
    ext x
    constructor
    · rintro ⟨hxL, hxa⟩
      obtain ⟨t, ht⟩ := f.surjective ⟨x, hxL⟩
      have hx' : (f t).1 = x := congrArg Subtype.val ht
      refine ⟨t, ⟨lt_of_le_of_ne unitInterval.nonneg' ?_, unitInterval.le_one'⟩, hx'⟩
      rintro rfl
      exact hxa (hx'.symm.trans hf0)
    · rintro ⟨t, ⟨h0, _⟩, rfl⟩
      refine ⟨(f t).2, ?_⟩
      intro h'
      have := f.injective (Subtype.ext (h'.trans hf0.symm))
      exact h0.ne this.symm
  rw [hEq]
  exact isPreconnected_Ioc.image _ (by fun_prop)

private theorem IsLineWithEnds.isPreconnected {L : Set EuclideanPlane} {a b : EuclideanPlane}
    (h : IsLineWithEnds L a b) : IsPreconnected L :=
  GraphMinor.Surface.IsLineWithEnds.isPreconnected h

private theorem disc_mono_of_subset {Y D₁ D₂ : Set EuclideanPlane}
    (hY : IsClosedDisc Y) (hD₁Y : D₁ ⊆ Y) (hD₂Y : D₂ ⊆ Y)
    (hD₁ : IsClosedDisc D₁) (hD₂ : IsClosedDisc D₂)
    (hbd : discBd D₁ ⊆ D₂) : D₁ ⊆ D₂ := by
  obtain ⟨Δ, ⟨hΔD₂, hΔ_disc, hΔ_bd, -⟩, -⟩ :=
    disc_oArc D₂ (discBd D₁) hD₂ hbd hD₁.isOArc_discBd
  obtain ⟨Δ', ⟨-, -, -, -⟩, huniq⟩ :=
    disc_oArc Y (discBd D₁) hY ((Surface.discBd_subset D₁).trans hD₁Y) hD₁.isOArc_discBd
  have h1 : D₁ = Δ' := huniq D₁ hD₁Y hD₁ rfl
  have h2 : Δ = Δ' := huniq Δ (hΔD₂.trans hD₂Y) hΔ_disc hΔ_bd
  rw [h1, ← h2]
  exact hΔD₂

/-- If `L` is an outer chord of a closed disc `D ⊆ Y` (with `L ∩ D = {s, t}`), then one of the two
arcs `A₁, A₂` of `discBd D` between `s` and `t` forms with `L` the boundary of a closed disc
`Δ_k ⊆ Y` containing `D`. -/
private theorem outer_chord_disc_contains {Y D A₁ A₂ L : Set EuclideanPlane} {s t : EuclideanPlane}
    (hY : IsClosedDisc Y) (hD : IsClosedDisc D) (hDY : D ⊆ Y)
    (hA₁ : IsLineWithEnds A₁ s t) (hA₂ : IsLineWithEnds A₂ s t) (hL : IsLineWithEnds L s t)
    (hA_inter : A₁ ∩ A₂ = {s, t}) (hA_union : A₁ ∪ A₂ = discBd D)
    (hLY : L ⊆ Y) (hLD : L ∩ D = {s, t}) :
    (∃ Δ₁ ⊆ Y, IsClosedDisc Δ₁ ∧ discBd Δ₁ = L ∪ A₁ ∧ D ⊆ Δ₁) ∨
    (∃ Δ₂ ⊆ Y, IsClosedDisc Δ₂ ∧ discBd Δ₂ = L ∪ A₂ ∧ D ⊆ Δ₂) := by
  have hman : ∀ x : EuclideanPlane, IsManifoldPoint x :=
    fun x ↦ (Surface.isInteriorPoint_euclideanPlane x).isManifoldPoint
  have hbdD : discBd D ⊆ D := Surface.discBd_subset D
  have hA₁D : A₁ ⊆ discBd D := hA_union ▸ subset_union_left
  have hA₂D : A₂ ⊆ discBd D := hA_union ▸ subset_union_right
  have hs_in : s ∈ A₁ ∩ A₂ := by rw [hA_inter]; exact mem_insert s _
  have ht_in : t ∈ A₁ ∩ A₂ := by rw [hA_inter]; exact mem_insert_of_mem s rfl
  have hs_L : s ∈ L := by
    have : s ∈ L ∩ D := by rw [hLD]; exact mem_insert s _
    exact this.1
  have ht_L : t ∈ L := by
    have : t ∈ L ∩ D := by rw [hLD]; exact mem_insert_of_mem s rfl
    exact this.1
  have hLA₁_inter : L ∩ A₁ ⊆ {s, t} := by
    intro x ⟨hxL, hxA₁⟩
    have : x ∈ L ∩ D := ⟨hxL, hbdD (hA₁D hxA₁)⟩
    rwa [hLD] at this
  have hLA₂_inter : L ∩ A₂ ⊆ {s, t} := by
    intro x ⟨hxL, hxA₂⟩
    have : x ∈ L ∩ D := ⟨hxL, hbdD (hA₂D hxA₂)⟩
    rwa [hLD] at this
  have hO₁ : IsOArc (L ∪ A₁) := GraphMinor.GM14.isOArc_union hL hA₁ hLA₁_inter
  have hO₂ : IsOArc (L ∪ A₂) := GraphMinor.GM14.isOArc_union hL hA₂ hLA₂_inter
  have hLA₁_Y : L ∪ A₁ ⊆ Y := union_subset hLY ((hA₁D.trans hbdD).trans hDY)
  have hLA₂_Y : L ∪ A₂ ⊆ Y := union_subset hLY ((hA₂D.trans hbdD).trans hDY)
  obtain ⟨Δ₁, ⟨hΔ₁Y, hΔ₁, hΔ₁_bd, -⟩, -⟩ := disc_oArc Y (L ∪ A₁) hY hLA₁_Y hO₁
  obtain ⟨Δ₂, ⟨hΔ₂Y, hΔ₂, hΔ₂_bd, -⟩, hΔ₂_uniq⟩ := disc_oArc Y (L ∪ A₂) hY hLA₂_Y hO₂
  have hdisj : Disjoint (discInt D) (discBd Δ₁) := by
    rw [hΔ₁_bd, disjoint_left]
    rintro x ⟨hxD, hx_nbd⟩ (hxL | hxA₁)
    · have hx_st : x ∈ ({s, t} : Set EuclideanPlane) := by
        rw [← hLD]; exact ⟨hxL, hxD⟩
      rcases hx_st with rfl | rfl
      · exact hx_nbd (hA₁D hs_in.1)
      · exact hx_nbd (hA₁D ht_in.1)
    · exact hx_nbd (hA₁D hxA₁)
  rcases hΔ₁.side hman hD.isPreconnected_discInt hdisj with hin | hout
  · left
    refine ⟨Δ₁, hΔ₁Y, hΔ₁, hΔ₁_bd, ?_⟩
    exact hD.subset_closure_discInt.trans
      (closure_minimal (hin.trans (discInt_subset Δ₁)) hΔ₁.isClosed)
  · right
    have hA₂_out : Disjoint (A₂ \ {s, t}) Δ₁ := by
      rw [disjoint_left]
      rintro x ⟨hxA₂, hx_nst⟩ hxΔ₁
      have hxD : x ∈ D := hbdD (hA₂D hxA₂)
      have hx_not_bd₁ : x ∉ discBd Δ₁ := by
        rw [hΔ₁_bd]
        rintro (hxL | hxA₁)
        · have : x ∈ L ∩ D := ⟨hxL, hxD⟩
          rw [hLD] at this
          exact hx_nst this
        · have : x ∈ A₁ ∩ A₂ := ⟨hxA₁, hxA₂⟩
          rw [hA_inter] at this
          exact hx_nst this
      have hx_int₁ : x ∈ discInt Δ₁ := ⟨hxΔ₁, hx_not_bd₁⟩
      have hx_cl : x ∈ closure (discInt D) := hD.subset_closure_discInt hxD
      obtain ⟨w, hw₁, hwD⟩ := mem_closure_iff.mp hx_cl _ (hΔ₁.isOpen_discInt hman) hx_int₁
      exact disjoint_left.mp hout hwD hw₁.1
    have hinter : Δ₁ ∩ D = A₁ := by
      apply subset_antisymm
      · rintro x ⟨hxΔ₁, hxD⟩
        by_cases hx_bd : x ∈ discBd D
        · rw [← hA_union] at hx_bd
          rcases hx_bd with hxA₁ | hxA₂
          · exact hxA₁
          · by_cases hx_st : x ∈ ({s, t} : Set EuclideanPlane)
            · rcases hx_st with rfl | rfl
              · exact hs_in.1
              · exact ht_in.1
            · exact (disjoint_left.mp hA₂_out ⟨hxA₂, hx_st⟩ hxΔ₁).elim
        · exact (disjoint_left.mp hout ⟨hxD, hx_bd⟩ hxΔ₁).elim
      · intro x hxA₁
        exact ⟨(Surface.discBd_subset Δ₁) (hΔ₁_bd ▸ Or.inr hxA₁), hbdD (hA₁D hxA₁)⟩
    have hu := disc_union Δ₁ D A₁ s t hΔ₁ hD hA₁ hinter
      (hΔ₁_bd ▸ subset_union_right) hA₁D
    have hbd_union : discBd (Δ₁ ∪ D) = L ∪ A₂ := by
      rw [hu.2, hΔ₁_bd, ← hA_union]
      ext x
      constructor
      · rintro ⟨(hxL | hxA₁) | hxA₁ | hxA₂, hxn⟩
        · exact Or.inl hxL
        · by_cases hx_st : x ∈ ({s, t} : Set EuclideanPlane)
          · rcases hx_st with rfl | rfl
            · exact Or.inl hs_L
            · exact Or.inl ht_L
          · exact (hxn ⟨hxA₁, hx_st⟩).elim
        · by_cases hx_st : x ∈ ({s, t} : Set EuclideanPlane)
          · rcases hx_st with rfl | rfl
            · exact Or.inl hs_L
            · exact Or.inl ht_L
          · exact (hxn ⟨hxA₁, hx_st⟩).elim
        · exact Or.inr hxA₂
      · rintro (hxL | hxA₂)
        · refine ⟨Or.inl (Or.inl hxL), fun ⟨hxA₁, hx_nst⟩ => ?_⟩
          exact hx_nst (hLA₁_inter ⟨hxL, hxA₁⟩)
        · refine ⟨Or.inr (Or.inr hxA₂), fun ⟨hxA₁, hx_nst⟩ => ?_⟩
          have : x ∈ A₁ ∩ A₂ := ⟨hxA₁, hxA₂⟩
          rw [hA_inter] at this
          exact hx_nst this
    have heq : Δ₁ ∪ D = Δ₂ := hΔ₂_uniq (Δ₁ ∪ D) (union_subset hΔ₁Y hDY) hu.1 hbd_union
    exact ⟨Δ₂, hΔ₂Y, hΔ₂, hΔ₂_bd, heq ▸ subset_union_right⟩

/-- If `L ⊆ D` is an inner chord of a closed disc `D` (`L ∩ discBd D = {s, t}`) and `Δ₀ ⊆ D` is a
closed disc whose interior `discInt Δ₀` is disjoint from `L`, then for one of the two arcs `A₁, A₂`
of `discBd D` between `s` and `t`, every preconnected set `R ⊆ D \ L` meeting `A_k` is disjoint
from `Δ₀`. -/
private theorem inner_chord_separates_from_core {D Δ₀ A₁ A₂ L : Set EuclideanPlane}
    {s t : EuclideanPlane}
    (hD : IsClosedDisc D) (hΔ₀ : IsClosedDisc Δ₀) (hΔ₀D : Δ₀ ⊆ D)
    (hA₁ : IsLineWithEnds A₁ s t) (hA₂ : IsLineWithEnds A₂ s t) (hL : IsLineWithEnds L s t)
    (hst : s ≠ t)
    (hA_inter : A₁ ∩ A₂ = {s, t}) (hA_union : A₁ ∪ A₂ = discBd D)
    (hLD : L ⊆ D) (hL_bd : L ∩ discBd D = {s, t})
    (hΔ₀_disj_L : Disjoint (discInt Δ₀) L) :
    (∀ R : Set EuclideanPlane, IsPreconnected R → R ⊆ D \ L →
      (R ∩ A₁).Nonempty → Disjoint R Δ₀) ∨
    (∀ R : Set EuclideanPlane, IsPreconnected R → R ⊆ D \ L →
      (R ∩ A₂).Nonempty → Disjoint R Δ₀) := by
  obtain ⟨B₁, B₂, Δ₁, Δ₂, _, hB_comp, hΔ₁, hΔ₂, hΔ_union, hΔ_inter, hΔ₁_bd, hΔ₂_bd, _⟩ :=
    disc_iArc D L s t hD hLD hst hL hL_bd
  have hsub_or_sub : ∀ {C : Set EuclideanPlane}, IsPreconnected C → C ⊆ D \ L →
      C ⊆ Δ₁ \ L ∨ C ⊆ Δ₂ \ L := by
    intro C hC hCDL
    by_contra hnot
    obtain ⟨hnot₁, hnot₂⟩ := not_or.mp hnot
    obtain ⟨x, hxC, hxn₁⟩ := not_subset.mp hnot₁
    obtain ⟨y, hyC, hyn₂⟩ := not_subset.mp hnot₂
    have hx₁_compl : x ∈ Δ₁ᶜ := fun hx₁ => hxn₁ ⟨hx₁, (hCDL hxC).2⟩
    have hy₂_compl : y ∈ Δ₂ᶜ := fun hy₂ => hyn₂ ⟨hy₂, (hCDL hyC).2⟩
    have hcov : C ⊆ Δ₂ᶜ ∪ Δ₁ᶜ := by
      intro z hz
      have hzDL := hCDL hz
      by_cases hz₂ : z ∈ Δ₂
      · refine Or.inr fun hz₁ => hzDL.2 ?_
        rw [← hΔ_inter]
        exact ⟨hz₁, hz₂⟩
      · exact Or.inl hz₂
    obtain ⟨z, hzC, hz₂, hz₁⟩ := hC Δ₂ᶜ Δ₁ᶜ hΔ₂.isClosed.isOpen_compl hΔ₁.isClosed.isOpen_compl
      hcov ⟨y, hyC, hy₂_compl⟩ ⟨x, hxC, hx₁_compl⟩
    have hzD : z ∈ Δ₁ ∪ Δ₂ := hΔ_union ▸ (hCDL hzC).1
    rcases hzD with h | h
    · exact hz₁ h
    · exact hz₂ h
  have hΔ₁₂_disj : Disjoint (Δ₁ \ L) (Δ₂ \ L) := by
    rw [disjoint_left]
    rintro x ⟨hx₁, hxn⟩ ⟨hx₂, _⟩
    exact hxn (hΔ_inter ▸ ⟨hx₁, hx₂⟩)
  have hsub_of_meet₁ : ∀ {C : Set EuclideanPlane}, IsPreconnected C → C ⊆ D \ L →
      (C ∩ (Δ₁ \ L)).Nonempty → C ⊆ Δ₁ \ L := by
    intro C hC hCDL ⟨x, hxC, hx₁⟩
    rcases hsub_or_sub hC hCDL with h | h
    · exact h
    · exact (disjoint_left.mp hΔ₁₂_disj hx₁ (h hxC)).elim
  have hsub_of_meet₂ : ∀ {C : Set EuclideanPlane}, IsPreconnected C → C ⊆ D \ L →
      (C ∩ (Δ₂ \ L)).Nonempty → C ⊆ Δ₂ \ L := by
    intro C hC hCDL ⟨x, hxC, hx₂⟩
    rcases hsub_or_sub hC hCDL with h | h
    · exact (disjoint_left.mp hΔ₁₂_disj (h hxC) hx₂).elim
    · exact h
  have hB₁_mem : B₁ ∈ componentsIn (discBd D \ {s, t}) := by
    rw [hB_comp]; exact mem_insert B₁ _
  have hB₂_mem : B₂ ∈ componentsIn (discBd D \ {s, t}) := by
    rw [hB_comp]; exact mem_insert_of_mem B₁ rfl
  obtain ⟨y₁, hy₁, hB₁_eq⟩ := hB₁_mem
  obtain ⟨y₂, hy₂, hB₂_eq⟩ := hB₂_mem
  have hB₁_ne : B₁.Nonempty := ⟨y₁, hB₁_eq ▸ mem_connectedComponentIn hy₁⟩
  have hB₂_ne : B₂.Nonempty := ⟨y₂, hB₂_eq ▸ mem_connectedComponentIn hy₂⟩
  have hB₁_sub : B₁ ⊆ discBd D \ {s, t} := hB₁_eq ▸ connectedComponentIn_subset _ _
  have hB₂_sub : B₂ ⊆ discBd D \ {s, t} := hB₂_eq ▸ connectedComponentIn_subset _ _
  have hB₁_in_Δ₁ : B₁ ⊆ Δ₁ \ L := by
    intro x hxB₁
    have hx_bd := hB₁_sub hxB₁
    refine ⟨(Surface.discBd_subset Δ₁) (hΔ₁_bd ▸ Or.inl hxB₁), fun hxL => hx_bd.2 ?_⟩
    rw [← hL_bd]
    exact ⟨hxL, hx_bd.1⟩
  have hB₂_in_Δ₂ : B₂ ⊆ Δ₂ \ L := by
    intro x hxB₂
    have hx_bd := hB₂_sub hxB₂
    refine ⟨(Surface.discBd_subset Δ₂) (hΔ₂_bd ▸ Or.inl hxB₂), fun hxL => hx_bd.2 ?_⟩
    rw [← hL_bd]
    exact ⟨hxL, hx_bd.1⟩
  have hC₁_sub : A₁ \ {s, t} ⊆ D \ L := by
    rintro x ⟨hxA₁, hx_nst⟩
    have hx_bd : x ∈ discBd D := hA_union ▸ Or.inl hxA₁
    refine ⟨(Surface.discBd_subset D) hx_bd, fun hxL => hx_nst ?_⟩
    rw [← hL_bd]
    exact ⟨hxL, hx_bd⟩
  have hC₂_sub : A₂ \ {s, t} ⊆ D \ L := by
    rintro x ⟨hxA₂, hx_nst⟩
    have hx_bd : x ∈ discBd D := hA_union ▸ Or.inr hxA₂
    refine ⟨(Surface.discBd_subset D) hx_bd, fun hxL => hx_nst ?_⟩
    rw [← hL_bd]
    exact ⟨hxL, hx_bd⟩
  have hbd_cov : discBd D \ {s, t} ⊆ (A₁ \ {s, t}) ∪ (A₂ \ {s, t}) := by
    rintro x ⟨hx_bd, hx_nst⟩
    rw [← hA_union] at hx_bd
    rcases hx_bd with h | h
    · exact Or.inl ⟨h, hx_nst⟩
    · exact Or.inr ⟨h, hx_nst⟩
  have hA₁_side := hsub_or_sub (GraphMinor.GM14.IsLineWithEnds.isPreconnected_sdiff_pair hA₁)
    hC₁_sub
  have hA₂_side := hsub_or_sub (GraphMinor.GM14.IsLineWithEnds.isPreconnected_sdiff_pair hA₂)
    hC₂_sub
  have hA_one_each :
      (A₁ \ {s, t} ⊆ Δ₁ \ L ∧ A₂ \ {s, t} ⊆ Δ₂ \ L) ∨
      (A₁ \ {s, t} ⊆ Δ₂ \ L ∧ A₂ \ {s, t} ⊆ Δ₁ \ L) := by
    rcases hA₁_side with h1 | h1 <;> rcases hA₂_side with h2 | h2
    · exfalso
      obtain ⟨b₂, hb₂⟩ := hB₂_ne
      have hb₂_cov := hbd_cov (hB₂_sub hb₂)
      have hb₂_in₁ : b₂ ∈ Δ₁ \ L := by
        rcases hb₂_cov with h | h
        · exact h1 h
        · exact h2 h
      exact disjoint_left.mp hΔ₁₂_disj hb₂_in₁ (hB₂_in_Δ₂ hb₂)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exfalso
      obtain ⟨b₁, hb₁⟩ := hB₁_ne
      have hb₁_cov := hbd_cov (hB₁_sub hb₁)
      have hb₁_in₂ : b₁ ∈ Δ₂ \ L := by
        rcases hb₁_cov with h | h
        · exact h1 h
        · exact h2 h
      exact disjoint_left.mp hΔ₁₂_disj (hB₁_in_Δ₁ hb₁) hb₁_in₂
  have hΔ₀_int_sub : discInt Δ₀ ⊆ D \ L :=
    subset_sdiff.mpr ⟨(discInt_subset Δ₀).trans hΔ₀D, hΔ₀_disj_L⟩
  have hs_L : s ∈ L := by
    have : s ∈ L ∩ discBd D := by rw [hL_bd]; exact mem_insert s _
    exact this.1
  have ht_L : t ∈ L := by
    have : t ∈ L ∩ discBd D := by rw [hL_bd]; exact mem_insert_of_mem s rfl
    exact this.1
  rcases hsub_or_sub hΔ₀.isPreconnected_discInt hΔ₀_int_sub with hΔ₀_1 | hΔ₀_2
  · have hΔ₀_sub_Δ₁ : Δ₀ ⊆ Δ₁ :=
      hΔ₀.subset_closure_discInt.trans
        (closure_minimal (hΔ₀_1.trans sdiff_subset) hΔ₁.isClosed)
    have hdisj₂ : Disjoint (Δ₂ \ L) Δ₀ :=
      disjoint_of_subset_right hΔ₀_sub_Δ₁
        (disjoint_left.mpr fun x hx₂ hx₁ => hx₂.2 (hΔ_inter ▸ ⟨hx₁, hx₂.1⟩))
    rcases hA_one_each with ⟨_, hA₂_in₂⟩ | ⟨hA₁_in₂, _⟩
    · right
      intro R hR hRDL ⟨x, hxR, hxA₂⟩
      have hx_nst : x ∉ ({s, t} : Set EuclideanPlane) := by
        rintro (rfl | rfl)
        · exact (hRDL hxR).2 hs_L
        · exact (hRDL hxR).2 ht_L
      have hR_sub : R ⊆ Δ₂ \ L :=
        hsub_of_meet₂ hR hRDL ⟨x, hxR, hA₂_in₂ ⟨hxA₂, hx_nst⟩⟩
      exact disjoint_of_subset_left hR_sub hdisj₂
    · left
      intro R hR hRDL ⟨x, hxR, hxA₁⟩
      have hx_nst : x ∉ ({s, t} : Set EuclideanPlane) := by
        rintro (rfl | rfl)
        · exact (hRDL hxR).2 hs_L
        · exact (hRDL hxR).2 ht_L
      have hR_sub : R ⊆ Δ₂ \ L :=
        hsub_of_meet₂ hR hRDL ⟨x, hxR, hA₁_in₂ ⟨hxA₁, hx_nst⟩⟩
      exact disjoint_of_subset_left hR_sub hdisj₂
  · have hΔ₀_sub_Δ₂ : Δ₀ ⊆ Δ₂ :=
      hΔ₀.subset_closure_discInt.trans
        (closure_minimal (hΔ₀_2.trans sdiff_subset) hΔ₂.isClosed)
    have hdisj₁ : Disjoint (Δ₁ \ L) Δ₀ :=
      disjoint_of_subset_right hΔ₀_sub_Δ₂
        (disjoint_left.mpr fun x hx₁ hx₂ => hx₁.2 (hΔ_inter ▸ ⟨hx₁.1, hx₂⟩))
    rcases hA_one_each with ⟨hA₁_in₁, _⟩ | ⟨_, hA₂_in₁⟩
    · left
      intro R hR hRDL ⟨x, hxR, hxA₁⟩
      have hx_nst : x ∉ ({s, t} : Set EuclideanPlane) := by
        rintro (rfl | rfl)
        · exact (hRDL hxR).2 hs_L
        · exact (hRDL hxR).2 ht_L
      have hR_sub : R ⊆ Δ₁ \ L :=
        hsub_of_meet₁ hR hRDL ⟨x, hxR, hA₁_in₁ ⟨hxA₁, hx_nst⟩⟩
      exact disjoint_of_subset_left hR_sub hdisj₁
    · right
      intro R hR hRDL ⟨x, hxR, hxA₂⟩
      have hx_nst : x ∉ ({s, t} : Set EuclideanPlane) := by
        rintro (rfl | rfl)
        · exact (hRDL hxR).2 hs_L
        · exact (hRDL hxR).2 ht_L
      have hR_sub : R ⊆ Δ₁ \ L :=
        hsub_of_meet₁ hR hRDL ⟨x, hxR, hA₂_in₁ ⟨hxA₂, hx_nst⟩⟩
      exact disjoint_of_subset_left hR_sub hdisj₁

theorem graphDrawingSubgraphU_mono {G P₁ P₂ : Graph α β}
    (Γ : GraphDrawing G EuclideanPlane) (hle : P₁ ≤ P₂) :
    graphDrawingSubgraphU Γ P₁ ⊆ graphDrawingSubgraphU Γ P₂ :=
  union_subset_union (biUnion_mono hle.vertexSet_mono fun _ _ => Subset.rfl)
    (biUnion_mono hle.edgeSet_mono fun _ _ => Subset.rfl)

theorem graphDrawingSubgraphU_subset_U {G : Graph α β}
    (Γ : GraphDrawing G EuclideanPlane) (P : Graph α β) :
    graphDrawingSubgraphU Γ P ⊆ Γ.drawing.U := by
  refine union_subset (iUnion₂_subset fun v _ x hx => ?_) (iUnion₂_subset fun e _ => ?_)
  · rcases hx with ⟨hvG, rfl⟩
    exact Γ.drawing.V_subset_U (Γ.iso.vertexEquiv ⟨v, hvG⟩).2
  · by_cases heG : e ∈ E(G)
    · rw [graphDrawingEdgeSet_eq Γ heG]
      exact Γ.drawing.closure_subset_U (Γ.iso.edgeEquiv ⟨e, heG⟩).2
    · have hemp : graphDrawingEdgeSet Γ e = ∅ := by
        ext x; simp [graphDrawingEdgeSet, heG]
      rw [hemp, closure_empty]
      exact empty_subset _

theorem graphDrawingSubgraphU_subgraphUnion {G P₁ P₂ : Graph α β}
    (Γ : GraphDrawing G EuclideanPlane) (hP₁ : P₁ ≤ G) (hP₂ : P₂ ≤ G) :
    graphDrawingSubgraphU Γ (subgraphUnion G P₁ P₂) =
      graphDrawingSubgraphU Γ P₁ ∪ graphDrawingSubgraphU Γ P₂ := by
  simp only [graphDrawingSubgraphU, vertexSet_subgraphUnion, edgeSet_subgraphUnion hP₁ hP₂,
    biUnion_union]
  ext x
  simp only [mem_union]
  tauto

private theorem closure_inter_subset_V_drawing (Γ : Drawing EuclideanPlane) {e f : Set
  EuclideanPlane}
    (he : e ∈ Γ.E) (hf : f ∈ Γ.E) (hef : e ≠ f) : closure e ∩ closure f ⊆ Γ.V := by
  rintro y ⟨h₁, h₂⟩
  by_contra hy
  exact hef (Γ.edge_eq_of_mem he hf ((Γ.closure_diff_V he).subset ⟨h₁, hy⟩)
    ((Γ.closure_diff_V hf).subset ⟨h₂, hy⟩))

theorem graphDrawingSubgraphU_inter_V {G P : Graph α β}
    (Γ : GraphDrawing G EuclideanPlane) (hPG : P ≤ G) {x : EuclideanPlane}
    (hxP : x ∈ graphDrawingSubgraphU Γ P) (hxV : x ∈ Γ.drawing.V) :
    ∃ v ∈ V(P), x ∈ graphDrawingVertexSet Γ v := by
  let v₀ := Γ.iso.vertexEquiv.symm ⟨x, hxV⟩
  have hv₀_eq : (Γ.iso.vertexEquiv v₀).1 = x :=
    congrArg Subtype.val (Γ.iso.vertexEquiv.apply_symm_apply ⟨x, hxV⟩)
  have hx_mem : x ∈ graphDrawingVertexSet Γ v₀.1 := ⟨v₀.2, hv₀_eq⟩
  have hsub : graphDrawingVertexSet Γ v₀.1 ⊆ graphDrawingSubgraphU Γ P := by
    rw [graphDrawingVertexSet_eq_singleton Γ v₀.2, hv₀_eq, singleton_subset_iff]
    exact hxP
  exact ⟨v₀.1, mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU Γ hPG v₀.2 hsub, hx_mem⟩

theorem graphDrawingSubgraphU_inter_of_disjoint_edgeSet {G P₁ P₂ : Graph α β}
    (Γ : GraphDrawing G EuclideanPlane) (hP₁ : P₁ ≤ G) (hP₂ : P₂ ≤ G)
    (hdisjE : Disjoint E(P₁) E(P₂)) :
    graphDrawingSubgraphU Γ P₁ ∩ graphDrawingSubgraphU Γ P₂ =
      ⋃ v ∈ V(P₁) ∩ V(P₂), graphDrawingVertexSet Γ v := by
  apply subset_antisymm
  · rintro x ⟨hx₁, hx₂⟩
    by_cases hxV : x ∈ Γ.drawing.V
    · obtain ⟨v₁, hv₁P₁, hxv₁⟩ := graphDrawingSubgraphU_inter_V Γ hP₁ hx₁ hxV
      obtain ⟨v₂, hv₂P₂, hxv₂⟩ := graphDrawingSubgraphU_inter_V Γ hP₂ hx₂ hxV
      obtain rfl : v₁ = v₂ := graphDrawingVertexSet_inj Γ hxv₁ hxv₂
      exact mem_iUnion₂.mpr ⟨v₁, ⟨hv₁P₁, hv₂P₂⟩, hxv₁⟩
    · exfalso
      have hnot_vert : ∀ {P : Graph α β}, x ∉ ⋃ v ∈ V(P), graphDrawingVertexSet Γ v := by
        rintro P hx
        obtain ⟨v, _, hvG, rfl⟩ := mem_iUnion₂.mp hx
        exact hxV (Γ.iso.vertexEquiv ⟨v, hvG⟩).2
      have hx₁E : x ∈ ⋃ e ∈ E(P₁), closure (graphDrawingEdgeSet Γ e) :=
        hx₁.resolve_left hnot_vert
      have hx₂E : x ∈ ⋃ e ∈ E(P₂), closure (graphDrawingEdgeSet Γ e) :=
        hx₂.resolve_left hnot_vert
      obtain ⟨e₁, he₁, hxe₁⟩ := mem_iUnion₂.mp hx₁E
      obtain ⟨e₂, he₂, hxe₂⟩ := mem_iUnion₂.mp hx₂E
      have he₁G : e₁ ∈ E(G) := hP₁.edgeSet_mono he₁
      have he₂G : e₂ ∈ E(G) := hP₂.edgeSet_mono he₂
      rw [graphDrawingEdgeSet_eq Γ he₁G] at hxe₁
      rw [graphDrawingEdgeSet_eq Γ he₂G] at hxe₂
      have hne : (Γ.iso.edgeEquiv ⟨e₁, he₁G⟩).1 ≠ (Γ.iso.edgeEquiv ⟨e₂, he₂G⟩).1 := by
        intro h
        have heq : e₁ = e₂ :=
          congrArg Subtype.val (Γ.iso.edgeEquiv.injective (Subtype.ext h))
        exact disjoint_left.mp hdisjE he₁ (heq ▸ he₂)
      exact hxV (closure_inter_subset_V_drawing Γ.drawing
        (Γ.iso.edgeEquiv ⟨e₁, he₁G⟩).2 (Γ.iso.edgeEquiv ⟨e₂, he₂G⟩).2 hne ⟨hxe₁, hxe₂⟩)
  · refine iUnion₂_subset fun v ⟨hv₁, hv₂⟩ x hx =>
      ⟨graphDrawingVertexSet_subset_subgraphU_of_mem Γ hv₁ hx,
       graphDrawingVertexSet_subset_subgraphU_of_mem Γ hv₂ hx⟩

theorem nonempty_inter_vertexSet_of_nonempty_inter_subgraphU {G P₁ P₂ : Graph α β}
    (Γ : GraphDrawing G EuclideanPlane) (hP₁ : P₁ ≤ G) (hP₂ : P₂ ≤ G)
    (hne : (graphDrawingSubgraphU Γ P₁ ∩ graphDrawingSubgraphU Γ P₂).Nonempty) :
    (V(P₁) ∩ V(P₂)).Nonempty := by
  obtain ⟨x, hx₁, hx₂⟩ := hne
  by_cases hxV : x ∈ Γ.drawing.V
  · obtain ⟨v₁, hv₁P₁, hxv₁⟩ := graphDrawingSubgraphU_inter_V Γ hP₁ hx₁ hxV
    obtain ⟨v₂, hv₂P₂, hxv₂⟩ := graphDrawingSubgraphU_inter_V Γ hP₂ hx₂ hxV
    obtain rfl : v₁ = v₂ := graphDrawingVertexSet_inj Γ hxv₁ hxv₂
    exact ⟨v₁, hv₁P₁, hv₂P₂⟩
  · have hnot_vert : ∀ {P : Graph α β}, x ∉ ⋃ v ∈ V(P), graphDrawingVertexSet Γ v := by
      rintro P hx
      obtain ⟨v, _, hvG, rfl⟩ := mem_iUnion₂.mp hx
      exact hxV (Γ.iso.vertexEquiv ⟨v, hvG⟩).2
    obtain ⟨e₁, he₁, hxe₁⟩ := mem_iUnion₂.mp (hx₁.resolve_left hnot_vert)
    obtain ⟨e₂, he₂, hxe₂⟩ := mem_iUnion₂.mp (hx₂.resolve_left hnot_vert)
    have he₁G : e₁ ∈ E(G) := hP₁.edgeSet_mono he₁
    have he₂G : e₂ ∈ E(G) := hP₂.edgeSet_mono he₂
    rw [graphDrawingEdgeSet_eq Γ he₁G] at hxe₁
    rw [graphDrawingEdgeSet_eq Γ he₂G] at hxe₂
    by_cases heq : e₁ = e₂
    · subst heq
      obtain ⟨u₁, v₁, hl₁⟩ := P₁.exists_isLink_of_mem_edgeSet he₁
      obtain ⟨u₂, v₂, hl₂⟩ := P₂.exists_isLink_of_mem_edgeSet he₂
      rcases G.eq_or_eq_of_isLink_of_isLink (hl₂.mono hP₂) (hl₁.mono hP₁) with rfl | rfl
      · exact ⟨u₂, hl₁.left_mem, hl₂.left_mem⟩
      · exact ⟨u₂, hl₁.right_mem, hl₂.left_mem⟩
    · have hne_e : (Γ.iso.edgeEquiv ⟨e₁, he₁G⟩).1 ≠ (Γ.iso.edgeEquiv ⟨e₂, he₂G⟩).1 := fun h =>
        heq (congrArg Subtype.val (Γ.iso.edgeEquiv.injective (Subtype.ext h)))
      exact (hxV (closure_inter_subset_V_drawing Γ.drawing
        (Γ.iso.edgeEquiv ⟨e₁, he₁G⟩).2 (Γ.iso.edgeEquiv ⟨e₂, he₂G⟩).2 hne_e ⟨hxe₁, hxe₂⟩)).elim

theorem disjoint_subgraphU_of_disjoint_vertexSet {G P₁ P₂ : Graph α β}
    (Γ : GraphDrawing G EuclideanPlane) (hP₁ : P₁ ≤ G) (hP₂ : P₂ ≤ G)
    (hdisj : Disjoint V(P₁) V(P₂)) :
    Disjoint (graphDrawingSubgraphU Γ P₁) (graphDrawingSubgraphU Γ P₂) := by
  rw [disjoint_iff_inter_eq_empty]
  by_contra hne
  obtain ⟨v, hv₁, hv₂⟩ := nonempty_inter_vertexSet_of_nonempty_inter_subgraphU Γ hP₁ hP₂
    (nonempty_iff_ne_empty.mpr hne)
  exact disjoint_left.mp hdisj hv₁ hv₂

private def mapWalkGraphDrawing {G : Graph α β} (Γ : GraphDrawing G EuclideanPlane) :
    ∀ {u v : α} (W : GraphWalk G u v),
      GraphWalk Γ.drawing.toGraph
        (Γ.iso.vertexEquiv ⟨u, W.mem_vertexSet_of_mem_support W.start_mem_support⟩).1
        (Γ.iso.vertexEquiv ⟨v, W.mem_vertexSet_of_mem_support W.end_mem_support⟩).1
  | _, _, .nil hv => .nil (Γ.iso.vertexEquiv ⟨_, hv⟩).2
  | _, _, .cons hlink r =>
    .cons ((Γ.iso.isLink_iff ⟨_, hlink.edge_mem⟩ ⟨_, hlink.left_mem⟩ ⟨_, hlink.right_mem⟩).mp hlink)
      (mapWalkGraphDrawing Γ r)

private theorem mem_support_mapWalkGraphDrawing {G : Graph α β}
    (Γ : GraphDrawing G EuclideanPlane) {u v : α} (W : GraphWalk G u v) (x : EuclideanPlane) :
    x ∈ (mapWalkGraphDrawing Γ W).support ↔
      ∃ w ∈ W.support, x ∈ graphDrawingVertexSet Γ w := by
  induction W with
  | @nil u hv =>
    simp only [mapWalkGraphDrawing, GraphWalk.support, List.mem_singleton,
      graphDrawingVertexSet_eq_singleton Γ hv, mem_singleton_iff, exists_eq_left]
  | @cons u y v e hlink r ih =>
    simp only [mapWalkGraphDrawing, GraphWalk.support, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨w, hw, hxw⟩)
      · exact ⟨u, Or.inl rfl, ⟨hlink.left_mem, rfl⟩⟩
      · exact ⟨w, Or.inr hw, hxw⟩
    · rintro ⟨w, rfl | hw, hxw⟩
      · rw [graphDrawingVertexSet_eq_singleton Γ hlink.left_mem, mem_singleton_iff] at hxw
        exact Or.inl hxw
      · exact Or.inr ⟨w, hw, hxw⟩

private theorem mem_edges_mapWalkGraphDrawing {G : Graph α β}
    (Γ : GraphDrawing G EuclideanPlane) {u v : α} (W : GraphWalk G u v)
    (f : Set EuclideanPlane) :
    f ∈ (mapWalkGraphDrawing Γ W).edges ↔
      ∃ e ∈ W.edges, f = graphDrawingEdgeSet Γ e := by
  induction W with
  | nil _ =>
    simp [mapWalkGraphDrawing, GraphWalk.edges]
  | @cons u y v e hlink r ih =>
    simp only [mapWalkGraphDrawing, GraphWalk.edges, List.mem_cons, ih,
      ← graphDrawingEdgeSet_eq Γ hlink.edge_mem]
    constructor
    · rintro (rfl | ⟨e', he', rfl⟩)
      · exact ⟨e, Or.inl rfl, rfl⟩
      · exact ⟨e', Or.inr he', rfl⟩
    · rintro ⟨e', rfl | he', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨e', he', rfl⟩

private theorem isSimple_mapWalkGraphDrawing {G : Graph α β}
    (Γ : GraphDrawing G EuclideanPlane) {u v : α} {W : GraphWalk G u v}
    (hW : W.IsSimple) : (mapWalkGraphDrawing Γ W).IsSimple := by
  induction W with
  | nil _ =>
    exact List.nodup_singleton _
  | @cons u y v e hlink r ih =>
    obtain ⟨hu_not, hr⟩ := List.nodup_cons.mp hW
    refine List.nodup_cons.mpr ⟨fun hmem => ?_, ih hr⟩
    obtain ⟨w, hw, hxw⟩ := (mem_support_mapWalkGraphDrawing Γ r _).mp hmem
    have huw : u = w := graphDrawingVertexSet_inj Γ ⟨hlink.left_mem, rfl⟩ hxw
    exact hu_not (huw ▸ hw)

theorem isLineWithEnds_graphDrawingSubgraphU {G P : Graph α β}
    (Γ : GraphDrawing G EuclideanPlane) {u v : α}
    (hP : IsGraphPathWithEnds G P u v) (huv : u ≠ v) :
    have huG : u ∈ V(G) := hP.le.vertexSet_mono hP.left_mem
    have hvG : v ∈ V(G) := hP.le.vertexSet_mono hP.right_mem
    IsLineWithEnds (graphDrawingSubgraphU Γ P)
      (Γ.iso.vertexEquiv ⟨u, huG⟩).1 (Γ.iso.vertexEquiv ⟨v, hvG⟩).1 ∧
    (Γ.iso.vertexEquiv ⟨u, huG⟩).1 ≠ (Γ.iso.vertexEquiv ⟨v, hvG⟩).1 := by
  have huG : u ∈ V(G) := hP.le.vertexSet_mono hP.left_mem
  have hvG : v ∈ V(G) := hP.le.vertexSet_mono hP.right_mem
  have hne : (Γ.iso.vertexEquiv ⟨u, huG⟩).1 ≠ (Γ.iso.vertexEquiv ⟨v, hvG⟩).1 := fun h =>
    huv (congrArg Subtype.val (Γ.iso.vertexEquiv.injective (Subtype.ext h)))
  rcases hP with ⟨hPG, W, hW, hVP, hEP⟩
  obtain ⟨W_G, hs_G, he_G⟩ := exists_walk_up_of_le hPG W
  have hW_G_simple : W_G.IsSimple := by
    change W_G.support.Nodup
    rw [hs_G]
    exact hW
  have hline := GraphMinor.GM14.walk_isLine Γ.drawing (mapWalkGraphDrawing Γ W_G)
    (isSimple_mapWalkGraphDrawing Γ hW_G_simple) hne
  have hset_eq : ({x | x ∈ (mapWalkGraphDrawing Γ W_G).support} ∪
      ⋃ f ∈ {f | f ∈ (mapWalkGraphDrawing Γ W_G).edges}, closure f) =
      graphDrawingSubgraphU Γ P := by
    ext x
    simp only [graphDrawingSubgraphU, mem_union, mem_ofPred_eq, mem_support_mapWalkGraphDrawing,
      mem_iUnion, mem_edges_mapWalkGraphDrawing, hs_G, he_G, hVP, hEP]
    constructor
    · rintro (⟨w, hw, hxw⟩ | ⟨f, ⟨e, he, rfl⟩, hxf⟩)
      · exact Or.inl ⟨w, hw, hxw⟩
      · exact Or.inr ⟨e, he, hxf⟩
    · rintro (⟨w, hw, hxw⟩ | ⟨e, he, hxe⟩)
      · exact Or.inl ⟨w, hw, hxw⟩
      · exact Or.inr ⟨_, ⟨e, he, rfl⟩, hxe⟩
  rw [hset_eq] at hline
  exact ⟨hline, hne⟩

theorem isPreconnected_graphDrawingSubgraphU {G P : Graph α β}
    (Γ : GraphDrawing G EuclideanPlane) {u v : α}
    (hP : IsGraphPathWithEnds G P u v) :
    IsPreconnected (graphDrawingSubgraphU Γ P) := by
  by_cases huv : u = v
  · subst huv
    have huG : u ∈ V(G) := hP.le.vertexSet_mono hP.left_mem
    rcases hP with ⟨_, W, hW, hVP, hEP⟩
    cases W with
    | nil _ =>
      have hVP' : V(P) = {u} := by
        rw [hVP]; ext x; simp [GraphWalk.support]
      have hEP' : E(P) = ∅ := by
        rw [hEP]; ext e; simp [GraphWalk.edges]
      have heq : graphDrawingSubgraphU Γ P = {(Γ.iso.vertexEquiv ⟨u, huG⟩).1} := by
        simp [graphDrawingSubgraphU, hVP', hEP', graphDrawingVertexSet_eq_singleton Γ huG]
      rw [heq]
      exact isPreconnected_singleton
    | cons _ r =>
      exact ((List.nodup_cons.mp hW).1 r.end_mem_support).elim
  · exact IsLineWithEnds.isPreconnected (isLineWithEnds_graphDrawingSubgraphU Γ hP huv).1

theorem nonempty_inter_of_path_from_bar_to_disc {N : Neighborhood α β}
    (P_pres : Presentation N) {C R : Graph α β} {D : Set EuclideanPlane} {x z : α}
    (hCG : C ≤ N.G) (hD : IsClosedDisc D) (hD_sub : D ⊆ P_pres.Δ)
    (hD_bd : subBd D = graphDrawingSubgraphU P_pres.Γ C)
    (hR : IsGraphPathWithEnds N.G R x z) (hx : x ∈ N.Ω.bar)
    (hz : (P_pres.Γ.iso.vertexEquiv ⟨z, hR.le.vertexSet_mono hR.right_mem⟩).1 ∈ D) :
    (V(R) ∩ V(C)).Nonempty := by
  have hxG : x ∈ V(N.G) := hR.le.vertexSet_mono hR.left_mem
  have hzG : z ∈ V(N.G) := hR.le.vertexSet_mono hR.right_mem
  set px := (P_pres.Γ.iso.vertexEquiv ⟨x, hxG⟩).1
  set pz := (P_pres.Γ.iso.vertexEquiv ⟨z, hzG⟩).1
  have hpx_bd : px ∈ subBd P_pres.Δ :=
    (P_pres.mem_bd_Δ_iff x hxG).mpr hx ⟨hxG, rfl⟩
  rw [GraphMinor.GM11.subBd_eq_frontier] at hpx_bd
  have hpx_not_int : px ∉ interior P_pres.Δ := hpx_bd.2
  have hpx_R : px ∈ graphDrawingSubgraphU P_pres.Γ R :=
    graphDrawingVertexSet_subset_subgraphU_of_mem P_pres.Γ hR.left_mem ⟨hxG, rfl⟩
  have hpz_R : pz ∈ graphDrawingSubgraphU P_pres.Γ R :=
    graphDrawingVertexSet_subset_subgraphU_of_mem P_pres.Γ hR.right_mem ⟨hzG, rfl⟩
  have hnot_disj : ¬ Disjoint (graphDrawingSubgraphU P_pres.Γ R) (frontier D) := by
    intro hdisj
    rcases GraphMinor.GM14.subset_or_disjoint_of_frontier hD.isClosed
        (isPreconnected_graphDrawingSubgraphU P_pres.Γ hR) hdisj with hin | hout
    · have hpx_fr : px ∈ frontier D :=
        ⟨subset_closure (hin hpx_R), fun hi => hpx_not_int (interior_mono hD_sub hi)⟩
      exact disjoint_left.mp hdisj hpx_R hpx_fr
    · exact disjoint_left.mp hout hpz_R hz
  rw [← GraphMinor.GM11.subBd_eq_frontier, hD_bd] at hnot_disj
  exact nonempty_inter_vertexSet_of_nonempty_inter_subgraphU P_pres.Γ hR.le hCG
    (not_disjoint_iff_nonempty_inter.mp hnot_disj)

private theorem detour_dichotomy {G C P_sub : Graph α β}
    (Γ : GraphDrawing G EuclideanPlane) {D : Set EuclideanPlane} {v v' : α}
    (hCG : C ≤ G) (hD : IsClosedDisc D)
    (hD_bd : subBd D = graphDrawingSubgraphU Γ C)
    (hP_sub : IsGraphPathWithEnds G P_sub v v') (hvv' : v ≠ v')
    (hVC : V(P_sub) ∩ V(C) = {v, v'}) (hEC : Disjoint E(P_sub) E(C)) :
    have hvG : v ∈ V(G) := hP_sub.le.vertexSet_mono hP_sub.left_mem
    have hv'G : v' ∈ V(G) := hP_sub.le.vertexSet_mono hP_sub.right_mem
    let s_pt := (Γ.iso.vertexEquiv ⟨v, hvG⟩).1
    let t_pt := (Γ.iso.vertexEquiv ⟨v', hv'G⟩).1
    IsLineWithEnds (graphDrawingSubgraphU Γ P_sub) s_pt t_pt ∧
    s_pt ≠ t_pt ∧
    graphDrawingSubgraphU Γ P_sub ∩ discBd D = {s_pt, t_pt} ∧
    (graphDrawingSubgraphU Γ P_sub ∩ D = {s_pt, t_pt} ∨
      graphDrawingSubgraphU Γ P_sub ⊆ D) := by
  have hvG : v ∈ V(G) := hP_sub.le.vertexSet_mono hP_sub.left_mem
  have hv'G : v' ∈ V(G) := hP_sub.le.vertexSet_mono hP_sub.right_mem
  set s_pt := (Γ.iso.vertexEquiv ⟨v, hvG⟩).1
  set t_pt := (Γ.iso.vertexEquiv ⟨v', hv'G⟩).1
  obtain ⟨hline, hne⟩ := isLineWithEnds_graphDrawingSubgraphU Γ hP_sub hvv'
  have hbd_inter : graphDrawingSubgraphU Γ P_sub ∩ discBd D = {s_pt, t_pt} := by
    rw [← Surface.subBd_eq_discBd_euclideanPlane hD, hD_bd,
      graphDrawingSubgraphU_inter_of_disjoint_edgeSet Γ hP_sub.le hCG hEC, hVC,
      biUnion_insert, biUnion_singleton,
      graphDrawingVertexSet_eq_singleton Γ hvG, graphDrawingVertexSet_eq_singleton Γ hv'G,
      singleton_union]
  refine ⟨hline, hne, hbd_inter, ?_⟩
  have hpre : IsPreconnected (graphDrawingSubgraphU Γ P_sub \ {s_pt, t_pt}) :=
    GraphMinor.GM14.IsLineWithEnds.isPreconnected_sdiff_pair hline
  have hdisj_fr : Disjoint (graphDrawingSubgraphU Γ P_sub \ {s_pt, t_pt}) (frontier D) := by
    rw [Surface.plane_disc_frontier hD, disjoint_left]
    rintro x ⟨hxP, hx_nst⟩ hx_bd
    exact hx_nst (hbd_inter ▸ ⟨hxP, hx_bd⟩)
  have hs_in : s_pt ∈ graphDrawingSubgraphU Γ P_sub ∩ discBd D := by
    rw [hbd_inter]; exact mem_insert s_pt _
  have ht_in : t_pt ∈ graphDrawingSubgraphU Γ P_sub ∩ discBd D := by
    rw [hbd_inter]; exact mem_insert_of_mem s_pt rfl
  rcases GraphMinor.GM14.subset_or_disjoint_of_frontier hD.isClosed hpre hdisj_fr with hin | hout
  · right
    intro x hx
    by_cases hx_st : x ∈ ({s_pt, t_pt} : Set EuclideanPlane)
    · rcases hx_st with rfl | rfl
      · exact Surface.discBd_subset D hs_in.2
      · exact Surface.discBd_subset D ht_in.2
    · exact hin ⟨hx, hx_st⟩
  · left
    apply subset_antisymm
    · rintro x ⟨hxP, hxD⟩
      by_contra hx_nst
      exact disjoint_left.mp hout ⟨hxP, hx_nst⟩ hxD
    · rintro x (rfl | rfl)
      · exact ⟨hs_in.1, Surface.discBd_subset D hs_in.2⟩
      · exact ⟨ht_in.1, Surface.discBd_subset D ht_in.2⟩

theorem circuit_two_arcs_drawing {G C : Graph α β}
    (Γ : GraphDrawing G EuclideanPlane) {D : Set EuclideanPlane} {v v' : α}
    (hC : IsGraphCircuit G C) (hD : IsClosedDisc D)
    (hD_bd : subBd D = graphDrawingSubgraphU Γ C)
    (hvC : v ∈ V(C)) (hv'C : v' ∈ V(C)) (hvv' : v ≠ v') :
    have hvG : v ∈ V(G) := hC.1.vertexSet_mono hvC
    have hv'G : v' ∈ V(G) := hC.1.vertexSet_mono hv'C
    let s_pt := (Γ.iso.vertexEquiv ⟨v, hvG⟩).1
    let t_pt := (Γ.iso.vertexEquiv ⟨v', hv'G⟩).1
    ∃ Q₁ Q₂ : Graph α β,
      Q₁ ≤ C ∧ Q₂ ≤ C ∧
      IsGraphPathWithEnds G Q₁ v v' ∧ IsGraphPathWithEnds G Q₂ v v' ∧
      V(Q₁) ∩ V(Q₂) = {v, v'} ∧ Disjoint E(Q₁) E(Q₂) ∧
      subgraphUnion G Q₁ Q₂ = C ∧
      IsLineWithEnds (graphDrawingSubgraphU Γ Q₁) s_pt t_pt ∧
      IsLineWithEnds (graphDrawingSubgraphU Γ Q₂) s_pt t_pt ∧
      graphDrawingSubgraphU Γ Q₁ ∩ graphDrawingSubgraphU Γ Q₂ = {s_pt, t_pt} ∧
      graphDrawingSubgraphU Γ Q₁ ∪ graphDrawingSubgraphU Γ Q₂ = discBd D := by
  have hvG : v ∈ V(G) := hC.1.vertexSet_mono hvC
  have hv'G : v' ∈ V(G) := hC.1.vertexSet_mono hv'C
  set s_pt := (Γ.iso.vertexEquiv ⟨v, hvG⟩).1
  set t_pt := (Γ.iso.vertexEquiv ⟨v', hv'G⟩).1
  obtain ⟨Q₁, Q₂, hQ₁C, hQ₂C, hQ₁, hQ₂, _, _, hV, hE, hunion⟩ :=
    hC.exists_two_paths hvC hv'C hvv'
  obtain ⟨hline₁, _⟩ := isLineWithEnds_graphDrawingSubgraphU Γ hQ₁ hvv'
  obtain ⟨hline₂, _⟩ := isLineWithEnds_graphDrawingSubgraphU Γ hQ₂ hvv'
  have hinter : graphDrawingSubgraphU Γ Q₁ ∩ graphDrawingSubgraphU Γ Q₂ = {s_pt, t_pt} := by
    rw [graphDrawingSubgraphU_inter_of_disjoint_edgeSet Γ hQ₁.le hQ₂.le hE, hV,
      biUnion_insert, biUnion_singleton,
      graphDrawingVertexSet_eq_singleton Γ hvG, graphDrawingVertexSet_eq_singleton Γ hv'G,
      singleton_union]
  have hunion_U : graphDrawingSubgraphU Γ Q₁ ∪ graphDrawingSubgraphU Γ Q₂ = discBd D := by
    rw [← graphDrawingSubgraphU_subgraphUnion Γ hQ₁.le hQ₂.le, hunion, ← hD_bd,
      Surface.subBd_eq_discBd_euclideanPlane hD]
  exact ⟨Q₁, Q₂, hQ₁C, hQ₂C, hQ₁, hQ₂, hV, hE, hunion, hline₁, hline₂, hinter, hunion_U⟩

private theorem move2_replace_with_arc {N : Neighborhood α β} (P_pres : Presentation N)
    {s : ℕ} {X : Set α}
    {C : Fin s → Graph α β} {P : Fin X.ncard → Graph α β}
    {D : Fin s → Set EuclideanPlane}
    (hC_circ : ∀ m, IsGraphCircuit N.G (C m))
    (hC_disj : Pairwise (fun m₁ m₂ => Disjoint V(C m₁) V(C m₂)))
    (hD_disc : ∀ m, IsClosedDisc (D m) ∧ subBd (D m) = graphDrawingSubgraphU P_pres.Γ (C m))
    (hD_bounds : ∀ m, P_pres.Δ₀ ⊆ D m ∧ D m ⊆ P_pres.Δ)
    (hD_mono : ∀ m₁ m₂, m₁ ≤ m₂ → D m₁ ⊆ D m₂)
    (hP_path : ∀ k, IsFromToPath N.G (P k) X N.Ω₀.bar)
    (hP_disj : Pairwise (fun k₁ k₂ => Disjoint V(P k₁) V(P k₂)))
    {j : Fin s} {i' : Fin X.ncard} {P_sub Q_keep Q_drop : Graph α β} {v v' : α}
    {Δ_keep : Set EuclideanPlane}
    (hP_sub_le : P_sub ≤ P i')
    (hP_sub : IsGraphPathWithEnds N.G P_sub v v') (hvv' : v ≠ v')
    (hVC : V(P_sub) ∩ V(C j) = {v, v'}) (hEC : Disjoint E(P_sub) E(C j))
    (hQ_keepC : Q_keep ≤ C j) (hQ_dropC : Q_drop ≤ C j)
    (hQ_keep : IsGraphPathWithEnds N.G Q_keep v v')
    (hQ_drop : IsGraphPathWithEnds N.G Q_drop v v')
    (hQ_disjE : Disjoint E(Q_keep) E(Q_drop))
    (hΔ_keep_Y : Δ_keep ⊆ P_pres.Δ) (hΔ_keep : IsClosedDisc Δ_keep)
    (hΔ_keep_bd : discBd Δ_keep =
      graphDrawingSubgraphU P_pres.Γ P_sub ∪ graphDrawingSubgraphU P_pres.Γ Q_keep)
    (hDj_sub : D j ⊆ Δ_keep)
    (hP_sub_disj_C : ∀ m : Fin s, m ≠ j → Disjoint V(P_sub) V(C m))
    (hP_sub_in_D : ∀ m : Fin s, j < m → graphDrawingSubgraphU P_pres.Γ P_sub ⊆ D m) :
    ∃ C' : Fin s → Graph α β,
      N.IsNest P_pres C' ∧
      totalUnionEdges C' P < totalUnionEdges C P := by
  classical
  let C_new := subgraphUnion N.G P_sub Q_keep
  let C' := Function.update C j C_new
  let D' := Function.update D j Δ_keep
  have hVP_Q : V(P_sub) ∩ V(Q_keep) = {v, v'} := by
    apply subset_antisymm
    · intro u ⟨huP, huQ⟩
      have : u ∈ V(P_sub) ∩ V(C j) := ⟨huP, hQ_keepC.vertexSet_mono huQ⟩
      rwa [hVC] at this
    · rintro u (rfl | rfl)
      · exact ⟨hP_sub.left_mem, hQ_keep.left_mem⟩
      · exact ⟨hP_sub.right_mem, hQ_keep.right_mem⟩
  have hEP_Q : Disjoint E(P_sub) E(Q_keep) :=
    disjoint_of_subset_right hQ_keepC.edgeSet_mono hEC
  have hC_new_circ : IsGraphCircuit N.G C_new :=
    isGraphCircuit_subgraphUnion hP_sub hQ_keep hvv' hVP_Q hEP_Q
  have hC'_nest : N.IsNest P_pres C' := by
    refine ⟨?_, ?_, D', ?_, ?_, ?_⟩
    · intro m
      by_cases hmj : m = j
      · subst hmj; simp only [C', Function.update_self]; exact hC_new_circ
      · simp only [C', Function.update_of_ne hmj]; exact hC_circ m
    · intro m₁ m₂ hm₁₂
      by_cases hm₁ : m₁ = j
      · subst hm₁
        have hm₂ : m₂ ≠ m₁ := hm₁₂.symm
        simp only [C', Function.update_self, Function.update_of_ne hm₂]
        have hsub : V(C_new) ⊆ V(P_sub) ∪ V(C m₁) :=
          union_subset_union Subset.rfl hQ_keepC.vertexSet_mono
        exact disjoint_of_subset_left hsub
          (disjoint_union_left.mpr ⟨hP_sub_disj_C m₂ hm₂, hC_disj hm₁₂⟩)
      · by_cases hm₂ : m₂ = j
        · subst hm₂
          simp only [C', Function.update_of_ne hm₁, Function.update_self]
          have hsub : V(C_new) ⊆ V(P_sub) ∪ V(C m₂) :=
            union_subset_union Subset.rfl hQ_keepC.vertexSet_mono
          exact disjoint_of_subset_right hsub
            (disjoint_union_right.mpr ⟨(hP_sub_disj_C m₁ hm₁).symm, hC_disj hm₁₂⟩)
        · simp only [C', Function.update_of_ne hm₁, Function.update_of_ne hm₂]
          exact hC_disj hm₁₂
    · intro m
      by_cases hmj : m = j
      · subst hmj
        simp only [D', C', C_new, Function.update_self]
        refine ⟨hΔ_keep, ?_⟩
        rw [Surface.subBd_eq_discBd_euclideanPlane hΔ_keep, hΔ_keep_bd,
          graphDrawingSubgraphU_subgraphUnion P_pres.Γ hP_sub.le hQ_keep.le]
      · simp only [D', C', Function.update_of_ne hmj]
        exact hD_disc m
    · intro m
      by_cases hmj : m = j
      · subst hmj
        simp only [D', Function.update_self]
        exact ⟨(hD_bounds m).1.trans hDj_sub, hΔ_keep_Y⟩
      · simp only [D', Function.update_of_ne hmj]
        exact hD_bounds m
    · intro m₁ m₂ hm₁₂
      by_cases hm₁ : m₁ = j
      · subst hm₁
        by_cases hm₂ : m₂ = m₁
        · subst hm₂; exact Subset.rfl
        · simp only [D', Function.update_self, Function.update_of_ne hm₂]
          have hlt : m₁ < m₂ := lt_of_le_of_ne hm₁₂ (Ne.symm hm₂)
          refine disc_mono_of_subset P_pres.isClosedDisc_Δ hΔ_keep_Y (hD_bounds m₂).2
            hΔ_keep (hD_disc m₂).1 ?_
          rw [hΔ_keep_bd]
          refine union_subset (hP_sub_in_D m₂ hlt) ?_
          have hQ_sub : graphDrawingSubgraphU P_pres.Γ Q_keep ⊆ D m₁ := by
            refine (graphDrawingSubgraphU_mono P_pres.Γ hQ_keepC).trans ?_
            rw [← (hD_disc m₁).2, Surface.subBd_eq_discBd_euclideanPlane (hD_disc m₁).1]
            exact Surface.discBd_subset (D m₁)
          exact hQ_sub.trans (hD_mono m₁ m₂ hm₁₂)
      · by_cases hm₂ : m₂ = j
        · subst hm₂
          simp only [D', Function.update_of_ne hm₁, Function.update_self]
          exact (hD_mono m₁ m₂ hm₁₂).trans hDj_sub
        · simp only [D', Function.update_of_ne hm₁, Function.update_of_ne hm₂]
          exact hD_mono m₁ m₂ hm₁₂
  have hPG : ∀ k, P k ≤ N.G := fun k => by
    obtain ⟨_, _, hft⟩ := hP_path k
    exact hft.1.le
  have hCG : ∀ m, C m ≤ N.G := fun m => (hC_circ m).1
  obtain ⟨x, y, hPi'_ft⟩ := hP_path i'
  obtain ⟨e₀, he₀_drop, he₀_not_P⟩ :=
    exists_edge_not_mem_iUnion_of_path hPG hP_disj hPi'_ft.1 hP_sub hP_sub_le hQ_drop hvv'
      (disjoint_of_subset_right hQ_dropC.edgeSet_mono hEC)
  have hlt := totalUnionEdges_lt_of_replace_circuit N.finite_E hCG hPG hC_disj
    hP_sub_le hQ_keepC hQ_dropC hQ_disjE he₀_drop
    (fun k hek => he₀_not_P (mem_iUnion.mpr ⟨k, hek⟩))
  exact ⟨C', hC'_nest, hlt⟩

private theorem move2_outer_detour {N : Neighborhood α β} (P_pres : Presentation N)
    {s : ℕ} {X : Set α} (hX_sub : X ⊆ N.Ω.bar)
    {C : Fin s → Graph α β} {P : Fin X.ncard → Graph α β}
    {D : Fin s → Set EuclideanPlane}
    (hC_circ : ∀ m, IsGraphCircuit N.G (C m))
    (hC_disj : Pairwise (fun m₁ m₂ => Disjoint V(C m₁) V(C m₂)))
    (hD_disc : ∀ m, IsClosedDisc (D m) ∧ subBd (D m) = graphDrawingSubgraphU P_pres.Γ (C m))
    (hD_bounds : ∀ m, P_pres.Δ₀ ⊆ D m ∧ D m ⊆ P_pres.Δ)
    (hD_mono : ∀ m₁ m₂, m₁ ≤ m₂ → D m₁ ⊆ D m₂)
    (hP_path : ∀ k, IsFromToPath N.G (P k) X N.Ω₀.bar)
    (hP_disj : Pairwise (fun k₁ k₂ => Disjoint V(P k₁) V(P k₂)))
    {j : Fin s}
    (hafter : ∀ j' : Fin s, j < j' → ∀ k : Fin X.ncard,
      IsGraphPath N.G (subgraphInter N.G (P k) (C j')))
    {i' : Fin X.ncard} {P_sub : Graph α β} {v v' : α}
    (hP_sub_le : P_sub ≤ P i')
    (hP_sub : IsGraphPathWithEnds N.G P_sub v v') (hvv' : v ≠ v')
    (hVC : V(P_sub) ∩ V(C j) = {v, v'}) (hEC : Disjoint E(P_sub) E(C j))
    (houter : graphDrawingSubgraphU P_pres.Γ P_sub ∩ D j =
      {(P_pres.Γ.iso.vertexEquiv ⟨v, hP_sub.le.vertexSet_mono hP_sub.left_mem⟩).1,
       (P_pres.Γ.iso.vertexEquiv ⟨v', hP_sub.le.vertexSet_mono hP_sub.right_mem⟩).1}) :
    ∃ C' : Fin s → Graph α β,
      N.IsNest P_pres C' ∧
      totalUnionEdges C' P < totalUnionEdges C P := by
  have hvC : v ∈ V(C j) := by
    have : v ∈ V(P_sub) ∩ V(C j) := by rw [hVC]; exact mem_insert v _
    exact this.2
  have hv'C : v' ∈ V(C j) := by
    have : v' ∈ V(P_sub) ∩ V(C j) := by rw [hVC]; exact mem_insert_of_mem v rfl
    exact this.2
  have hvG : v ∈ V(N.G) := hP_sub.le.vertexSet_mono hP_sub.left_mem
  have hv'G : v' ∈ V(N.G) := hP_sub.le.vertexSet_mono hP_sub.right_mem
  set s_pt := (P_pres.Γ.iso.vertexEquiv ⟨v, hvG⟩).1
  set t_pt := (P_pres.Γ.iso.vertexEquiv ⟨v', hv'G⟩).1
  have hs_Dj : s_pt ∈ D j := by
    have : s_pt ∈ graphDrawingSubgraphU P_pres.Γ P_sub ∩ D j := by
      rw [houter]; exact mem_insert s_pt _
    exact this.2
  have ht_Dj : t_pt ∈ D j := by
    have : t_pt ∈ graphDrawingSubgraphU P_pres.Γ P_sub ∩ D j := by
      rw [houter]; exact mem_insert_of_mem s_pt rfl
    exact this.2
  have hP_sub_disj_C : ∀ m : Fin s, m ≠ j → Disjoint V(P_sub) V(C m) := by
    intro m hmj
    rcases lt_or_gt_of_ne hmj with hlt | hgt
    · refine disjoint_left.mpr fun w hwP hwCm => ?_
      have hwG : w ∈ V(N.G) := hP_sub.le.vertexSet_mono hwP
      let pw := (P_pres.Γ.iso.vertexEquiv ⟨w, hwG⟩).1
      have hpw_P : pw ∈ graphDrawingSubgraphU P_pres.Γ P_sub :=
        graphDrawingVertexSet_subset_subgraphU_of_mem P_pres.Γ hwP ⟨hwG, rfl⟩
      have hpw_Cm : pw ∈ graphDrawingSubgraphU P_pres.Γ (C m) :=
        graphDrawingVertexSet_subset_subgraphU_of_mem P_pres.Γ hwCm ⟨hwG, rfl⟩
      rw [← (hD_disc m).2, Surface.subBd_eq_discBd_euclideanPlane (hD_disc m).1] at hpw_Cm
      have hpw_Dj : pw ∈ D j :=
        hD_mono m j (le_of_lt hlt) (Surface.discBd_subset (D m) hpw_Cm)
      have hpw_st : pw ∈ ({s_pt, t_pt} : Set EuclideanPlane) :=
        houter ▸ ⟨hpw_P, hpw_Dj⟩
      have hw_Cj : w ∈ V(C j) := by
        rcases hpw_st with h | h
        · have : w = v := congrArg Subtype.val (P_pres.Γ.iso.vertexEquiv.injective (Subtype.ext h))
          exact this ▸ hvC
        · have : w = v' := congrArg Subtype.val (P_pres.Γ.iso.vertexEquiv.injective (Subtype.ext h))
          exact this ▸ hv'C
      exact disjoint_left.mp (hC_disj hmj) hwCm hw_Cj
    · obtain ⟨x, y, hPi'_ft, hxX, _⟩ := hP_path i'
      have hx_bar : x ∈ N.Ω.bar := hX_sub (by
        have : x ∈ V(P i') ∩ X := by rw [hxX]; exact mem_singleton x
        exact this.2)
      obtain ⟨v₁, hv₁_eq, R₁, hR₁_le, hR₁, hR₁_inter⟩ :=
        exists_prefix_disjoint_subpath hPi'_ft hP_sub hP_sub_le
      have hv₁_Dm : (P_pres.Γ.iso.vertexEquiv ⟨v₁, hR₁.le.vertexSet_mono hR₁.right_mem⟩).1 ∈ D m
        := by
        have hv₁_Dj : (P_pres.Γ.iso.vertexEquiv ⟨v₁, hR₁.le.vertexSet_mono hR₁.right_mem⟩).1 ∈ D j
          := by
          rcases hv₁_eq with rfl | rfl
          · exact hs_Dj
          · exact ht_Dj
        exact hD_mono j m (le_of_lt hgt) hv₁_Dj
      have hR₁_meet : (V(R₁) ∩ V(C m)).Nonempty :=
        nonempty_inter_of_path_from_bar_to_disc P_pres (hC_circ m).1 (hD_disc m).1
          (hD_bounds m).2 (hD_disc m).2 hR₁ hx_bar hv₁_Dm
      have hv_not : v ∉ V(C m) := disjoint_left.mp (hC_disj hmj.symm) hvC
      have hv'_not : v' ∉ V(C m) := disjoint_left.mp (hC_disj hmj.symm) hv'C
      exact disjoint_detour_of_isGraphPath_inter (hC_circ m).1 hPi'_ft hP_sub hP_sub_le hv₁_eq
        hR₁_le hR₁ hR₁_inter hv_not hv'_not (hafter m hgt i') hR₁_meet
  have hP_sub_in_D : ∀ m : Fin s, j < m → graphDrawingSubgraphU P_pres.Γ P_sub ⊆ D m := by
    intro m hjm
    have hdisj_U := disjoint_subgraphU_of_disjoint_vertexSet P_pres.Γ hP_sub.le (hC_circ m).1
      (hP_sub_disj_C m (ne_of_gt hjm))
    rw [← (hD_disc m).2, GraphMinor.GM11.subBd_eq_frontier] at hdisj_U
    rcases GraphMinor.GM14.subset_or_disjoint_of_frontier (hD_disc m).1.isClosed
        (isPreconnected_graphDrawingSubgraphU P_pres.Γ hP_sub) hdisj_U with hin | hout
    · exact hin
    · exfalso
      have hs_P : s_pt ∈ graphDrawingSubgraphU P_pres.Γ P_sub :=
        graphDrawingVertexSet_subset_subgraphU_of_mem P_pres.Γ hP_sub.left_mem ⟨hvG, rfl⟩
      exact disjoint_left.mp hout hs_P (hD_mono j m (le_of_lt hjm) hs_Dj)
  obtain ⟨hline_P, _, _, _⟩ :=
    detour_dichotomy P_pres.Γ (hC_circ j).1 (hD_disc j).1 (hD_disc j).2 hP_sub hvv' hVC hEC
  obtain ⟨Q₁, Q₂, hQ₁C, hQ₂C, hQ₁, hQ₂, _, hQ_E, _, hline₁, hline₂, hQ_inter_U, hQ_union_U⟩ :=
    circuit_two_arcs_drawing P_pres.Γ (hC_circ j) (hD_disc j).1 (hD_disc j).2 hvC hv'C hvv'
  have hP_sub_Y : graphDrawingSubgraphU P_pres.Γ P_sub ⊆ P_pres.Δ :=
    (graphDrawingSubgraphU_subset_U P_pres.Γ P_sub).trans (P_pres.U_subset.trans sdiff_subset)
  rcases outer_chord_disc_contains P_pres.isClosedDisc_Δ (hD_disc j).1 (hD_bounds j).2
      hline₁ hline₂ hline_P hQ_inter_U hQ_union_U hP_sub_Y houter with
    ⟨Δ₁, hΔ₁Y, hΔ₁, hΔ₁_bd, hDj_Δ₁⟩ | ⟨Δ₂, hΔ₂Y, hΔ₂, hΔ₂_bd, hDj_Δ₂⟩
  · exact move2_replace_with_arc P_pres hC_circ hC_disj hD_disc hD_bounds hD_mono hP_path hP_disj
      hP_sub_le hP_sub hvv' hVC hEC hQ₁C hQ₂C hQ₁ hQ₂ hQ_E hΔ₁Y hΔ₁ hΔ₁_bd hDj_Δ₁
      hP_sub_disj_C hP_sub_in_D
  · exact move2_replace_with_arc P_pres hC_circ hC_disj hD_disc hD_bounds hD_mono hP_path hP_disj
      hP_sub_le hP_sub hvv' hVC hEC hQ₂C hQ₁C hQ₂ hQ₁ hQ_E.symm hΔ₂Y hΔ₂ hΔ₂_bd hDj_Δ₂
      hP_sub_disj_C hP_sub_in_D

theorem isClosedDisc_Δ₀_and_mem_of_mem_bar₀ {N : Neighborhood α β}
    (P_pres : Presentation N) {y : α} (hy : y ∈ N.Ω₀.bar) :
    have hyG : y ∈ V(N.G) := N.bar₀_subset hy
    IsClosedDisc P_pres.Δ₀ ∧
    (P_pres.Γ.iso.vertexEquiv ⟨y, hyG⟩).1 ∈ P_pres.Δ₀ := by
  have hyG : y ∈ V(N.G) := N.bar₀_subset hy
  rcases P_pres.agrees_Δ₀ with ⟨_, hbar_emp⟩ | ⟨hΔ₀_disc, _⟩
  · exact (Set.notMem_empty y (hbar_emp ▸ hy)).elim
  · refine ⟨hΔ₀_disc, ?_⟩
    have hpy_bd : (P_pres.Γ.iso.vertexEquiv ⟨y, hyG⟩).1 ∈ subBd P_pres.Δ₀ :=
      (P_pres.mem_bd_Δ₀_iff y hyG).mpr hy ⟨hyG, rfl⟩
    rw [Surface.subBd_eq_discBd_euclideanPlane hΔ₀_disc] at hpy_bd
    exact Surface.discBd_subset P_pres.Δ₀ hpy_bd

private theorem prop2_inner_walk {N : Neighborhood α β} (P_pres : Presentation N)
    {C_j P_i' : Graph α β} {D_j : Set EuclideanPlane} {y : α}
    (hC : IsGraphCircuit N.G C_j) (hD : IsClosedDisc D_j)
    (hD_bd : subBd D_j = graphDrawingSubgraphU P_pres.Γ C_j)
    (hΔ₀_sub : P_pres.Δ₀ ⊆ D_j) (hy : y ∈ N.Ω₀.bar)
    (hdetour_in : ∀ {u u' : α} {P_sub : Graph α β},
      P_sub ≤ P_i' → IsGraphPathWithEnds N.G P_sub u u' → u ≠ u' →
      V(P_sub) ∩ V(C_j) = {u, u'} → Disjoint E(P_sub) E(C_j) →
      graphDrawingSubgraphU P_pres.Γ P_sub ⊆ D_j) :
    ∀ (n : ℕ) {v : α} (W : GraphWalk N.G v y),
      W.length = n → W.IsSimple → v ∈ V(C_j) → walkSubgraph W ≤ P_i' →
      graphDrawingSubgraphU P_pres.Γ (walkSubgraph W) ⊆ D_j := by
  have hyG : y ∈ V(N.G) := N.bar₀_subset hy
  obtain ⟨_, hpy_Δ₀⟩ := isClosedDisc_Δ₀_and_mem_of_mem_bar₀ P_pres hy
  have hpy_Dj : (P_pres.Γ.iso.vertexEquiv ⟨y, hyG⟩).1 ∈ D_j := hΔ₀_sub hpy_Δ₀
  have hCj_Dj : graphDrawingSubgraphU P_pres.Γ C_j ⊆ D_j := by
    rw [← hD_bd, Surface.subBd_eq_discBd_euclideanPlane hD]
    exact Surface.discBd_subset D_j
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro v W hlen hW_s hvC hW_le
    cases W with
    | @nil v hvG =>
      refine union_subset (iUnion₂_subset fun u hu => ?_) (iUnion₂_subset fun e he => ?_)
      · rw [vertexSet_walkSubgraph, mem_ofPred_eq, GraphWalk.support_nil,
          List.mem_singleton] at hu
        subst hu
        exact (graphDrawingVertexSet_subset_subgraphU_of_mem P_pres.Γ hvC).trans hCj_Dj
      · rw [edgeSet_walkSubgraph, mem_ofPred_eq, GraphWalk.edges_nil] at he
        exact (List.not_mem_nil he).elim
    | @cons v w _ e hl r =>
      have hv_not_r : v ∉ r.support := (List.nodup_cons.mp hW_s).1
      have hr_s : r.IsSimple := (List.nodup_cons.mp hW_s).2
      have hr_le_cons : walkSubgraph r ≤ walkSubgraph (GraphWalk.cons hl r) := by
        rw [(Compatible.of_le_le (walkSubgraph_le r) (walkSubgraph_le _)).le_iff,
          vertexSet_walkSubgraph, vertexSet_walkSubgraph,
          edgeSet_walkSubgraph, edgeSet_walkSubgraph]
        exact ⟨fun x hx => List.mem_cons_of_mem v hx, fun f hf => List.mem_cons_of_mem e hf⟩
      by_cases heC : e ∈ E(C_j)
      · have hlC : C_j.IsLink e v w := (hC.1.isLink_iff heC).mpr hl
        have hwC : w ∈ V(C_j) := hlC.right_mem
        have hlt : r.length < n := by
          rw [← hlen, GraphWalk.length_cons]
          omega
        have hr_Dj := ih r.length hlt r rfl hr_s hwC (hr_le_cons.trans hW_le)
        refine union_subset (iUnion₂_subset fun u hu => ?_) (iUnion₂_subset fun f hf => ?_)
        · rw [vertexSet_walkSubgraph, mem_ofPred_eq, GraphWalk.support_cons,
            List.mem_cons] at hu
          rcases hu with rfl | hur
          · exact (graphDrawingVertexSet_subset_subgraphU_of_mem P_pres.Γ hvC).trans hCj_Dj
          · have hu_W : u ∈ V(walkSubgraph r) := by
              rw [vertexSet_walkSubgraph]; exact hur
            exact (graphDrawingVertexSet_subset_subgraphU_of_mem P_pres.Γ hu_W).trans hr_Dj
        · rw [edgeSet_walkSubgraph, mem_ofPred_eq, GraphWalk.edges_cons,
            List.mem_cons] at hf
          rcases hf with rfl | hfr
          · intro x hx
            exact hCj_Dj (Or.inr (mem_iUnion₂.mpr ⟨f, heC, hx⟩))
          · intro x hx
            have hf_W : f ∈ E(walkSubgraph r) := by
              rw [edgeSet_walkSubgraph]; exact hfr
            exact hr_Dj (Or.inr (mem_iUnion₂.mpr ⟨f, hf_W, hx⟩))
      · by_cases hhit : ∃ x ∈ r.support, x ∈ V(C_j)
        · obtain ⟨v', hv'C, r₁, r₂, hsplit_r, hr₁_first⟩ := exists_first_hit_split r hhit
          have hr₁_s : r₁.IsSimple := (isSimple_of_append (hsplit_r ▸ hr_s)).1
          have hr₂_s : r₂.IsSimple := (isSimple_of_append (hsplit_r ▸ hr_s)).2
          have hv_not_r₁ : v ∉ r₁.support := fun hv_in =>
            hv_not_r (hsplit_r ▸ (GraphWalk.mem_support_append r₁ r₂).mpr (Or.inl hv_in))
          have hcons_r₁_s : (GraphWalk.cons hl r₁).IsSimple :=
            List.nodup_cons.mpr ⟨hv_not_r₁, hr₁_s⟩
          have hvv' : v ≠ v' := fun h => hv_not_r₁ (h ▸ r₁.end_mem_support)
          let P_sub := walkSubgraph (GraphWalk.cons hl r₁)
          have hP_sub_le : P_sub ≤ walkSubgraph (GraphWalk.cons hl r) := by
            rw [(Compatible.of_le_le (walkSubgraph_le _) (walkSubgraph_le _)).le_iff,
              vertexSet_walkSubgraph, vertexSet_walkSubgraph,
              edgeSet_walkSubgraph, edgeSet_walkSubgraph]
            refine ⟨fun x hx => ?_, fun f hf => ?_⟩
            · rcases List.mem_cons.mp hx with rfl | hx₁
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem v
                  (hsplit_r ▸ (GraphWalk.mem_support_append r₁ r₂).mpr (Or.inl hx₁))
            · rcases List.mem_cons.mp hf with rfl | hf₁
              · exact List.mem_cons_self
              · refine List.mem_cons_of_mem e ?_
                rw [hsplit_r, GraphWalk.edges_append, List.mem_append]
                exact Or.inl hf₁
          have hr₁_no_edge : ∀ f ∈ r₁.edges, f ∉ E(C_j) := by
            intro f hf₁ hfC
            obtain ⟨x, z, hxzC⟩ := C_j.exists_isLink_of_mem_edgeSet hfC
            have hxzG : N.G.IsLink f x z := hxzC.mono hC.1
            have hx_s : x ∈ r₁.support := r₁.left_mem_support_of_mem_edges hf₁ hxzG
            have hz_s : z ∈ r₁.support := r₁.left_mem_support_of_mem_edges hf₁ hxzG.symm
            have hxv' : x = v' := hr₁_first x hx_s hxzC.left_mem
            have hzv' : z = v' := hr₁_first z hz_s hxzC.right_mem
            subst hxv' hzv'
            exact not_isLink_self_of_mem_edges_of_isSimple r₁ hr₁_s hf₁ hxzG
          have hVC_sub : V(P_sub) ∩ V(C_j) = {v, v'} := by
            rw [vertexSet_walkSubgraph]
            ext x
            simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.support_cons, List.mem_cons,
              mem_insert_iff, mem_singleton_iff]
            constructor
            · rintro ⟨rfl | hx₁, hxC⟩
              · exact Or.inl rfl
              · exact Or.inr (hr₁_first x hx₁ hxC)
            · rintro (rfl | rfl)
              · exact ⟨Or.inl rfl, hvC⟩
              · exact ⟨Or.inr r₁.end_mem_support, hv'C⟩
          have hEC_sub : Disjoint E(P_sub) E(C_j) := by
            rw [edgeSet_walkSubgraph]
            refine disjoint_left.mpr fun f hf hfC => ?_
            rcases List.mem_cons.mp hf with rfl | hf₁
            · exact heC hfC
            · exact hr₁_no_edge f hf₁ hfC
          have hP_sub_Dj : graphDrawingSubgraphU P_pres.Γ P_sub ⊆ D_j :=
            hdetour_in (hP_sub_le.trans hW_le) (isGraphPathWithEnds_walkSubgraph hcons_r₁_s)
              hvv' hVC_sub hEC_sub
          have hr₂_le : walkSubgraph r₂ ≤ walkSubgraph (GraphWalk.cons hl r) := by
            rw [(Compatible.of_le_le (walkSubgraph_le _) (walkSubgraph_le _)).le_iff,
              vertexSet_walkSubgraph, vertexSet_walkSubgraph,
              edgeSet_walkSubgraph, edgeSet_walkSubgraph]
            refine ⟨fun x hx => List.mem_cons_of_mem v ?_, fun f hf => List.mem_cons_of_mem e ?_⟩
            · rw [hsplit_r, GraphWalk.mem_support_append]
              exact Or.inr hx
            · rw [hsplit_r, GraphWalk.edges_append, List.mem_append]
              exact Or.inr hf
          have hlt₂ : r₂.length < n := by
            rw [← hlen, GraphWalk.length_cons, hsplit_r, GraphWalk.length_append]
            omega
          have hr₂_Dj := ih r₂.length hlt₂ r₂ rfl hr₂_s hv'C (hr₂_le.trans hW_le)
          refine union_subset (iUnion₂_subset fun u hu => ?_) (iUnion₂_subset fun f hf => ?_)
          · rw [vertexSet_walkSubgraph, mem_ofPred_eq, GraphWalk.support_cons, List.mem_cons,
              hsplit_r, GraphWalk.mem_support_append] at hu
            rcases hu with rfl | hu₁ | hu₂
            · have hu_sub : u ∈ V(P_sub) := by
                rw [vertexSet_walkSubgraph]; exact List.mem_cons_self
              exact (graphDrawingVertexSet_subset_subgraphU_of_mem P_pres.Γ hu_sub).trans hP_sub_Dj
            · have hu_sub : u ∈ V(P_sub) := by
                rw [vertexSet_walkSubgraph]; exact List.mem_cons_of_mem v hu₁
              exact (graphDrawingVertexSet_subset_subgraphU_of_mem P_pres.Γ hu_sub).trans hP_sub_Dj
            · have hu_r₂ : u ∈ V(walkSubgraph r₂) := by
                rw [vertexSet_walkSubgraph]; exact hu₂
              exact (graphDrawingVertexSet_subset_subgraphU_of_mem P_pres.Γ hu_r₂).trans hr₂_Dj
          · rw [edgeSet_walkSubgraph, mem_ofPred_eq, GraphWalk.edges_cons, List.mem_cons,
              hsplit_r, GraphWalk.edges_append, List.mem_append] at hf
            rcases hf with rfl | hf₁ | hf₂
            · intro x hx
              have hf_sub : f ∈ E(P_sub) := by
                rw [edgeSet_walkSubgraph]; exact List.mem_cons_self
              exact hP_sub_Dj (Or.inr (mem_iUnion₂.mpr ⟨f, hf_sub, hx⟩))
            · intro x hx
              have hf_sub : f ∈ E(P_sub) := by
                rw [edgeSet_walkSubgraph]; exact List.mem_cons_of_mem e hf₁
              exact hP_sub_Dj (Or.inr (mem_iUnion₂.mpr ⟨f, hf_sub, hx⟩))
            · intro x hx
              have hf_r₂ : f ∈ E(walkSubgraph r₂) := by
                rw [edgeSet_walkSubgraph]; exact hf₂
              exact hr₂_Dj (Or.inr (mem_iUnion₂.mpr ⟨f, hf_r₂, hx⟩))
        · have hhit' : ∀ x ∈ r.support, x ∉ V(C_j) := fun x hx hxC => hhit ⟨x, hx, hxC⟩
          let R := walkSubgraph (GraphWalk.cons hl r)
          have hR_path : IsGraphPathWithEnds N.G R v y := isGraphPathWithEnds_walkSubgraph hW_s
          have hvy : v ≠ y := fun h => hhit' y r.end_mem_support (h ▸ hvC)
          have hVC_R : V(R) ∩ V(C_j) = {v} := by
            rw [vertexSet_walkSubgraph]
            ext x
            simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.support_cons, List.mem_cons,
              mem_singleton_iff]
            constructor
            · rintro ⟨rfl | hxr, hxC⟩
              · rfl
              · exact (hhit' x hxr hxC).elim
            · rintro rfl
              exact ⟨Or.inl rfl, hvC⟩
          have hEC_R : Disjoint E(R) E(C_j) := by
            rw [edgeSet_walkSubgraph]
            refine disjoint_left.mpr fun f hf hfC => ?_
            rcases List.mem_cons.mp hf with rfl | hfr
            · exact heC hfC
            · obtain ⟨x, z, hxzC⟩ := C_j.exists_isLink_of_mem_edgeSet hfC
              have hxzG : N.G.IsLink f x z := hxzC.mono hC.1
              have hx_r : x ∈ r.support := r.left_mem_support_of_mem_edges hfr hxzG
              exact hhit' x hx_r hxzC.left_mem
          have hvG : v ∈ V(N.G) := hl.left_mem
          set pv := (P_pres.Γ.iso.vertexEquiv ⟨v, hvG⟩).1
          set py := (P_pres.Γ.iso.vertexEquiv ⟨y, hyG⟩).1
          obtain ⟨hline_R, hpvy_ne⟩ := isLineWithEnds_graphDrawingSubgraphU P_pres.Γ hR_path hvy
          have hbd_inter : graphDrawingSubgraphU P_pres.Γ R ∩ discBd D_j = {pv} := by
            rw [← Surface.subBd_eq_discBd_euclideanPlane hD, hD_bd,
              graphDrawingSubgraphU_inter_of_disjoint_edgeSet P_pres.Γ hR_path.le hC.1 hEC_R,
              hVC_R, biUnion_singleton, graphDrawingVertexSet_eq_singleton P_pres.Γ hvG]
          have hpre_R : IsPreconnected (graphDrawingSubgraphU P_pres.Γ R \ {pv}) :=
            IsLineWithEnds.isPreconnected_sdiff_left hline_R
          have hdisj_fr : Disjoint (graphDrawingSubgraphU P_pres.Γ R \ {pv}) (frontier D_j) := by
            rw [Surface.plane_disc_frontier hD, disjoint_left]
            rintro x ⟨hxR, hx_npv⟩ hx_bd
            exact hx_npv (hbd_inter ▸ ⟨hxR, hx_bd⟩)
          rcases GraphMinor.GM14.subset_or_disjoint_of_frontier hD.isClosed hpre_R hdisj_fr with
            hin | hout
          · intro x hx
            by_cases hxpv : x = pv
            · subst hxpv
              have hpv_in : pv ∈ graphDrawingSubgraphU P_pres.Γ R ∩ discBd D_j := by
                rw [hbd_inter]; exact mem_singleton pv
              exact Surface.discBd_subset D_j hpv_in.2
            · exact hin ⟨hx, hxpv⟩
          · exfalso
            have hpy_R : py ∈ graphDrawingSubgraphU P_pres.Γ R :=
              graphDrawingVertexSet_subset_subgraphU_of_mem P_pres.Γ hR_path.right_mem ⟨hyG, rfl⟩
            exact disjoint_left.mp hout ⟨hpy_R, hpvy_ne.symm⟩ hpy_Dj

private theorem prop2_inner_subpath {N : Neighborhood α β} (P_pres : Presentation N)
    {C_j P_i' : Graph α β} {D_j : Set EuclideanPlane} {x y v : α}
    (hC : IsGraphCircuit N.G C_j) (hD : IsClosedDisc D_j)
    (hD_bd : subBd D_j = graphDrawingSubgraphU P_pres.Γ C_j)
    (hΔ₀_sub : P_pres.Δ₀ ⊆ D_j)
    (hPi' : IsGraphPathWithEnds N.G P_i' x y) (hy : y ∈ N.Ω₀.bar)
    (hdetour_in : ∀ {u u' : α} {P_sub : Graph α β},
      P_sub ≤ P_i' → IsGraphPathWithEnds N.G P_sub u u' → u ≠ u' →
      V(P_sub) ∩ V(C_j) = {u, u'} → Disjoint E(P_sub) E(C_j) →
      graphDrawingSubgraphU P_pres.Γ P_sub ⊆ D_j)
    (hvC : v ∈ V(C_j)) (hvP : v ∈ V(P_i')) :
    ∃ R : Graph α β, R ≤ P_i' ∧ IsGraphPathWithEnds N.G R v y ∧
      graphDrawingSubgraphU P_pres.Γ R ⊆ D_j := by
  obtain ⟨R, hR_le, _, hR⟩ := hPi'.exists_subpath hvP hPi'.right_mem
  refine ⟨R, hR_le, hR, ?_⟩
  rcases hR with ⟨hRG, W, hW_s, hVR, hER⟩
  obtain ⟨WG, hsG, heG⟩ := exists_walk_up_of_le hRG W
  have hWG_s : WG.IsSimple := by change WG.support.Nodup; rw [hsG]; exact hW_s
  have hR_eq : R = walkSubgraph WG := by
    refine (Compatible.of_le_le hRG (walkSubgraph_le WG)).ext ?_ ?_
    · rw [hVR, vertexSet_walkSubgraph, hsG]
    · rw [hER, edgeSet_walkSubgraph, heG]
  rw [hR_eq]
  exact prop2_inner_walk P_pres hC hD hD_bd hΔ₀_sub hy hdetour_in WG.length WG rfl hWG_s hvC
    (hR_eq ▸ hR_le)

private theorem move3_reroute_with_arc {N : Neighborhood α β} (P_pres : Presentation N)
    {s : ℕ} {X : Set α}
    {C : Fin s → Graph α β} {P : Fin X.ncard → Graph α β}
    {D : Fin s → Set EuclideanPlane}
    (hC_circ : ∀ m, IsGraphCircuit N.G (C m))
    (hC_disj : Pairwise (fun m₁ m₂ => Disjoint V(C m₁) V(C m₂)))
    (hD_disc : ∀ m, IsClosedDisc (D m) ∧ subBd (D m) = graphDrawingSubgraphU P_pres.Γ (C m))
    (hD_bounds : ∀ m, P_pres.Δ₀ ⊆ D m ∧ D m ⊆ P_pres.Δ)
    (hP_path : ∀ k, IsFromToPath N.G (P k) X N.Ω₀.bar)
    (hP_disj : Pairwise (fun k₁ k₂ => Disjoint V(P k₁) V(P k₂)))
    {j : Fin s} {i : Fin X.ncard}
    (hdetour_in : ∀ {k : Fin X.ncard} {u u' : α} {P_sub : Graph α β},
      P_sub ≤ P k → IsGraphPathWithEnds N.G P_sub u u' → u ≠ u' →
      V(P_sub) ∩ V(C j) = {u, u'} → Disjoint E(P_sub) E(C j) →
      graphDrawingSubgraphU P_pres.Γ P_sub ⊆ D j)
    {P_sub Q_k : Graph α β} {v v' w₁ : α} {e₁ : β}
    (hvC : v ∈ V(C j))
    (hP_sub_le : P_sub ≤ P i)
    (hP_sub : IsGraphPathWithEnds N.G P_sub v v')
    (hEC : Disjoint E(P_sub) E(C j))
    (he₁_sub : e₁ ∈ E(P_sub)) (hl₁ : N.G.IsLink e₁ v w₁)
    (hQ_kC : Q_k ≤ C j) (hQ_k : IsGraphPathWithEnds N.G Q_k v v')
    (hno_escape : ∀ R_set : Set EuclideanPlane, IsPreconnected R_set →
      R_set ⊆ D j \ graphDrawingSubgraphU P_pres.Γ P_sub →
      (R_set ∩ graphDrawingSubgraphU P_pres.Γ Q_k).Nonempty →
      Disjoint R_set P_pres.Δ₀) :
    ∃ P' : Fin X.ncard → Graph α β,
      ((∀ k, IsFromToPath N.G (P' k) X N.Ω₀.bar) ∧
        Pairwise (fun k₁ k₂ => Disjoint V(P' k₁) V(P' k₂))) ∧
      totalUnionEdges C P' < totalUnionEdges C P := by
  classical
  have hQ_disj_other : ∀ i' : Fin X.ncard, i' ≠ i → Disjoint V(Q_k) V(P i') := by
    intro i' hi'
    refine disjoint_left.mpr fun u huQ huPi' => ?_
    obtain ⟨x', y', hPi'_ft, _, hy'_eq⟩ := hP_path i'
    have hy' : y' ∈ N.Ω₀.bar := by
      have : y' ∈ V(P i') ∩ N.Ω₀.bar := by rw [hy'_eq]; exact mem_singleton y'
      exact this.2
    obtain ⟨R, hR_le, hR, hR_Dj⟩ :=
      prop2_inner_subpath P_pres (hC_circ j) (hD_disc j).1 (hD_disc j).2 (hD_bounds j).1
        hPi'_ft hy' hdetour_in (hQ_kC.vertexSet_mono huQ) huPi'
    have hdisj_RP : Disjoint V(R) V(P_sub) :=
      disjoint_of_subset hR_le.vertexSet_mono hP_sub_le.vertexSet_mono (hP_disj hi')
    have hdisj_U : Disjoint (graphDrawingSubgraphU P_pres.Γ R)
        (graphDrawingSubgraphU P_pres.Γ P_sub) :=
      disjoint_subgraphU_of_disjoint_vertexSet P_pres.Γ hR.le hP_sub.le hdisj_RP
    have hR_sdiff : graphDrawingSubgraphU P_pres.Γ R ⊆ D j \ graphDrawingSubgraphU P_pres.Γ P_sub :=
      subset_sdiff.mpr ⟨hR_Dj, hdisj_U⟩
    have huG : u ∈ V(N.G) := hR.le.vertexSet_mono hR.left_mem
    let pu := (P_pres.Γ.iso.vertexEquiv ⟨u, huG⟩).1
    have hpu_R : pu ∈ graphDrawingSubgraphU P_pres.Γ R :=
      graphDrawingVertexSet_subset_subgraphU_of_mem P_pres.Γ hR.left_mem ⟨huG, rfl⟩
    have hpu_Q : pu ∈ graphDrawingSubgraphU P_pres.Γ Q_k :=
      graphDrawingVertexSet_subset_subgraphU_of_mem P_pres.Γ huQ ⟨huG, rfl⟩
    have hdisj_Δ₀ := hno_escape (graphDrawingSubgraphU P_pres.Γ R)
      (isPreconnected_graphDrawingSubgraphU P_pres.Γ hR) hR_sdiff ⟨pu, hpu_R, hpu_Q⟩
    obtain ⟨_, hpy'_Δ₀⟩ := isClosedDisc_Δ₀_and_mem_of_mem_bar₀ P_pres hy'
    have hy'G : y' ∈ V(N.G) := N.bar₀_subset hy'
    have hpy'_R : (P_pres.Γ.iso.vertexEquiv ⟨y', hy'G⟩).1 ∈ graphDrawingSubgraphU P_pres.Γ R :=
      graphDrawingVertexSet_subset_subgraphU_of_mem P_pres.Γ hR.right_mem ⟨hy'G, rfl⟩
    exact disjoint_left.mp hdisj_Δ₀ hpy'_R hpy'_Δ₀
  obtain ⟨x_i, y_i, hPi_ft, hx_i_eq, hy_i_eq⟩ := hP_path i
  have hx_i : x_i ∈ X := by
    have : x_i ∈ V(P i) ∩ X := by rw [hx_i_eq]; exact mem_singleton x_i
    exact this.2
  have hy_i : y_i ∈ N.Ω₀.bar := by
    have : y_i ∈ V(P i) ∩ N.Ω₀.bar := by rw [hy_i_eq]; exact mem_singleton y_i
    exact this.2
  have hex_raw : ∃ P_raw : Graph α β,
      IsGraphPathWithEnds N.G P_raw x_i y_i ∧
      V(P_raw) ⊆ V(P i) ∪ V(Q_k) ∧
      E(P_raw) ⊆ (E(P i) \ E(P_sub)) ∪ E(Q_k) := by
    rcases exists_decomp_of_isGraphPathWithEnds_le hPi_ft hP_sub hP_sub_le with
      ⟨P₁, P₂, hP₁P, hP₂P, hP₁, hP₂, _, hE₁, hE₂⟩ |
      ⟨P₁, P₂, hP₁P, hP₂P, hP₁, hP₂, _, hE₁, hE₂⟩
    · exact reroute_path_along_arc ⟨P₁, P₂, hP₁P, hP₂P, hP₁, hP₂, hE₁, hE₂⟩ hQ_k
    · exact reroute_path_along_arc ⟨P₁, P₂, hP₁P, hP₂P, hP₁, hP₂, hE₁, hE₂⟩
        hQ_k.symm
  obtain ⟨P_raw, hP_raw, hP_raw_V, hP_raw_E⟩ := hex_raw
  obtain ⟨x_new, _, y_new, _, P'_i, hP'_i_le, hP'_i_ft⟩ :=
    hP_raw.exists_isFromToPathWithEnds hx_i hy_i
  have hP'_V : V(P'_i) ⊆ V(P i) ∪ V(Q_k) := hP'_i_le.vertexSet_mono.trans hP_raw_V
  have hP'_E : E(P'_i) ⊆ (E(P i) \ E(P_sub)) ∪ E(Q_k) := hP'_i_le.edgeSet_mono.trans hP_raw_E
  have hCG : ∀ m, C m ≤ N.G := fun m => (hC_circ m).1
  have hPG : ∀ k, P k ≤ N.G := fun k => by
    obtain ⟨_, _, hft⟩ := hP_path k
    exact hft.1.le
  have he₁_not_Cj : e₁ ∉ E(C j) := disjoint_left.mp hEC he₁_sub
  have he₁_not_C : ∀ m : Fin s, e₁ ∉ E(C m) :=
    not_mem_edgeSet_of_endpoint_mem_disjoint_family hCG hC_disj hl₁ hvC he₁_not_Cj
  obtain ⟨hP'_disj, hlt⟩ := totalUnionEdges_lt_of_reroute_path N.finite_E hCG hPG hP_disj
    hP_sub_le hQ_kC hP'_V hP'_E hQ_disj_other he₁_sub he₁_not_C
  refine ⟨Function.update P i P'_i, ⟨?_, hP'_disj⟩, hlt⟩
  intro k
  by_cases hki : k = i
  · subst hki
    rw [Function.update_self]
    exact ⟨x_new, y_new, hP'_i_ft⟩
  · rw [Function.update_of_ne hki]
    exact hP_path k

private theorem theorem_10_1_step {N : Neighborhood α β} (P_pres : Presentation N) {s : ℕ}
    {X : Set α} (hX_sub : X ⊆ N.Ω.bar)
    (C : Fin s → Graph α β) (P : Fin X.ncard → Graph α β)
    (hC_nest : N.IsNest P_pres C)
    (hP_valid : (∀ i, IsFromToPath N.G (P i) X N.Ω₀.bar) ∧
      Pairwise (fun i₁ i₂ => Disjoint V(P i₁) V(P i₂)))
    (j : Fin s) (i : Fin X.ncard)
    (hafter : ∀ (j' : Fin s), j < j' → ∀ i' : Fin X.ncard,
      IsGraphPath N.G (subgraphInter N.G (P i') (C j')))
    (hnot_path : ¬ IsGraphPath N.G (subgraphInter N.G (P i) (C j))) :
    ∃ (C' : Fin s → Graph α β) (P' : Fin X.ncard → Graph α β),
      N.IsNest P_pres C' ∧
      ((∀ i, IsFromToPath N.G (P' i) X N.Ω₀.bar) ∧
        Pairwise (fun i₁ i₂ => Disjoint V(P' i₁) V(P' i₂))) ∧
      totalUnionEdges C' P' < totalUnionEdges C P := by
  obtain ⟨hC_circ, hC_disj, D, hD_disc, hD_bounds, hD_mono⟩ := hC_nest
  obtain ⟨hP_path, hP_disj⟩ := hP_valid
  by_cases h_outer : ∃ (i' : Fin X.ncard) (v v' : α) (P_sub : Graph α β)
      (hP_sub : IsGraphPathWithEnds N.G P_sub v v'),
      P_sub ≤ P i' ∧ v ≠ v' ∧ V(P_sub) ∩ V(C j) = {v, v'} ∧ Disjoint E(P_sub) E(C j) ∧
      graphDrawingSubgraphU P_pres.Γ P_sub ∩ D j =
        {(P_pres.Γ.iso.vertexEquiv ⟨v, hP_sub.le.vertexSet_mono hP_sub.left_mem⟩).1,
         (P_pres.Γ.iso.vertexEquiv ⟨v', hP_sub.le.vertexSet_mono hP_sub.right_mem⟩).1}
  · obtain ⟨i', v, v', P_sub, hP_sub, hP_sub_le, hvv', hVC, hEC, houter⟩ := h_outer
    obtain ⟨C', hC'_nest, hlt⟩ :=
      move2_outer_detour P_pres hX_sub hC_circ hC_disj hD_disc hD_bounds hD_mono hP_path hP_disj
        hafter hP_sub_le hP_sub hvv' hVC hEC houter
    exact ⟨C', P, hC'_nest, ⟨hP_path, hP_disj⟩, hlt⟩
  · have hdetour_in : ∀ {k : Fin X.ncard} {u u' : α} {P_sub : Graph α β},
        P_sub ≤ P k → IsGraphPathWithEnds N.G P_sub u u' → u ≠ u' →
        V(P_sub) ∩ V(C j) = {u, u'} → Disjoint E(P_sub) E(C j) →
        graphDrawingSubgraphU P_pres.Γ P_sub ⊆ D j := by
      intro k u u' P_sub hP_sub_le hP_sub huu' hVC hEC
      obtain ⟨_, _, _, h_or⟩ :=
        detour_dichotomy P_pres.Γ (hC_circ j).1 (hD_disc j).1 (hD_disc j).2 hP_sub huu' hVC hEC
      rcases h_or with houter | hinner
      · exact (h_outer ⟨k, u, u', P_sub, hP_sub, hP_sub_le, huu', hVC, hEC, houter⟩).elim
      · exact hinner
    obtain ⟨x_i, y_i, hPi_ft, hx_i_eq, hy_i_eq⟩ := hP_path i
    have hx_i : x_i ∈ X := by
      have : x_i ∈ V(P i) ∩ X := by rw [hx_i_eq]; exact mem_singleton x_i
      exact this.2
    have hy_i : y_i ∈ N.Ω₀.bar := by
      have : y_i ∈ V(P i) ∩ N.Ω₀.bar := by rw [hy_i_eq]; exact mem_singleton y_i
      exact this.2
    obtain ⟨hΔ₀_disc, hpy_i_Δ₀⟩ := isClosedDisc_Δ₀_and_mem_of_mem_bar₀ P_pres hy_i
    have hpy_i_Dj :
        (P_pres.Γ.iso.vertexEquiv ⟨y_i, hPi_ft.le.vertexSet_mono hPi_ft.right_mem⟩).1 ∈ D j :=
      (hD_bounds j).1 hpy_i_Δ₀
    have hne_inter : (V(C j) ∩ V(P i)).Nonempty := by
      rw [inter_comm]
      exact nonempty_inter_of_path_from_bar_to_disc P_pres (hC_circ j).1 (hD_disc j).1
        (hD_bounds j).2 (hD_disc j).2 hPi_ft (hX_sub hx_i) hpy_i_Dj
    rcases isGraphPath_inter_or_exists_detour (hC_circ j).1 hPi_ft hne_inter with
      hpath | ⟨v, ⟨hvC, _⟩, v', ⟨hv'C, _⟩, hvv', P_sub, hP_sub_le, hP_sub, hVC, hEC,
        e₁, he₁_sub, w₁, hl₁⟩
    · exfalso
      rw [subgraphInter_comm (hC_circ j).1 hPi_ft.le] at hpath
      exact hnot_path hpath
    · obtain ⟨hline_P, hst_ne, hbd_inter, _⟩ :=
        detour_dichotomy P_pres.Γ (hC_circ j).1 (hD_disc j).1 (hD_disc j).2 hP_sub hvv' hVC hEC
      have hP_sub_Dj : graphDrawingSubgraphU P_pres.Γ P_sub ⊆ D j :=
        hdetour_in hP_sub_le hP_sub hvv' hVC hEC
      obtain ⟨Q₁, Q₂, hQ₁C, hQ₂C, hQ₁, hQ₂, _, _, _, hline₁, hline₂, hQ_inter_U, hQ_union_U⟩ :=
        circuit_two_arcs_drawing P_pres.Γ (hC_circ j) (hD_disc j).1 (hD_disc j).2 hvC hv'C hvv'
      have hΔ₀_disj_L : Disjoint (discInt P_pres.Δ₀) (graphDrawingSubgraphU P_pres.Γ P_sub) := by
        rw [← Surface.interior_eq_discInt_euclideanPlane hΔ₀_disc, disjoint_left]
        intro x hx_int hxP
        exact ((P_pres.U_subset (graphDrawingSubgraphU_subset_U P_pres.Γ P_sub hxP)).2 hx_int).elim
      rcases inner_chord_separates_from_core (hD_disc j).1 hΔ₀_disc (hD_bounds j).1
          hline₁ hline₂ hline_P hst_ne hQ_inter_U hQ_union_U hP_sub_Dj hbd_inter hΔ₀_disj_L with
        hno₁ | hno₂
      · obtain ⟨P', hP'_valid, hlt⟩ :=
          move3_reroute_with_arc P_pres hC_circ hC_disj hD_disc hD_bounds hP_path hP_disj
            hdetour_in hvC hP_sub_le hP_sub hEC he₁_sub hl₁ hQ₁C hQ₁ hno₁
        exact ⟨C, P', ⟨hC_circ, hC_disj, D, hD_disc, hD_bounds, hD_mono⟩, hP'_valid, hlt⟩
      · obtain ⟨P', hP'_valid, hlt⟩ :=
          move3_reroute_with_arc P_pres hC_circ hC_disj hD_disc hD_bounds hP_path hP_disj
            hdetour_in hvC hP_sub_le hP_sub hEC he₁_sub hl₁ hQ₂C hQ₂ hno₂
        exact ⟨C, P', ⟨hC_circ, hC_disj, D, hD_disc, hD_bounds, hD_mono⟩, hP'_valid, hlt⟩

/-! ## 6. Master Uncrossing Theorem (GM03 (4.1) / GM09 (10.1) / GM14 (9.5)) -/

/-- **Master Uncrossing Theorem (Proof of Graph Minors III, Theorem (4.1), pages 60–61)**:
Given any notion `IsValidNest C` of an `s`-nest of circuits in `G` and `IsValidPaths C P` of `r`
vertex-disjoint paths in `G` such that:
- there exists at least one valid pair `(C₀, P₀)`, and
- whenever `(C, P)` is a valid pair for which `subgraphInter G (P i) (C j)` is not a path in `G` for
  some `i, j`, selecting the smallest index `j` where `subgraphInter G (P i) (C j)` fails to be a
  path for some `i` allows either Move 1 (boundary shortening), Move 2 (outer detour replacement of
  `C_j`), or Move 3 (inner detour rerouting of `P_i` using Property `(2)`), producing a valid pair
  `(C', P')` with strictly fewer edges in the union `totalUnionEdges C' P' < totalUnionEdges C P`,
there exists a valid pair `(C, P)` such that `subgraphInter G (P i) (C j)` is a path in `G` for all
`i : Fin r` and `j : Fin s`. -/
theorem nest_uncrossing {s r : ℕ} (G : Graph α β)
    (IsValidNest : (Fin s → Graph α β) → Prop)
    (IsValidPaths : (Fin s → Graph α β) → (Fin r → Graph α β) → Prop)
    (hex : ∃ C₀ P₀, IsValidNest C₀ ∧ IsValidPaths C₀ P₀)
    (hstep : ∀ C P, IsValidNest C → IsValidPaths C P →
      (∀ (j : Fin s) (i : Fin r),
        (∀ (j' : Fin s), j' < j → ∀ i' : Fin r, IsGraphPath G (subgraphInter G (P i') (C j'))) →
        ¬ IsGraphPath G (subgraphInter G (P i) (C j)) →
        ∃ C' P', IsValidNest C' ∧ IsValidPaths C' P' ∧
          totalUnionEdges C' P' < totalUnionEdges C P)) :
    ∃ C P, IsValidNest C ∧ IsValidPaths C P ∧
      ∀ (i : Fin r) (j : Fin s), IsGraphPath G (subgraphInter G (P i) (C j)) := by
  classical
  obtain ⟨C, P, ⟨hC, hP⟩, hmin⟩ :=
    exists_min_totalUnionEdges (fun C P => IsValidNest C ∧ IsValidPaths C P) hex
  refine ⟨C, P, hC, hP, ?_⟩
  by_contra hnot_all
  push Not at hnot_all
  have hex_j : ∃ n : ℕ, ∃ (hn : n < s) (i : Fin r),
      ¬ IsGraphPath G (subgraphInter G (P i) (C ⟨n, hn⟩)) := by
    obtain ⟨i, j, hij⟩ := hnot_all
    exact ⟨j.1, j.2, i, hij⟩
  let n₀ := Nat.find hex_j
  obtain ⟨hn₀, i₀, hi₀⟩ := Nat.find_spec hex_j
  let j₀ : Fin s := ⟨n₀, hn₀⟩
  have hprev : ∀ (j' : Fin s), j' < j₀ → ∀ i' : Fin r,
      IsGraphPath G (subgraphInter G (P i') (C j')) := by
    intro j' hj' i'
    by_contra hnot'
    exact Nat.find_min hex_j hj' ⟨j'.2, i', hnot'⟩
  obtain ⟨C', P', hC', hP', hlt⟩ := hstep C P hC hP j₀ i₀ hprev hi₀
  exact Nat.lt_irrefl _ (lt_of_lt_of_le hlt (hmin C' P' ⟨hC', hP'⟩))

/-- Dual-index version of `nest_uncrossing` selecting the **largest** circuit index `j : Fin s`
where `subgraphInter G (P i) (C j)` fails to be a path (used when `C (s - 1)` is the outermost
circuit and `C 0` is the innermost circuit, as in `Neighborhood.IsNest`). -/
theorem nest_uncrossing_of_gt {s r : ℕ} (G : Graph α β)
    (IsValidNest : (Fin s → Graph α β) → Prop)
    (IsValidPaths : (Fin s → Graph α β) → (Fin r → Graph α β) → Prop)
    (hex : ∃ C₀ P₀, IsValidNest C₀ ∧ IsValidPaths C₀ P₀)
    (hstep : ∀ C P, IsValidNest C → IsValidPaths C P →
      (∀ (j : Fin s) (i : Fin r),
        (∀ (j' : Fin s), j < j' → ∀ i' : Fin r, IsGraphPath G (subgraphInter G (P i') (C j'))) →
        ¬ IsGraphPath G (subgraphInter G (P i) (C j)) →
        ∃ C' P', IsValidNest C' ∧ IsValidPaths C' P' ∧
          totalUnionEdges C' P' < totalUnionEdges C P)) :
    ∃ C P, IsValidNest C ∧ IsValidPaths C P ∧
      ∀ (i : Fin r) (j : Fin s), IsGraphPath G (subgraphInter G (P i) (C j)) := by
  classical
  obtain ⟨C, P, ⟨hC, hP⟩, hmin⟩ :=
    exists_min_totalUnionEdges (fun C P => IsValidNest C ∧ IsValidPaths C P) hex
  refine ⟨C, P, hC, hP, ?_⟩
  by_contra hnot_all
  push Not at hnot_all
  have hex_k : ∃ k : ℕ, ∃ (hk : k < s) (i : Fin r),
      ¬ IsGraphPath G (subgraphInter G (P i) (C ⟨s - 1 - k, by omega⟩)) := by
    obtain ⟨i, j, hij⟩ := hnot_all
    refine ⟨s - 1 - j.1, by omega, i, ?_⟩
    have hj_eq : (⟨s - 1 - (s - 1 - j.1), by omega⟩ : Fin s) = j :=
      Fin.ext (by dsimp; omega)
    rwa [hj_eq]
  let k₀ := Nat.find hex_k
  obtain ⟨hk₀, i₀, hi₀⟩ := Nat.find_spec hex_k
  let j₀ : Fin s := ⟨s - 1 - k₀, by omega⟩
  have hafter : ∀ (j' : Fin s), j₀ < j' → ∀ i' : Fin r,
      IsGraphPath G (subgraphInter G (P i') (C j')) := by
    intro j' hj' i'
    by_contra hnot'
    have hj'_lt : s - 1 - j'.1 < k₀ := by
      change s - 1 - k₀ < j'.1 at hj'
      omega
    have hj'_eq : (⟨s - 1 - (s - 1 - j'.1), by omega⟩ : Fin s) = j' :=
      Fin.ext (by dsimp; omega)
    exact Nat.find_min hex_k hj'_lt ⟨by omega, i', hj'_eq.symm ▸ hnot'⟩
  obtain ⟨C', P', hC', hP', hlt⟩ := hstep C P hC hP j₀ i₀ hafter hi₀
  exact Nat.lt_irrefl _ (lt_of_lt_of_le hlt (hmin C' P' ⟨hC', hP'⟩))

/-- **Graph Minors IX, (10.1)** (page 64):
"Let $(G, \Omega, \Omega_0)$ be a rural neighborhood and let $(\Sigma, \Gamma, \Delta, \Delta_0)$ be
a presentation with an $s$-nest. Let $X \subseteq \bar{\Omega}$ be weakly-linked, with $|X| = r$.
Then we may choose an $s$-nest $(C_1, \dots, C_s)$ and disjoint paths $P_1, \dots, P_r$ of $G$ each
with one end in $X$ and the other in $\bar{\Omega}_0$, such that for $1 \le i \le r$ and
$1 \le j \le s$, $P_i \cap C_j$ is a path." -/
theorem theorem_10_1_proof {N : Neighborhood α β} (P_pres : Presentation N) {s : ℕ}
    (h_nest : ∃ C₀ : Fin s → Graph α β, N.IsNest P_pres C₀)
    {X : Set α} (hX : N.IsWeaklyLinked X) :
    ∃ (C : Fin s → Graph α β) (P : Fin X.ncard → Graph α β),
      N.IsNest P_pres C ∧
      (∀ i, IsFromToPath N.G (P i) X N.Ω₀.bar) ∧
      Pairwise (fun i₁ i₂ => Disjoint V(P i₁) V(P i₂)) ∧
      ∀ (i : Fin X.ncard) (j : Fin s), IsGraphPath N.G (subgraphInter N.G (P i) (C j)) := by
  obtain ⟨C₀, hC₀⟩ := h_nest
  obtain ⟨hX_sub, P₀, hP₀_path, hP₀_disj⟩ := hX
  obtain ⟨C, P, hC, ⟨hP_path, hP_disj⟩, hinter⟩ :=
    nest_uncrossing_of_gt N.G (N.IsNest P_pres)
      (fun _ P => (∀ i, IsFromToPath N.G (P i) X N.Ω₀.bar) ∧
        Pairwise (fun i₁ i₂ => Disjoint V(P i₁) V(P i₂)))
      ⟨C₀, P₀, hC₀, hP₀_path, hP₀_disj⟩
      (theorem_10_1_step P_pres hX_sub)
  exact ⟨C, P, hC, hP_path, hP_disj, hinter⟩

export Neighborhood (IsNest HasBreadthGe IsWeaklyLinked IsLinked)

end GraphMinor.GM09
