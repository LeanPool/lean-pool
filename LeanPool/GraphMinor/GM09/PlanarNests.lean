/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.GM09.Basic
public import LeanPool.GraphMinor.GM12.Section2DiscChordSplit
public import LeanPool.GraphMinor.GM14.Section6a

/-!
# Planar Nests and Disjoint Paths Uncrossing (Graph Minors III, Theorem (4.1))

This file formalizes the nest-and-paths uncrossing argument from the proof of
**Graph Minors III, Theorem (4.1)** (pages 59–61), which is used both in
**Graph Minors IX, (10.1)** (page 64) and in **Graph Minors XIV, (9.5), Claim (3)** (page 46:
*"By [1, theorem (4.1)], or rather by the proof of that theorem, we deduce from (1) and (2) that
(3) There are circuits $C_1, \dots, C_{\beta+1}$ as in (1), and paths $P_1, \dots, P_\beta$ as in
(2), such that $C_i \cap P_j$ is a path for $1 \le i \le \beta + 1$ and $1 \le j \le \beta$."*).

We work over drawings `H : Drawing S` in a closed surface `S` inside a closed disc `Δ_out`, proving:
1. Subdrawing intersection `Drawing.inf H A B` and its point-set identity
   `(Drawing.inf H A B).U = A.U ∩ B.U`.
2. Detour decomposition (`path_inf_isPath_or_exists_detour`): for a path `P` in `H` meeting a
   circuit `C` of `H`, either `Drawing.inf H C P` is a path of `H`, or the walk of `P` splits as
   `W₁.append (W_sub.append W₂)` where `P_sub = walkDrawing H W_sub` is a detour path between
   distinct vertices `v, v' ∈ C.V ∩ P.V` with `P_sub.V ∩ C.V = {v, v'}` and
   `Disjoint P_sub.E C.E`.
3. Suffix inside-disc dichotomy (`walk_subset_disc_or_exists_outer_detour`): if no outer detour
   on `C_j` occurs along `P_i`, then for every `v ∈ (C_j).V ∩ (P_i).V`, the suffix of `P_i` from
   `v` to its inner endpoint lies inside `Δ_j`.
4. Outer detour circuit replacement (Move 2, using `isSlope_discIns` and `no_circuit_in_path`) and
   inner detour path rerouting (Move 3, using `disc_split_with_boundary_arcs`).
5. Complete closed-disc nest-and-paths uncrossing theorem (`planar_nest_uncrossing`).
-/

@[expose] public section

namespace GraphMinor.GM09.PlanarNests

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM12
open GraphMinor.GM14

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-! ## 1. Intersection of Subdrawings `Drawing.inf` -/

/-- The intersection `Drawing.inf H A B` of two subdrawings `A, B` of `H`. -/
noncomputable def Drawing.inf (H A B : Drawing S) : Drawing S :=
  H.span (A.V ∩ B.V) (A.E ∩ B.E)

theorem Drawing.inf_isSubdrawing (H A B : Drawing S) : (Drawing.inf H A B).IsSubdrawing H :=
  H.span_isSubdrawing _ _

theorem Drawing.inf_V {H A B : Drawing S} (hA : A.IsSubdrawing H) (hB : B.IsSubdrawing H) :
    (Drawing.inf H A B).V = A.V ∩ B.V := by
  apply subset_antisymm
  · rintro x (⟨hx, _⟩ | hx)
    · exact hx
    · obtain ⟨e, ⟨⟨heA, heB⟩, _⟩, hxe, hxV⟩ := mem_iUnion₂.mp hx
      have hxA : x ∈ closure e ∩ A.V := by rw [hA.closure_inter_V heA]; exact ⟨hxe, hxV⟩
      have hxB : x ∈ closure e ∩ B.V := by rw [hB.closure_inter_V heB]; exact ⟨hxe, hxV⟩
      exact ⟨hxA.2, hxB.2⟩
  · intro x hx
    exact Or.inl ⟨hx, hA.1 hx.1⟩

theorem Drawing.inf_E {H A B : Drawing S} (hA : A.IsSubdrawing H) :
    (Drawing.inf H A B).E = A.E ∩ B.E := by
  rw [Drawing.inf, H.span_E]
  exact inter_eq_left.mpr (inter_subset_left.trans hA.2)

theorem Drawing.inf_isSubdrawing_left {H A B : Drawing S} (hA : A.IsSubdrawing H)
    (hB : B.IsSubdrawing H) : (Drawing.inf H A B).IsSubdrawing A :=
  ⟨by rw [Drawing.inf_V hA hB]; exact inter_subset_left,
   by rw [Drawing.inf_E hA]; exact inter_subset_left⟩

theorem Drawing.inf_isSubdrawing_right {H A B : Drawing S} (hA : A.IsSubdrawing H)
    (hB : B.IsSubdrawing H) : (Drawing.inf H A B).IsSubdrawing B :=
  ⟨by rw [Drawing.inf_V hA hB]; exact inter_subset_right,
   by rw [Drawing.inf_E hA]; exact inter_subset_right⟩

theorem Drawing.inf_U {H A B : Drawing S} (hA : A.IsSubdrawing H) (hB : B.IsSubdrawing H) :
    (Drawing.inf H A B).U = A.U ∩ B.U := by
  apply subset_antisymm
  · exact subset_inter (Drawing.inf_isSubdrawing_left hA hB).U_subset
      (Drawing.inf_isSubdrawing_right hA hB).U_subset
  · rintro x ⟨hxA, hxB⟩
    rw [Drawing.U_eq, Drawing.inf_V hA hB, Drawing.inf_E hA]
    by_cases hxV : x ∈ H.V
    · have hxAV : x ∈ A.V := by
        by_contra hxAV
        obtain ⟨e, heA, hxe⟩ := A.exists_edge_of_mem hxA hxAV
        exact ((hA.2 heA).2.1 hxe).2 hxV
      have hxBV : x ∈ B.V := by
        by_contra hxBV
        obtain ⟨e, heB, hxe⟩ := B.exists_edge_of_mem hxB hxBV
        exact ((hB.2 heB).2.1 hxe).2 hxV
      exact Or.inl ⟨hxAV, hxBV⟩
    · obtain ⟨e₁, he₁, hxe₁⟩ := A.exists_edge_of_mem hxA (fun h => hxV (hA.1 h))
      obtain ⟨e₂, he₂, hxe₂⟩ := B.exists_edge_of_mem hxB (fun h => hxV (hB.1 h))
      have heq : e₁ = e₂ := H.edge_eq_of_mem (hA.2 he₁) (hB.2 he₂) hxe₁ hxe₂
      exact Or.inr (mem_iUnion₂.mpr ⟨e₁, ⟨he₁, heq ▸ he₂⟩, subset_closure hxe₁⟩)

theorem Drawing.inf_comm {H A B : Drawing S} (hA : A.IsSubdrawing H) (hB : B.IsSubdrawing H) :
    Drawing.inf H A B = Drawing.inf H B A := by
  apply Drawing.ext_of_V_E
  · rw [Drawing.inf_V hA hB, Drawing.inf_V hB hA, inter_comm]
  · rw [Drawing.inf_E hA, Drawing.inf_E hB, inter_comm]

theorem Drawing.sup_U {H A B : Drawing S} (hA : A.IsSubdrawing H) (hB : B.IsSubdrawing H) :
    (H.sup A B).U = A.U ∪ B.U := by
  rw [Drawing.U_eq, H.sup_V hA hB, H.sup_E hA hB, A.U_eq, B.U_eq, biUnion_union,
    union_union_union_comm]

/-- A subdrawing `D` is a path if `D.IsPathBetween u v` for some `u, v`. -/
def IsDrawingPath (D : Drawing S) : Prop :=
  ∃ u v : S, D.IsPathBetween u v

omit [T2Space S] in
theorem Drawing.IsPathBetween.symm {D : Drawing S} {u v : S} (h : D.IsPathBetween u v) :
    D.IsPathBetween v u := by
  obtain ⟨W, hW, hV, hE⟩ := h
  refine ⟨W.reverse, hW.reverse, ?_, ?_⟩
  · rw [hV]; ext x; simp [GraphWalk.support_reverse]
  · rw [hE]; ext e; simp [GraphWalk.edges_reverse]

theorem Drawing.IsPathBetween.isPreconnected_U {D : Drawing S} {u v : S}
    (h : D.IsPathBetween u v) : IsPreconnected D.U := by
  by_cases huv : u = v
  · subst huv
    obtain ⟨W, hW, hV, hE⟩ := h
    have hlen : W.length = 0 := hW.length_eq_zero
    have hedges : W.edges = [] := List.length_eq_zero_iff.mp hlen
    have hsupp : W.support = [u] := by
      cases W with
      | nil _ => rfl
      | cons _ _ => simp at hedges
    have hDU : D.U = {u} := by
      rw [D.U_eq, hV, hE, hsupp, hedges]
      simp
    rw [hDU]
    exact isPreconnected_singleton
  · obtain ⟨f, _, _⟩ := GM14.isLine_of_isPathBetween h huv
    have hEq : D.U = (fun t : unitInterval => (f t).1) '' univ := by
      ext x
      exact ⟨fun hx => ⟨f.symm ⟨x, hx⟩, trivial, by simp⟩, fun ⟨t, _, ht⟩ => ht ▸ (f t).2⟩
    rw [hEq]
    exact isPreconnected_univ.image _ (continuous_subtype_val.comp f.continuous).continuousOn

theorem IsDrawingPath.isPreconnected_U {D : Drawing S} (h : IsDrawingPath D) :
    IsPreconnected D.U := by
  obtain ⟨u, v, huv⟩ := h
  exact Drawing.IsPathBetween.isPreconnected_U huv

/-! ## 2. Walk Splitting, Detour Decomposition, and Suffix Dichotomy -/

/-- Every walk `W` meeting a vertex set `X` splits at the first vertex `v ∈ X` into a prefix `W₁`
(meeting `X` only at its last vertex `v`) and a suffix `W₂` starting at `v`. -/
theorem exists_first_hit_split {α β : Type*} {G : Graph α β} {a b : α} (W : GraphWalk G a b)
    {X : Set α} (hne : ∃ x ∈ W.support, x ∈ X) :
    ∃ v ∈ X, ∃ (W₁ : GraphWalk G a v) (W₂ : GraphWalk G v b),
      W = W₁.append W₂ ∧ ∀ x ∈ W₁.support, x ∈ X → x = v := by
  induction W with
  | @nil a h =>
    obtain ⟨x, hx, hxX⟩ := hne
    have hxa : x = a := List.mem_singleton.mp hx
    exact ⟨a, hxa ▸ hxX, .nil h, .nil h, rfl, fun y hy _ => List.mem_singleton.mp hy⟩
  | @cons a w b e hl r ih =>
    by_cases haX : a ∈ X
    · exact ⟨a, haX, .nil hl.left_mem, .cons hl r, rfl, fun y hy _ => List.mem_singleton.mp hy⟩
    · have hne_r : ∃ x ∈ r.support, x ∈ X := by
        obtain ⟨x, hx, hxX⟩ := hne
        rcases List.mem_cons.mp hx with rfl | hxr
        · exact (haX hxX).elim
        · exact ⟨x, hxr, hxX⟩
      obtain ⟨v, hvX, W₁, W₂, rfl, hfirst⟩ := ih hne_r
      refine ⟨v, hvX, .cons hl W₁, W₂, rfl, fun x hx hxX => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx₁
      · exact (haX hxX).elim
      · exact hfirst x hx₁ hxX

/-- In a simple walk `W`, no edge in `W.edges` can be a loop `G.IsLink f z z`. -/
theorem not_isLink_self_of_mem_edges_of_isSimple {α β : Type*} {G : Graph α β} {a b z : α}
    {f : β} (W : GraphWalk G a b) (hW : W.IsSimple) (hf : f ∈ W.edges) (hl : G.IsLink f z z) :
    False := by
  induction W with
  | nil _ => simp at hf
  | @cons u v _ e₀ hl₀ r₀ ih =>
    rcases List.mem_cons.mp hf with rfl | hfr₀
    · have huz : u = z := by rcases hl₀.left_eq_or_eq hl with h | h <;> exact h
      have hvz : v = z := by rcases hl₀.symm.left_eq_or_eq hl with h | h <;> exact h
      have huv : u = v := huz.trans hvz.symm
      exact (List.nodup_cons.mp hW).1 (huv ▸ r₀.start_mem_support)
    · exact ih (List.nodup_cons.mp hW).2 hfr₀

/-- If a simple walk `W` in `H` starts at `v₀ ∈ C.V`, then either `Drawing.inf H C (walkDrawing H
W)`
is a path from `v₀` to some `u ∈ C.V`, or `W` decomposes as `W_pre.append (W_sub.append W_post)`
where `P_sub = walkDrawing H W_sub` is a detour path between distinct `v, v' ∈ C.V` with
`P_sub.V ∩ C.V = {v, v'}`, `Disjoint P_sub.E C.E`, and its first edge incident with `v`. -/
theorem walk_inf_isPath_or_exists_detour {H C : Drawing S} (hC : C.IsSubdrawing H)
    {v₀ b : S} (W : GraphWalk H.toGraph v₀ b) (hWs : W.IsSimple) (hv₀ : v₀ ∈ C.V) :
    (∃ u ∈ C.V, (Drawing.inf H C (walkDrawing H W)).IsPathBetween v₀ u) ∨
      ∃ v ∈ C.V, ∃ v' ∈ C.V, v ≠ v' ∧
        ∃ (W_pre : GraphWalk H.toGraph v₀ v) (W_sub : GraphWalk H.toGraph v v')
          (W_post : GraphWalk H.toGraph v' b),
          W = W_pre.append (W_sub.append W_post) ∧
          (walkDrawing H W_sub).V ∩ C.V = {v, v'} ∧
          Disjoint (walkDrawing H W_sub).E C.E ∧
          ∃ e ∈ (walkDrawing H W_sub).E, ∃ w : S, H.toGraph.IsLink e v w := by
  induction W with
  | @nil a haH =>
    left
    refine ⟨a, hv₀, ?_⟩
    have heq : Drawing.inf H C (walkDrawing H (GraphWalk.nil haH)) =
        walkDrawing H (GraphWalk.nil haH) := by
      apply Drawing.ext_of_V_E
      · rw [Drawing.inf_V hC (walkDrawing_isSubdrawing H _), walkDrawing_V]
        ext x
        simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.support_nil, List.mem_singleton]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hv₀, h⟩⟩
      · rw [Drawing.inf_E hC, walkDrawing_E]
        simp
    rw [heq]
    exact walkDrawing_isPathBetween H (List.nodup_singleton a)
  | @cons a w b e hl r ih =>
    have ha_not_r : a ∉ r.support := (List.nodup_cons.mp hWs).1
    have hr_s : r.IsSimple := (List.nodup_cons.mp hWs).2
    by_cases heC : e ∈ C.E
    · have hlC : C.toGraph.IsLink e a w := (hC.isLink_iff heC).mpr hl
      have hwC : w ∈ C.V := hlC.2.2.1
      rcases ih hr_s hwC with ⟨u, huC, hpath_r⟩ |
        ⟨v, hvC, v', hv'C, hvv', W_pre, W_sub, W_post, hr_eq, hVC, hEC, hex_e⟩
      · left
        refine ⟨u, huC, ?_⟩
        obtain ⟨W_r, hW_r_s, hV_r, hE_r⟩ := hpath_r
        have hsub_r := Drawing.inf_isSubdrawing H C (walkDrawing H r)
        obtain ⟨W_r_H, hs_r, he_r⟩ := hsub_r.exists_walk_up W_r
        have ha_not_Wr : a ∉ W_r_H.support := by
          intro ha_in
          rw [hs_r] at ha_in
          have ha_mem : a ∈ (Drawing.inf H C (walkDrawing H r)).V := by rw [hV_r]; exact ha_in
          rw [Drawing.inf_V hC (walkDrawing_isSubdrawing H r), walkDrawing_V] at ha_mem
          exact ha_not_r ha_mem.2
        have hW_r_H_s : W_r_H.IsSimple := by
          change W_r_H.support.Nodup
          rw [hs_r]
          exact hW_r_s
        have hW_cons_s : (GraphWalk.cons hl W_r_H).IsSimple :=
          List.nodup_cons.mpr ⟨ha_not_Wr, hW_r_H_s⟩
        have heq : Drawing.inf H C (walkDrawing H (GraphWalk.cons hl r)) =
            walkDrawing H (GraphWalk.cons hl W_r_H) := by
          apply Drawing.ext_of_V_E
          · rw [Drawing.inf_V hC (walkDrawing_isSubdrawing H _), walkDrawing_V, walkDrawing_V]
            ext x
            simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.support_cons, List.mem_cons]
            constructor
            · rintro ⟨hxC, rfl | hxr⟩
              · exact Or.inl rfl
              · right
                rw [hs_r]
                have hx_in : x ∈ (Drawing.inf H C (walkDrawing H r)).V := by
                  rw [Drawing.inf_V hC (walkDrawing_isSubdrawing H r), walkDrawing_V]
                  exact ⟨hxC, hxr⟩
                rwa [hV_r] at hx_in
            · rintro (rfl | hxWr)
              · exact ⟨hv₀, Or.inl rfl⟩
              · rw [hs_r] at hxWr
                have hx_in : x ∈ (Drawing.inf H C (walkDrawing H r)).V := by rw [hV_r]; exact hxWr
                rw [Drawing.inf_V hC (walkDrawing_isSubdrawing H r), walkDrawing_V] at hx_in
                exact ⟨hx_in.1, Or.inr hx_in.2⟩
          · rw [Drawing.inf_E hC, walkDrawing_E, walkDrawing_E]
            ext f
            simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.edges_cons, List.mem_cons]
            constructor
            · rintro ⟨hfC, rfl | hfr⟩
              · exact Or.inl rfl
              · right
                rw [he_r]
                have hf_in : f ∈ (Drawing.inf H C (walkDrawing H r)).E := by
                  rw [Drawing.inf_E hC, walkDrawing_E]
                  exact ⟨hfC, hfr⟩
                rwa [hE_r] at hf_in
            · rintro (rfl | hfWr)
              · exact ⟨heC, Or.inl rfl⟩
              · rw [he_r] at hfWr
                have hf_in : f ∈ (Drawing.inf H C (walkDrawing H r)).E := by rw [hE_r]; exact hfWr
                rw [Drawing.inf_E hC, walkDrawing_E] at hf_in
                exact ⟨hf_in.1, Or.inr hf_in.2⟩
        rw [heq]
        exact walkDrawing_isPathBetween H hW_cons_s
      · right
        refine ⟨v, hvC, v', hv'C, hvv', .cons hl W_pre, W_sub, W_post, ?_, hVC, hEC, hex_e⟩
        rw [hr_eq]; rfl
    · by_cases hhit : ∃ x ∈ r.support, x ∈ C.V
      · right
        obtain ⟨v', hv'C, r₁, r₂, hsplit_r, hr₁_first⟩ := exists_first_hit_split r hhit
        have hr₁_s : r₁.IsSimple := (isSimple_of_append (hsplit_r ▸ hr_s)).1
        have ha_not_r₁ : a ∉ r₁.support := fun ha_in =>
          ha_not_r (hsplit_r ▸ (GraphWalk.mem_support_append r₁ r₂).mpr (Or.inl ha_in))
        have hav' : a ≠ v' := fun h => ha_not_r₁ (h ▸ r₁.end_mem_support)
        let W_sub := GraphWalk.cons hl r₁
        have hr₁_no_edge : ∀ f ∈ r₁.edges, f ∉ C.E := by
          intro f hf₁ hfC
          obtain ⟨x, y, hxyH⟩ := (H.toGraph.edge_mem_iff_exists_isLink f).mp (hC.2 hfC)
          have hxyC : C.toGraph.IsLink f x y := (hC.isLink_iff hfC).mpr hxyH
          have hx_s : x ∈ r₁.support := r₁.left_mem_support_of_mem_edges hf₁ hxyH
          have hy_s : y ∈ r₁.support := r₁.left_mem_support_of_mem_edges hf₁ hxyH.symm
          have hxv' : x = v' := hr₁_first x hx_s hxyC.2.1
          have hyv' : y = v' := hr₁_first y hy_s hxyC.2.2.1
          subst hxv' hyv'
          exact not_isLink_self_of_mem_edges_of_isSimple r₁ hr₁_s hf₁ hxyH
        refine ⟨a, hv₀, v', hv'C, hav', .nil hl.left_mem, W_sub, r₂, ?_, ?_, ?_,
          ⟨e, by rw [walkDrawing_E]; exact List.mem_cons_self, w, hl⟩⟩
        · rw [hsplit_r]; rfl
        · rw [walkDrawing_V]
          ext x
          simp only [W_sub, mem_inter_iff, mem_ofPred_eq, GraphWalk.support_cons, List.mem_cons,
            mem_insert_iff, mem_singleton_iff]
          constructor
          · rintro ⟨rfl | hx₁, hxC⟩
            · exact Or.inl rfl
            · exact Or.inr (hr₁_first x hx₁ hxC)
          · rintro (rfl | rfl)
            · exact ⟨Or.inl rfl, hv₀⟩
            · exact ⟨Or.inr r₁.end_mem_support, hv'C⟩
        · rw [walkDrawing_E]
          refine disjoint_left.mpr fun f hf hfC => ?_
          rcases List.mem_cons.mp hf with rfl | hf₁
          · exact heC hfC
          · exact hr₁_no_edge f hf₁ hfC
      · left
        have hhit' : ∀ x ∈ r.support, x ∉ C.V := fun x hx hxC => hhit ⟨x, hx, hxC⟩
        refine ⟨a, hv₀, ?_⟩
        have haH : a ∈ V(H.toGraph) := hl.left_mem
        have heq : Drawing.inf H C (walkDrawing H (GraphWalk.cons hl r)) =
            walkDrawing H (GraphWalk.nil haH) := by
          apply Drawing.ext_of_V_E
          · rw [Drawing.inf_V hC (walkDrawing_isSubdrawing H _), walkDrawing_V, walkDrawing_V]
            ext x
            simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.support_cons, List.mem_cons,
              GraphWalk.support_nil, List.not_mem_nil, or_false]
            constructor
            · rintro ⟨hxC, rfl | hxr⟩
              · rfl
              · exact (hhit' x hxr hxC).elim
            · rintro rfl
              exact ⟨hv₀, Or.inl rfl⟩
          · rw [Drawing.inf_E hC, walkDrawing_E, walkDrawing_E]
            ext f
            simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.edges_cons, List.mem_cons,
              GraphWalk.edges_nil, List.not_mem_nil, iff_false, not_and]
            rintro hfC (rfl | hfr)
            · exact heC hfC
            · obtain ⟨x, y, hxyH⟩ := (H.toGraph.edge_mem_iff_exists_isLink f).mp (hC.2 hfC)
              have hxyC : C.toGraph.IsLink f x y := (hC.isLink_iff hfC).mpr hxyH
              have hx_r : x ∈ r.support := r.left_mem_support_of_mem_edges hfr hxyH
              exact hhit' x hx_r hxyC.2.1
        rw [heq]
        exact walkDrawing_isPathBetween H (List.nodup_singleton a)

/-- For any path `P` in `H` between `a` and `b` meeting `C.V`, either `Drawing.inf H C P` is a path,
or the simple walk `W` of `P` in `H` decomposes as `W₁.append (W_sub.append W₂)` where
`P_sub = walkDrawing H W_sub` is a detour path between distinct `v, v' ∈ C.V ∩ P.V`. -/
theorem path_inf_isPath_or_exists_detour {H C P : Drawing S} (hC : C.IsSubdrawing H)
    (hP_sub : P.IsSubdrawing H) {a b : S} (hP : P.IsPathBetween a b) (hne : (C.V ∩ P.V).Nonempty) :
    IsDrawingPath (Drawing.inf H C P) ∨
      ∃ v ∈ C.V ∩ P.V, ∃ v' ∈ C.V ∩ P.V, v ≠ v' ∧
        ∃ (W₁ : GraphWalk H.toGraph a v) (W_sub : GraphWalk H.toGraph v v')
          (W₂ : GraphWalk H.toGraph v' b),
          (W₁.append (W_sub.append W₂)).IsSimple ∧
          P = walkDrawing H (W₁.append (W_sub.append W₂)) ∧
          (walkDrawing H W_sub).V ∩ C.V = {v, v'} ∧
          Disjoint (walkDrawing H W_sub).E C.E ∧
          ∃ e ∈ (walkDrawing H W_sub).E, ∃ w : S, H.toGraph.IsLink e v w := by
  obtain ⟨W₀, hW₀s, hVP, hEP⟩ := hP
  obtain ⟨W, hsW, heW⟩ := hP_sub.exists_walk_up W₀
  have hWs : W.IsSimple := by change W.support.Nodup; rw [hsW]; exact hW₀s
  have hP_eq : P = walkDrawing H W := by
    apply Drawing.ext_of_V_E
    · rw [hVP, walkDrawing_V, hsW]
    · rw [hEP, walkDrawing_E, heW]
  have hne_W : ∃ x ∈ W.support, x ∈ C.V := by
    obtain ⟨x, hxC, hxP⟩ := hne
    rw [hVP, ← hsW] at hxP
    exact ⟨x, hxP, hxC⟩
  obtain ⟨v₀, hv₀C, W_init, W_rem, hsplit, hW_init_first⟩ := exists_first_hit_split W hne_W
  have hsp_init_rem := isSimple_of_append (hsplit ▸ hWs)
  have hW_init_no_edge : ∀ f ∈ W_init.edges, f ∉ C.E := by
    intro f hf hfC
    obtain ⟨x, y, hxyH⟩ := (H.toGraph.edge_mem_iff_exists_isLink f).mp (hC.2 hfC)
    have hxyC : C.toGraph.IsLink f x y := (hC.isLink_iff hfC).mpr hxyH
    have hx_s : x ∈ W_init.support := W_init.left_mem_support_of_mem_edges hf hxyH
    have hy_s : y ∈ W_init.support := W_init.left_mem_support_of_mem_edges hf hxyH.symm
    have hxv₀ : x = v₀ := hW_init_first x hx_s hxyC.2.1
    have hyv₀ : y = v₀ := hW_init_first y hy_s hxyC.2.2.1
    subst hxv₀ hyv₀
    exact not_isLink_self_of_mem_edges_of_isSimple W_init hsp_init_rem.1 hf hxyH
  have hinf_eq : Drawing.inf H C P = Drawing.inf H C (walkDrawing H W_rem) := by
    rw [hP_eq, hsplit]
    apply Drawing.ext_of_V_E
    · rw [Drawing.inf_V hC (walkDrawing_isSubdrawing H _),
        Drawing.inf_V hC (walkDrawing_isSubdrawing H _), walkDrawing_V, walkDrawing_V]
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.mem_support_append]
      constructor
      · rintro ⟨hxC, hx₁ | hx₂⟩
        · rw [hW_init_first x hx₁ hxC]
          exact ⟨hv₀C, W_rem.start_mem_support⟩
        · exact ⟨hxC, hx₂⟩
      · rintro ⟨hxC, hx₂⟩
        exact ⟨hxC, Or.inr hx₂⟩
    · rw [Drawing.inf_E hC, Drawing.inf_E hC, walkDrawing_E, walkDrawing_E]
      ext f
      simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.edges_append, List.mem_append]
      constructor
      · rintro ⟨hfC, hf₁ | hf₂⟩
        · exact (hW_init_no_edge f hf₁ hfC).elim
        · exact ⟨hfC, hf₂⟩
      · rintro ⟨hfC, hf₂⟩
        exact ⟨hfC, Or.inr hf₂⟩
  rcases walk_inf_isPath_or_exists_detour hC W_rem hsp_init_rem.2 hv₀C with
    ⟨u, _, hpath⟩ |
    ⟨v, hvC, v', hv'C, hvv', W_pre, W_sub, W_post, hrem_eq, hVC, hEC, hex_e⟩
  · left
    exact ⟨v₀, u, hinf_eq ▸ hpath⟩
  · right
    have hW_all : W = (W_init.append W_pre).append (W_sub.append W_post) := by
      rw [hsplit, hrem_eq]
      clear * -
      induction W_init with
      | nil _ => rfl
      | cons _ _ ih => simp [GraphWalk.append, ih]
    have hvP : v ∈ P.V := by
      rw [hP_eq, hW_all, walkDrawing_V, mem_ofPred_eq, GraphWalk.mem_support_append]
      exact Or.inl (W_init.append W_pre).end_mem_support
    have hv'P : v' ∈ P.V := by
      rw [hP_eq, hW_all, walkDrawing_V, mem_ofPred_eq, GraphWalk.mem_support_append]
      exact Or.inr ((GraphWalk.mem_support_append W_sub W_post).mpr (Or.inl W_sub.end_mem_support))
    exact ⟨v, ⟨hvC, hvP⟩, v', ⟨hv'C, hv'P⟩, hvv', W_init.append W_pre, W_sub, W_post,
      hW_all ▸ hWs, hW_all ▸ hP_eq, hVC, hEC, hex_e⟩

/-! ## 3. Suffix Inside-Disc Dichotomy and Walk Rerouting -/

theorem GraphWalk.append_assoc {α β : Type*} {G : Graph α β} {a b c d : α}
    (W₁ : GraphWalk G a b) (W₂ : GraphWalk G b c) (W₃ : GraphWalk G c d) :
    (W₁.append W₂).append W₃ = W₁.append (W₂.append W₃) := by
  induction W₁ with
  | nil _ => rfl
  | cons _ _ ih => simp [GraphWalk.append, ih]

theorem walkDrawing_append_U (H : Drawing S) {a b c : S}
    (W₁ : GraphWalk H.toGraph a b) (W₂ : GraphWalk H.toGraph b c) :
    (walkDrawing H (W₁.append W₂)).U = (walkDrawing H W₁).U ∪ (walkDrawing H W₂).U := by
  ext x
  simp only [mem_walkDrawing_U, mem_union, GraphWalk.mem_support_append, GraphWalk.edges_append,
    List.mem_append]
  constructor
  · rintro ((hx | hx) | ⟨e, he | he, hxe⟩)
    · exact Or.inl (Or.inl hx)
    · exact Or.inr (Or.inl hx)
    · exact Or.inl (Or.inr ⟨e, he, hxe⟩)
    · exact Or.inr (Or.inr ⟨e, he, hxe⟩)
  · rintro ((hx | ⟨e, he, hxe⟩) | (hx | ⟨e, he, hxe⟩))
    · exact Or.inl (Or.inl hx)
    · exact Or.inr ⟨e, Or.inl he, hxe⟩
    · exact Or.inl (Or.inr hx)
    · exact Or.inr ⟨e, Or.inr he, hxe⟩

omit [T2Space S] in
/-- For a line `L` with ends `a ≠ b`, `L \ {a}` is preconnected and contains `b`. -/
theorem IsLineWithEnds.isPreconnected_diff_left {L : Set S} {a b : S}
    (hL : IsLineWithEnds L a b) (hab : a ≠ b) :
    IsPreconnected (L \ {a}) ∧ b ∈ L \ {a} := by
  obtain ⟨f, hf0, hf1⟩ := hL
  have hb : b ∈ L \ {a} := ⟨hf1 ▸ (f 1).2, fun h => hab (mem_singleton_iff.mp h).symm⟩
  refine ⟨?_, hb⟩
  have hEq : L \ {a} = (fun t : ℝ => (f (projIcc 0 1 zero_le_one t)).1) '' Ioc (0 : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨hxL, hxa⟩
      let t : unitInterval := f.symm ⟨x, hxL⟩
      have ht : (f t).1 = x := congrArg Subtype.val (f.apply_symm_apply ⟨x, hxL⟩)
      have ht0 : (0 : ℝ) < t.1 := by
        refine lt_of_le_of_ne t.2.1 fun h0 => hxa ?_
        have ht_eq : t = 0 := Subtype.ext h0.symm
        exact mem_singleton_iff.mpr (ht.symm.trans (ht_eq ▸ hf0))
      refine ⟨t.1, ⟨ht0, t.2.2⟩, ?_⟩
      have hp : projIcc (0 : ℝ) 1 zero_le_one t.1 = t := projIcc_of_mem zero_le_one t.2
      simp [hp, ht]
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      have hp : projIcc (0 : ℝ) 1 zero_le_one t = ⟨t, ht0.le, ht1⟩ :=
        projIcc_of_mem zero_le_one ⟨ht0.le, ht1⟩
      refine ⟨(f _).2, fun hxa => ?_⟩
      have heq : f (projIcc 0 1 zero_le_one t) = f 0 :=
        Subtype.ext ((mem_singleton_iff.mp hxa).trans hf0.symm)
      have hinj := f.injective heq
      rw [hp] at hinj
      exact ht0.ne (congrArg Subtype.val hinj).symm
  rw [hEq]
  have hcont : Continuous (fun t : ℝ => (f (projIcc 0 1 zero_le_one t)).1) :=
    continuous_subtype_val.comp (f.continuous.comp continuous_projIcc)
  exact (convex_Ioc (0 : ℝ) 1).isPreconnected.image _ hcont.continuousOn

/-- If a simple walk `W` from `v ∈ C.V` to `b ∈ Δ \ C.U` meets `C.V` only at `v` and is
edge-disjoint from `C.E`, then `(walkDrawing H W).U ⊆ Δ`. -/
private theorem tail_subset_disc_of_inter_eq_singleton {H C : Drawing S} {Δ : Set S}
    (hC : C.IsSubdrawing H) (hΔ : IsClosed Δ) (hfr : frontier Δ = C.U)
    {v b : S} (W : GraphWalk H.toGraph v b) (hWs : W.IsSimple)
    (hvC : v ∈ C.V) (hb : b ∈ Δ \ C.U)
    (hVC : (walkDrawing H W).V ∩ C.V = {v}) (hEC : Disjoint (walkDrawing H W).E C.E) :
    (walkDrawing H W).U ⊆ Δ := by
  let P := walkDrawing H W
  have hPs : P.IsSubdrawing H := walkDrawing_isSubdrawing H W
  have hP_path : P.IsPathBetween v b := walkDrawing_isPathBetween H hWs
  have hvCU : v ∈ C.U := C.V_subset_U hvC
  have hvb : v ≠ b := fun h => hb.2 (h ▸ hvCU)
  have hL : IsLineWithEnds P.U v b := GM14.isLine_of_isPathBetween hP_path hvb
  obtain ⟨hpre, hb_in⟩ := IsLineWithEnds.isPreconnected_diff_left hL hvb
  have hU_inter : P.U ∩ C.U = {v} := by
    rw [GM14.U_inter_of_disjoint hPs hC hEC, hVC]
  have hdis_fr : Disjoint (P.U \ {v}) (frontier Δ) := by
    rw [hfr]
    refine disjoint_left.mpr fun x hx hxC => hx.2 ?_
    have : x ∈ P.U ∩ C.U := ⟨hx.1, hxC⟩
    rwa [hU_inter] at this
  have hsub : P.U \ {v} ⊆ Δ := by
    rcases GM14.subset_or_disjoint_of_frontier hΔ hpre hdis_fr with hsub | hdis
    · exact hsub
    · exact (disjoint_left.mp hdis hb_in hb.1).elim
  intro x hx
  by_cases hxv : x = v
  · subst hxv
    exact hΔ.frontier_subset (hfr.symm ▸ hvCU)
  · exact hsub ⟨hx, hxv⟩

/-- For any simple walk `W` in `H` from `v ∈ C.V` to `b ∈ Δ \ C.U` (where `Δ` is closed with
`frontier Δ = C.U`), either `(walkDrawing H W).U ⊆ Δ`, or `W` decomposes as
`W_pre.append (W_sub.append W_post)` where `P_sub = walkDrawing H W_sub` is an outer detour on `C`
(`¬ P_sub.U ⊆ Δ`). -/
theorem walk_subset_disc_or_exists_outer_detour {H C : Drawing S} {Δ : Set S}
    (hC : C.IsSubdrawing H) (hΔ : IsClosed Δ) (hfr : frontier Δ = C.U)
    {v b : S} (W : GraphWalk H.toGraph v b) (hWs : W.IsSimple)
    (hv : v ∈ C.V) (hb : b ∈ Δ \ C.U) :
    (walkDrawing H W).U ⊆ Δ ∨
      ∃ u₁ ∈ C.V, ∃ u₂ ∈ C.V, u₁ ≠ u₂ ∧
        ∃ (W_pre : GraphWalk H.toGraph v u₁) (W_sub : GraphWalk H.toGraph u₁ u₂)
          (W_post : GraphWalk H.toGraph u₂ b),
          W = W_pre.append (W_sub.append W_post) ∧
          (walkDrawing H W_sub).V ∩ C.V = {u₁, u₂} ∧
          Disjoint (walkDrawing H W_sub).E C.E ∧
          ¬ (walkDrawing H W_sub).U ⊆ Δ := by
  suffices hlen : ∀ n : ℕ, ∀ {v : S} (W : GraphWalk H.toGraph v b), W.length = n →
      W.IsSimple → v ∈ C.V →
      (walkDrawing H W).U ⊆ Δ ∨
        ∃ u₁ ∈ C.V, ∃ u₂ ∈ C.V, u₁ ≠ u₂ ∧
          ∃ (W_pre : GraphWalk H.toGraph v u₁) (W_sub : GraphWalk H.toGraph u₁ u₂)
            (W_post : GraphWalk H.toGraph u₂ b),
            W = W_pre.append (W_sub.append W_post) ∧
            (walkDrawing H W_sub).V ∩ C.V = {u₁, u₂} ∧
            Disjoint (walkDrawing H W_sub).E C.E ∧
            ¬ (walkDrawing H W_sub).U ⊆ Δ from
    hlen W.length W rfl hWs hv
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a W hn hWs hv
    cases W with
    | nil _ =>
      exact (hb.2 (C.V_subset_U hv)).elim
    | @cons a w b e hl r =>
      have ha_not_r : a ∉ r.support := (List.nodup_cons.mp hWs).1
      have hr_s : r.IsSimple := (List.nodup_cons.mp hWs).2
      have hr_lt : r.length < n := by rw [← hn, GraphWalk.length_cons]; omega
      by_cases heC : e ∈ C.E
      · have hlC : C.toGraph.IsLink e a w := (hC.isLink_iff heC).mpr hl
        have hwC : w ∈ C.V := hlC.2.2.1
        rcases ih r.length hr_lt r rfl hr_s hwC with hr_in |
          ⟨u₁, hu₁C, u₂, hu₂C, hu12, W_pre, W_sub, W_post, hr_eq, hVC, hEC, hnot_in⟩
        · left
          have hcons_eq : GraphWalk.cons hl r =
              (GraphWalk.cons hl (.nil hl.right_mem)).append r := rfl
          rw [hcons_eq, walkDrawing_append_U]
          refine union_subset ?_ hr_in
          have he_sub : (walkDrawing H (GraphWalk.cons hl (.nil hl.right_mem))).U ⊆ C.U := by
            intro x hx
            rw [mem_walkDrawing_U] at hx
            rcases hx with hxV | ⟨f, hf, hxf⟩
            · simp only [GraphWalk.support_cons, GraphWalk.support_nil, List.mem_cons,
                List.not_mem_nil, or_false] at hxV
              rcases hxV with rfl | rfl
              · exact C.V_subset_U hv
              · exact C.V_subset_U hwC
            · simp only [GraphWalk.edges_cons, GraphWalk.edges_nil, List.mem_singleton] at hf
              subst hf
              exact C.closure_subset_U heC hxf
          exact he_sub.trans (hfr ▸ hΔ.frontier_subset)
        · right
          refine ⟨u₁, hu₁C, u₂, hu₂C, hu12, .cons hl W_pre, W_sub, W_post, ?_, hVC, hEC, hnot_in⟩
          rw [hr_eq]; rfl
      · by_cases hhit : ∃ x ∈ r.support, x ∈ C.V
        · obtain ⟨v', hv'C, r₁, r₂, hsplit_r, hr₁_first⟩ := exists_first_hit_split r hhit
          have hr₁_s : r₁.IsSimple := (isSimple_of_append (hsplit_r ▸ hr_s)).1
          have hr₂_s : r₂.IsSimple := (isSimple_of_append (hsplit_r ▸ hr_s)).2
          have ha_not_r₁ : a ∉ r₁.support := fun ha_in =>
            ha_not_r (hsplit_r ▸ (GraphWalk.mem_support_append r₁ r₂).mpr (Or.inl ha_in))
          have hav' : a ≠ v' := fun h => ha_not_r₁ (h ▸ r₁.end_mem_support)
          let W_sub := GraphWalk.cons hl r₁
          have hr₁_no_edge : ∀ f ∈ r₁.edges, f ∉ C.E := by
            intro f hf₁ hfC
            obtain ⟨x, y, hxyH⟩ := (H.toGraph.edge_mem_iff_exists_isLink f).mp (hC.2 hfC)
            have hxyC : C.toGraph.IsLink f x y := (hC.isLink_iff hfC).mpr hxyH
            have hx_s : x ∈ r₁.support := r₁.left_mem_support_of_mem_edges hf₁ hxyH
            have hy_s : y ∈ r₁.support := r₁.left_mem_support_of_mem_edges hf₁ hxyH.symm
            have hxv' : x = v' := hr₁_first x hx_s hxyC.2.1
            have hyv' : y = v' := hr₁_first y hy_s hxyC.2.2.1
            subst hxv' hyv'
            exact not_isLink_self_of_mem_edges_of_isSimple r₁ hr₁_s hf₁ hxyH
          have hVC : (walkDrawing H W_sub).V ∩ C.V = {a, v'} := by
            rw [walkDrawing_V]
            ext x
            simp only [W_sub, mem_inter_iff, mem_ofPred_eq, GraphWalk.support_cons, List.mem_cons,
              mem_insert_iff]
            constructor
            · rintro ⟨rfl | hx₁, hxC⟩
              · exact Or.inl rfl
              · exact Or.inr (hr₁_first x hx₁ hxC)
            · rintro (rfl | rfl)
              · exact ⟨Or.inl rfl, hv⟩
              · exact ⟨Or.inr r₁.end_mem_support, hv'C⟩
          have hEC : Disjoint (walkDrawing H W_sub).E C.E := by
            rw [walkDrawing_E]
            refine disjoint_left.mpr fun f hf hfC => ?_
            rcases List.mem_cons.mp hf with rfl | hf₁
            · exact heC hfC
            · exact hr₁_no_edge f hf₁ hfC
          by_cases hsub_in : (walkDrawing H W_sub).U ⊆ Δ
          · have hr₂_lt : r₂.length < n := by
              rw [← hn, GraphWalk.length_cons, hsplit_r, GraphWalk.length_append]
              omega
            rcases ih r₂.length hr₂_lt r₂ rfl hr₂_s hv'C with hr₂_in |
              ⟨u₁, hu₁C, u₂, hu₂C, hu12, W_pre, W_sub', W_post, hr₂_eq, hVC', hEC', hnot_in'⟩
            · left
              have hcons_eq : GraphWalk.cons hl r = W_sub.append r₂ := by rw [hsplit_r]; rfl
              rw [hcons_eq, walkDrawing_append_U]
              exact union_subset hsub_in hr₂_in
            · right
              refine ⟨u₁, hu₁C, u₂, hu₂C, hu12, W_sub.append W_pre, W_sub', W_post, ?_,
                hVC', hEC', hnot_in'⟩
              have hcons_eq : GraphWalk.cons hl r = W_sub.append r₂ := by rw [hsplit_r]; rfl
              rw [hcons_eq, hr₂_eq, GraphWalk.append_assoc]
          · right
            refine ⟨a, hv, v', hv'C, hav', .nil hl.left_mem, W_sub, r₂, ?_, hVC, hEC, hsub_in⟩
            rw [hsplit_r]; rfl
        · left
          have hhit' : ∀ x ∈ r.support, x ∉ C.V := fun x hx hxC => hhit ⟨x, hx, hxC⟩
          have hVC : (walkDrawing H (GraphWalk.cons hl r)).V ∩ C.V = {a} := by
            rw [walkDrawing_V]
            ext x
            simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.support_cons, List.mem_cons]
            constructor
            · rintro ⟨rfl | hxr, hxC⟩
              · rfl
              · exact (hhit' x hxr hxC).elim
            · rintro rfl
              exact ⟨Or.inl rfl, hv⟩
          have hEC : Disjoint (walkDrawing H (GraphWalk.cons hl r)).E C.E := by
            rw [walkDrawing_E]
            refine disjoint_left.mpr fun f hf hfC => ?_
            rcases List.mem_cons.mp hf with rfl | hfr
            · exact heC hfC
            · obtain ⟨x, y, hxyH⟩ := (H.toGraph.edge_mem_iff_exists_isLink f).mp (hC.2 hfC)
              have hxyC : C.toGraph.IsLink f x y := (hC.isLink_iff hfC).mpr hxyH
              have hx_r : x ∈ r.support := r.left_mem_support_of_mem_edges hfr hxyH
              exact hhit' x hx_r hxyC.2.1
          exact tail_subset_disc_of_inter_eq_singleton hC hΔ hfr (GraphWalk.cons hl r) hWs hv hb
            hVC hEC

/-- Rerouting a path `P = walkDrawing H (W₁.append (W_sub.append W₂))` by replacing `W_sub` with a
path `Q` in `H` between `v` and `v'` produces a path `P'` in `H` between `a` and `b` with
`P'.V ⊆ P.V ∪ Q.V` and `P'.E ⊆ (P.E \ (walkDrawing H W_sub).E) ∪ Q.E`. -/
theorem reroute_drawing_path {H P Q : Drawing S} {a b v v' : S}
    {W₁ : GraphWalk H.toGraph a v} {W_sub : GraphWalk H.toGraph v v'}
    {W₂ : GraphWalk H.toGraph v' b}
    (hWs : (W₁.append (W_sub.append W₂)).IsSimple)
    (hP_eq : P = walkDrawing H (W₁.append (W_sub.append W₂)))
    (hQs : Q.IsSubdrawing H) (hQ : Q.IsPathBetween v v') :
    ∃ P' : Drawing S, P'.IsSubdrawing H ∧ P'.IsPathBetween a b ∧
      P'.V ⊆ P.V ∪ Q.V ∧ P'.E ⊆ (P.E \ (walkDrawing H W_sub).E) ∪ Q.E := by
  obtain ⟨WQ₀, _, hVQ, hEQ⟩ := hQ
  obtain ⟨WQ, hsQ, heQ⟩ := hQs.exists_walk_up WQ₀
  let W_all := W₁.append (WQ.append W₂)
  obtain ⟨W', hW's, hsupp, hedges⟩ := exists_isSimple_subwalk W_all
  let P' := walkDrawing H W'
  have hnd_edges : (W₁.edges ++ (W_sub.edges ++ W₂.edges)).Nodup := by
    have h := hWs.edges_nodup
    rwa [GraphWalk.edges_append, GraphWalk.edges_append] at h
  have hd₁ := List.nodup_append.mp hnd_edges
  have hd₂ := List.nodup_append.mp hd₁.2.1
  refine ⟨P', walkDrawing_isSubdrawing H W', walkDrawing_isPathBetween H hW's, ?_, ?_⟩
  · intro x hx
    rw [walkDrawing_V, mem_ofPred_eq] at hx
    have hx_all := hsupp x hx
    simp only [W_all, GraphWalk.mem_support_append] at hx_all
    rcases hx_all with hx₁ | hxQ | hx₂
    · left
      rw [hP_eq, walkDrawing_V, mem_ofPred_eq, GraphWalk.mem_support_append]
      exact Or.inl hx₁
    · right
      rw [hVQ, mem_ofPred_eq, ← hsQ]
      exact hxQ
    · left
      rw [hP_eq, walkDrawing_V, mem_ofPred_eq, GraphWalk.mem_support_append,
        GraphWalk.mem_support_append]
      exact Or.inr (Or.inr hx₂)
  · intro e he
    rw [walkDrawing_E, mem_ofPred_eq] at he
    have he_all := hedges e he
    simp only [W_all, GraphWalk.edges_append, List.mem_append] at he_all
    rcases he_all with he₁ | heQ' | he₂
    · left
      refine ⟨?_, ?_⟩
      · rw [hP_eq, walkDrawing_E, mem_ofPred_eq, GraphWalk.edges_append, List.mem_append]
        exact Or.inl he₁
      · rw [walkDrawing_E, mem_ofPred_eq]
        exact fun hsub => hd₁.2.2 e he₁ e (List.mem_append_left _ hsub) rfl
    · right
      rw [hEQ, mem_ofPred_eq, ← heQ]
      exact heQ'
    · left
      refine ⟨?_, ?_⟩
      · rw [hP_eq, walkDrawing_E, mem_ofPred_eq, GraphWalk.edges_append, GraphWalk.edges_append,
          List.mem_append, List.mem_append]
        exact Or.inr (Or.inr he₂)
      · rw [walkDrawing_E, mem_ofPred_eq]
        exact fun hsub => hd₂.2.2 e hsub e he₂ rfl

/-! ## 4. Total Union Edge Count and Strict-Decrease Moves -/

/-- The set of all edges in `C₁ ∪ ⋯ ∪ C_s ∪ P₁ ∪ ⋯ ∪ P_r`. -/
def totalDrawingEdgeSet {s r : ℕ} (C : Fin s → Drawing S) (P : Fin r → Drawing S) : Set (Set S) :=
  (⋃ j : Fin s, (C j).E) ∪ (⋃ i : Fin r, (P i).E)

/-- The total number of edges `|E(C₁ ∪ ⋯ ∪ C_s ∪ P₁ ∪ ⋯ ∪ P_r)|` minimized in `(1)` of the proof of
Graph Minors III, (4.1) (page 60). -/
noncomputable def totalDrawingEdges {s r : ℕ} (C : Fin s → Drawing S) (P : Fin r → Drawing S) :
    ℕ :=
  (totalDrawingEdgeSet C P).ncard

omit [T2Space S] in
theorem totalDrawingEdgeSet_finite {s r : ℕ} {H : Drawing S}
    {C : Fin s → Drawing S} {P : Fin r → Drawing S}
    (hCH : ∀ j, (C j).IsSubdrawing H) (hPH : ∀ i, (P i).IsSubdrawing H) :
    (totalDrawingEdgeSet C P).Finite := by
  refine H.finite_edges.subset ?_
  exact union_subset (iUnion_subset fun j => (hCH j).2) (iUnion_subset fun i => (hPH i).2)

omit [T2Space S] in
/-- Condition `(1)` of the proof of Graph Minors III, (4.1) (page 60):
choose `C₁, …, C_s, P₁, …, P_r` with `|E(C₁ ∪ ⋯ ∪ C_s ∪ P₁ ∪ ⋯ ∪ P_r)|` minimum. -/
theorem exists_min_totalDrawingEdges {s r : ℕ}
    (IsValidPair : (Fin s → Drawing S) → (Fin r → Drawing S) → Prop)
    (hex : ∃ C₀ P₀, IsValidPair C₀ P₀) :
    ∃ C P, IsValidPair C P ∧
      ∀ C' P', IsValidPair C' P' → totalDrawingEdges C P ≤ totalDrawingEdges C' P' := by
  classical
  obtain ⟨C₀, P₀, h₀⟩ := hex
  have hne : {n : ℕ | ∃ C P, IsValidPair C P ∧ totalDrawingEdges C P = n}.Nonempty :=
    ⟨totalDrawingEdges C₀ P₀, C₀, P₀, h₀, rfl⟩
  obtain ⟨C, P, hCP, hmin⟩ := Nat.sInf_mem hne
  refine ⟨C, P, hCP, fun C' P' h' => ?_⟩
  rw [hmin]
  exact Nat.sInf_le ⟨C', P', h', rfl⟩

omit [T2Space S] in
theorem disjoint_E_of_disjoint_V {H A B : Drawing S} (hA : A.IsSubdrawing H)
    (hB : B.IsSubdrawing H) (hV : Disjoint A.V B.V) : Disjoint A.E B.E := by
  refine disjoint_left.mpr fun e heA heB => ?_
  obtain ⟨x, y, hxyH⟩ := (H.toGraph.edge_mem_iff_exists_isLink e).mp (hA.2 heA)
  have hxyA : A.toGraph.IsLink e x y := (hA.isLink_iff heA).mpr hxyH
  have hxyB : B.toGraph.IsLink e x y := (hB.isLink_iff heB).mpr hxyH
  exact disjoint_left.mp hV hxyA.2.1 hxyB.2.1

/-- **Move 2 (Outer detour circuit replacement, GM03 (4.1) paragraph 4, page 60)**:
Replacing `C j` by `H.sup P_sub Q₁` when `Q₂` has an edge `e₀` not in `⋃ k, (P k).E` strictly
decreases `totalDrawingEdges C P`. -/
theorem totalDrawingEdges_lt_of_replace_circuit {s r : ℕ} [DecidableEq (Fin s)] {H : Drawing S}
    {C : Fin s → Drawing S} {P : Fin r → Drawing S}
    (hCH : ∀ m, (C m).IsSubdrawing H) (hPH : ∀ k, (P k).IsSubdrawing H)
    (hC_disj : Pairwise (fun m₁ m₂ => Disjoint (C m₁).V (C m₂).V))
    {j : Fin s} {i : Fin r} {P_sub Q₁ Q₂ : Drawing S}
    (hP_sub : P_sub.IsSubdrawing (P i)) (hQ₁ : Q₁.IsSubdrawing (C j))
    (hQ₂ : Q₂.IsSubdrawing (C j)) (hQ_disj : Disjoint Q₁.E Q₂.E)
    {e₀ : Set S} (he₀_Q₂ : e₀ ∈ Q₂.E) (he₀_not_P : ∀ k : Fin r, e₀ ∉ (P k).E) :
    totalDrawingEdges (Function.update C j (H.sup P_sub Q₁)) P < totalDrawingEdges C P := by
  have : T1Space S := inferInstance
  have hP_sub_H : P_sub.IsSubdrawing H := hP_sub.trans (hPH i)
  have hQ₁_H : Q₁.IsSubdrawing H := hQ₁.trans (hCH j)
  have he₀_Cj : e₀ ∈ (C j).E := hQ₂.2 he₀_Q₂
  have hsub : totalDrawingEdgeSet (Function.update C j (H.sup P_sub Q₁)) P ⊆
      totalDrawingEdgeSet C P := by
    rintro f (hfC | hfP)
    · obtain ⟨m, hfm⟩ := mem_iUnion.mp hfC
      by_cases hmj : m = j
      · subst hmj
        rw [Function.update_self, H.sup_E hP_sub_H hQ₁_H] at hfm
        rcases hfm with hfm_P | hfm_Q₁
        · exact Or.inr (mem_iUnion.mpr ⟨i, hP_sub.2 hfm_P⟩)
        · exact Or.inl (mem_iUnion.mpr ⟨m, hQ₁.2 hfm_Q₁⟩)
      · rw [Function.update_of_ne hmj] at hfm
        exact Or.inl (mem_iUnion.mpr ⟨m, hfm⟩)
    · exact Or.inr hfP
  have he₀_in : e₀ ∈ totalDrawingEdgeSet C P := Or.inl (mem_iUnion.mpr ⟨j, he₀_Cj⟩)
  have he₀_not_in :
      e₀ ∉ totalDrawingEdgeSet (Function.update C j (H.sup P_sub Q₁)) P := by
    rintro (heC | heP)
    · obtain ⟨m, hem⟩ := mem_iUnion.mp heC
      by_cases hmj : m = j
      · subst hmj
        rw [Function.update_self, H.sup_E hP_sub_H hQ₁_H] at hem
        rcases hem with hem_P | hem_Q₁
        · exact he₀_not_P i (hP_sub.2 hem_P)
        · exact disjoint_left.mp hQ_disj hem_Q₁ he₀_Q₂
      · rw [Function.update_of_ne hmj] at hem
        have hdisjE := disjoint_E_of_disjoint_V (hCH j) (hCH m) (hC_disj (Ne.symm hmj))
        exact disjoint_left.mp hdisjE he₀_Cj hem
    · obtain ⟨k, hek⟩ := mem_iUnion.mp heP
      exact he₀_not_P k hek
  exact Set.ncard_lt_ncard ⟨hsub, fun h => he₀_not_in (h he₀_in)⟩
    (totalDrawingEdgeSet_finite hCH hPH)

omit [T2Space S] in
/-- **Move 3 (Inner detour path rerouting, GM03 (4.1) paragraph 6, page 61)**:
Rerouting `P i` along `Q_k ≤ C j` while omitting `P_sub.E` preserves pairwise vertex-disjointness
and strictly decreases `totalDrawingEdges C P`. -/
theorem totalDrawingEdges_lt_of_reroute_path {s r : ℕ} [DecidableEq (Fin r)] {H : Drawing S}
    {C : Fin s → Drawing S} {P : Fin r → Drawing S}
    (hCH : ∀ m, (C m).IsSubdrawing H) (hPH : ∀ k, (P k).IsSubdrawing H)
    (hP_disj : Pairwise (fun k₁ k₂ => Disjoint (P k₁).V (P k₂).V))
    {j : Fin s} {i : Fin r} {P_sub Q_k P'_i : Drawing S}
    (hP_sub : P_sub.IsSubdrawing (P i)) (hQ_k : Q_k.IsSubdrawing (C j))
    (hP'_V : P'_i.V ⊆ (P i).V ∪ Q_k.V)
    (hP'_E : P'_i.E ⊆ ((P i).E \ P_sub.E) ∪ Q_k.E)
    (hQ_disj_other : ∀ i' : Fin r, i' ≠ i → Disjoint Q_k.V (P i').V)
    {e₁ : Set S} (he₁_sub : e₁ ∈ P_sub.E) (he₁_not_C : ∀ m : Fin s, e₁ ∉ (C m).E) :
    Pairwise (fun k₁ k₂ => Disjoint (Function.update P i P'_i k₁).V (Function.update P i P'_i
      k₂).V) ∧
      totalDrawingEdges C (Function.update P i P'_i) < totalDrawingEdges C P := by
  refine ⟨?_, ?_⟩
  · intro k₁ k₂ hk₁₂
    by_cases hk₁ : k₁ = i
    · subst hk₁
      have hk₂ : k₂ ≠ k₁ := hk₁₂.symm
      rw [Function.update_self, Function.update_of_ne hk₂]
      exact disjoint_of_subset_left hP'_V
        (disjoint_union_left.mpr ⟨hP_disj hk₁₂, hQ_disj_other k₂ hk₂⟩)
    · by_cases hk₂ : k₂ = i
      · subst hk₂
        rw [Function.update_of_ne hk₁, Function.update_self]
        exact disjoint_of_subset_right hP'_V
          (disjoint_union_right.mpr ⟨hP_disj hk₁₂, (hQ_disj_other k₁ hk₁).symm⟩)
      · rw [Function.update_of_ne hk₁, Function.update_of_ne hk₂]
        exact hP_disj hk₁₂
  · have he₁_Pi : e₁ ∈ (P i).E := hP_sub.2 he₁_sub
    have hsub : totalDrawingEdgeSet C (Function.update P i P'_i) ⊆ totalDrawingEdgeSet C P := by
      rintro f (hfC | hfP)
      · exact Or.inl hfC
      · obtain ⟨k, hfk⟩ := mem_iUnion.mp hfP
        by_cases hki : k = i
        · subst hki
          rw [Function.update_self] at hfk
          rcases hP'_E hfk with ⟨hfPi, _⟩ | hfQ
          · exact Or.inr (mem_iUnion.mpr ⟨k, hfPi⟩)
          · exact Or.inl (mem_iUnion.mpr ⟨j, hQ_k.2 hfQ⟩)
        · rw [Function.update_of_ne hki] at hfk
          exact Or.inr (mem_iUnion.mpr ⟨k, hfk⟩)
    have he₁_in : e₁ ∈ totalDrawingEdgeSet C P := Or.inr (mem_iUnion.mpr ⟨i, he₁_Pi⟩)
    have he₁_not_in : e₁ ∉ totalDrawingEdgeSet C (Function.update P i P'_i) := by
      rintro (heC | heP)
      · obtain ⟨m, hem⟩ := mem_iUnion.mp heC
        exact he₁_not_C m hem
      · obtain ⟨k, hek⟩ := mem_iUnion.mp heP
        by_cases hki : k = i
        · subst hki
          rw [Function.update_self] at hek
          rcases hP'_E hek with ⟨_, he_not_sub⟩ | heQ
          · exact he_not_sub he₁_sub
          · exact he₁_not_C j (hQ_k.2 heQ)
        · rw [Function.update_of_ne hki] at hek
          have hdisjE := disjoint_E_of_disjoint_V (hPH i) (hPH k) (hP_disj (Ne.symm hki))
          exact disjoint_left.mp hdisjE he₁_Pi hek
    exact Set.ncard_lt_ncard ⟨hsub, fun h => he₁_not_in (h he₁_in)⟩
      (totalDrawingEdgeSet_finite hCH hPH)

/-! ## 5. Closed-Disc Nest Uncrossing (Graph Minors III, Theorem (4.1)) -/

omit [T2Space S] in
theorem frontier_inter_subset_frontier_of_subset {A B : Set S} (hAB : A ⊆ B) :
    A ∩ frontier B ⊆ frontier A := fun _ ⟨hxA, hxB⟩ =>
  ⟨subset_closure hxA, fun hx_int => hxB.2 (interior_mono hAB hx_int)⟩

/-- If `W₁.append W₂` is a simple walk in `H` where `W₁` ends at `v` and `W₂` starts at `v`, then
`(walkDrawing H W₁).U ∩ (walkDrawing H W₂).U = {v}`. -/
theorem walkDrawing_append_U_inter {H : Drawing S} {a v b : S}
    (W₁ : GraphWalk H.toGraph a v) (W₂ : GraphWalk H.toGraph v b)
    (hWs : (W₁.append W₂).IsSimple) :
    (walkDrawing H W₁).U ∩ (walkDrawing H W₂).U = {v} := by
  have hnd_V : (W₁.support ++ W₂.support.tail).Nodup := by
    have h := hWs
    rwa [GraphWalk.IsSimple, GraphWalk.support_append] at h
  have hd_V := List.nodup_append.mp hnd_V
  have hnd_E : (W₁.edges ++ W₂.edges).Nodup := by
    have h := hWs.edges_nodup
    rwa [GraphWalk.edges_append] at h
  have hd_E := List.nodup_append.mp hnd_E
  have hdisjE : Disjoint (walkDrawing H W₁).E (walkDrawing H W₂).E := by
    rw [walkDrawing_E, walkDrawing_E]
    exact disjoint_left.mpr fun e he₁ he₂ => hd_E.2.2 e he₁ e he₂ rfl
  rw [GM14.U_inter_of_disjoint (walkDrawing_isSubdrawing H W₁) (walkDrawing_isSubdrawing H W₂)
      hdisjE, walkDrawing_V, walkDrawing_V]
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hx₁, hx₂⟩
    rw [W₂.support_eq_cons] at hx₂
    rcases List.mem_cons.mp hx₂ with rfl | hx₂_tail
    · rfl
    · exact (hd_V.2.2 x hx₁ x hx₂_tail rfl).elim
  · rintro rfl
    exact ⟨W₁.end_mem_support, W₂.start_mem_support⟩

/-- If `W = W₁.append W₂` is a simple walk in `H` with `W₁ : GraphWalk H.toGraph a v`,
`Drawing.inf H C (walkDrawing H W)` is a path in `H`, `(walkDrawing H W₁).U` meets `C.U`, and
`v ∉ C.U`, then `Disjoint (walkDrawing H W₂).U C.U`. -/
theorem disjoint_tail_of_inf_isPath {H C : Drawing S} (hC : C.IsSubdrawing H)
    {a v b : S} (W₁ : GraphWalk H.toGraph a v) (W₂ : GraphWalk H.toGraph v b)
    (hWs : (W₁.append W₂).IsSimple)
    (hinf : IsDrawingPath (Drawing.inf H C (walkDrawing H (W₁.append W₂))))
    (hmeet₁ : ((walkDrawing H W₁).U ∩ C.U).Nonempty)
    (hv_not : v ∉ C.U) :
    Disjoint (walkDrawing H W₂).U C.U := by
  let P₁ := walkDrawing H W₁
  let P₂ := walkDrawing H W₂
  let P := walkDrawing H (W₁.append W₂)
  let I := Drawing.inf H C P
  have hI_U : I.U = C.U ∩ P.U := Drawing.inf_U hC (walkDrawing_isSubdrawing H _)
  have hP_U : P.U = P₁.U ∪ P₂.U := walkDrawing_append_U H W₁ W₂
  have hP12_inter : P₁.U ∩ P₂.U = {v} := walkDrawing_append_U_inter W₁ W₂ hWs
  have hI_pre : IsPreconnected I.U := hinf.isPreconnected_U
  by_contra hnot_disj
  obtain ⟨y, hy₂, hyC⟩ := not_disjoint_iff.mp hnot_disj
  obtain ⟨x, hx₁, hxC⟩ := hmeet₁
  have hxI : x ∈ I.U := by
    rw [hI_U, hP_U]
    exact ⟨hxC, Or.inl hx₁⟩
  have hyI : y ∈ I.U := by
    rw [hI_U, hP_U]
    exact ⟨hyC, Or.inr hy₂⟩
  have hI_sub : I.U ⊆ P₁.U ∪ P₂.U := by
    rw [hI_U, hP_U]
    exact inter_subset_right
  obtain ⟨z, hzI, hz₁, hz₂⟩ :=
    isPreconnected_closed_iff.mp hI_pre P₁.U P₂.U P₁.isClosed_U P₂.isClosed_U hI_sub
      ⟨x, hxI, hx₁⟩ ⟨y, hyI, hy₂⟩
  have hzv : z = v := by
    have : z ∈ P₁.U ∩ P₂.U := ⟨hz₁, hz₂⟩
    rwa [hP12_inter, mem_singleton_iff] at this
  subst hzv
  rw [hI_U] at hzI
  exact hv_not hzI.1

/-- If `P : Fin r → Drawing S` is a family of pairwise vertex-disjoint paths in `H`,
`P_sub.IsSubdrawing (P i)`, `Q.IsSubdrawing H` is a path between `v` and `v'` with `v ∈ (P i).V`,
and `(H.sup P_sub Q).IsCircuit`, then `Q` has an edge `e₀ ∈ Q.E` not belonging to `(P m).E` for any
`m : Fin r`. -/
theorem exists_edge_not_in_paths_of_theta {r : ℕ} {H : Drawing S} {P : Fin r → Drawing S}
    (hPH : ∀ m, (P m).IsSubdrawing H)
    (hP_path : ∀ m, ∃ a b, (P m).IsPathBetween a b)
    (hP_disj : Pairwise (fun m₁ m₂ => Disjoint (P m₁).V (P m₂).V))
    {i : Fin r} {P_sub Q : Drawing S} {v v' : S} (hvv' : v ≠ v')
    (hP_sub : P_sub.IsSubdrawing (P i)) (hQ_H : Q.IsSubdrawing H)
    (hQ_path : Q.IsPathBetween v v') (hv_Pi : v ∈ (P i).V)
    (hcirc : (H.sup P_sub Q).IsCircuit) :
    ∃ e₀ ∈ Q.E, ∀ m : Fin r, e₀ ∉ (P m).E := by
  by_contra hall
  push Not at hall
  have hwalk_in_Pi : ∀ {x y : S} (W : GraphWalk H.toGraph x y),
      x ∈ (P i).V → (∀ e ∈ W.edges, ∃ m : Fin r, e ∈ (P m).E) →
      (∀ z ∈ W.support, z ∈ (P i).V) ∧ (∀ e ∈ W.edges, e ∈ (P i).E) := by
    intro x y W hx hed
    induction W with
    | @nil u _ =>
      exact ⟨fun z hz => (List.mem_singleton.mp hz) ▸ hx, fun e he => (List.not_mem_nil he).elim⟩
    | @cons u w _ e hl r ih =>
      obtain ⟨m, hem⟩ := hed e List.mem_cons_self
      have hl_m : (P m).toGraph.IsLink e u w := ((hPH m).isLink_iff hem).mpr hl
      have hu_m : u ∈ (P m).V := hl_m.2.1
      have hmi : m = i := by
        by_contra hne
        exact disjoint_left.mp (hP_disj hne) hu_m hx
      subst m
      have hw_i : w ∈ (P i).V := hl_m.2.2.1
      obtain ⟨hsupp, hedges⟩ := ih hw_i (fun f hf => hed f (List.mem_cons_of_mem _ hf))
      refine ⟨fun z hz => ?_, fun f hf => ?_⟩
      · rcases List.mem_cons.mp hz with rfl | hzr
        · exact hx
        · exact hsupp z hzr
      · rcases List.mem_cons.mp hf with rfl | hfr
        · exact hem
        · exact hedges f hfr
  obtain ⟨WQ₀, _, hVQ, hEQ⟩ := hQ_path
  obtain ⟨WQ, hsQ, heQ⟩ := hQ_H.exists_walk_up WQ₀
  have hed_WQ : ∀ e ∈ WQ.edges, ∃ m : Fin r, e ∈ (P m).E := by
    intro e he
    have he_Q : e ∈ Q.E := by rw [hEQ, mem_ofPred_eq, ← heQ]; exact he
    exact hall e he_Q
  obtain ⟨hsupp_Pi, hedges_Pi⟩ := hwalk_in_Pi WQ hv_Pi hed_WQ
  have hQ_sub_Pi : Q.IsSubdrawing (P i) := by
    refine ⟨fun z hz => ?_, fun e he => ?_⟩
    · rw [hVQ, mem_ofPred_eq, ← hsQ] at hz
      exact hsupp_Pi z hz
    · rw [hEQ, mem_ofPred_eq, ← heQ] at he
      exact hedges_Pi e he
  have hsup_U : (H.sup P_sub Q).U ⊆ (P i).U := by
    rw [Drawing.sup_U (hP_sub.trans (hPH i)) hQ_H]
    exact union_subset hP_sub.U_subset hQ_sub_Pi.U_subset
  obtain ⟨a_i, b_i, hPi_path⟩ := hP_path i
  have hab_ne : a_i ≠ b_i := by
    rintro rfl
    obtain ⟨W₀, hW₀, hPV₀, _⟩ := hPi_path
    have hlen : W₀.length = 0 := hW₀.length_eq_zero
    have hsupp₀ : W₀.support = [a_i] := by
      cases W₀ with
      | nil _ => rfl
      | cons _ _ => simp [GraphWalk.length] at hlen
    have hv'_Pi : v' ∈ (P i).V := hQ_sub_Pi.1 (by rw [hVQ]; exact WQ₀.end_mem_support)
    rw [hPV₀, hsupp₀] at hv_Pi hv'_Pi
    exact hvv' ((List.mem_singleton.mp hv_Pi).trans (List.mem_singleton.mp hv'_Pi).symm)
  exact GM14.no_circuit_in_path hPi_path hab_ne hcirc hsup_U

/-- If `A₀, A₁, A₂` form a theta graph between `a ≠ b` in a closed surface `S`, and `Δ₀, Δ₁, Δ₂` are
closed discs with `frontier Δ₀ = A₁ ∪ A₂`, `frontier Δ₁ = A₂ ∪ A₀`, `frontier Δ₂ = A₀ ∪ A₁` such
that `¬ A₀ ⊆ Δ₀` and `¬ A₁ ⊆ Δ₁`, then `Δ₀ ∩ Δ₁ = A₂`, `Disjoint (A₀ \ {a, b}) Δ₀`,
`Disjoint (A₁ \ {a, b}) Δ₁`, and `Δ₀ ∪ Δ₁` is a closed disc with `discBd (Δ₀ ∪ Δ₁) = discBd Δ₂`. -/
theorem theta_inner_chord_split (hS : IsClosedSurface S) {A₀ A₁ A₂ Δ₀ Δ₁ Δ₂ : Set S} {a b : S}
    (l₀ : IsLineWithEnds A₀ a b) (l₁ : IsLineWithEnds A₁ a b) (l₂ : IsLineWithEnds A₂ a b)
    (i₀₁ : A₀ ∩ A₁ = {a, b}) (i₁₂ : A₁ ∩ A₂ = {a, b}) (i₂₀ : A₂ ∩ A₀ = {a, b})
    (d₀ : IsClosedDisc Δ₀) (d₁ : IsClosedDisc Δ₁) (d₂ : IsClosedDisc Δ₂)
    (f₀ : frontier Δ₀ = A₁ ∪ A₂) (f₁ : frontier Δ₁ = A₂ ∪ A₀) (f₂ : frontier Δ₂ = A₀ ∪ A₁)
    (h₀ : ¬ A₀ ⊆ Δ₀) (h₁ : ¬ A₁ ⊆ Δ₁) :
    IsClosedDisc (Δ₀ ∪ Δ₁) ∧ discBd (Δ₀ ∪ Δ₁) = discBd Δ₂ ∧
      Δ₀ ∩ Δ₁ = A₂ ∧ Disjoint (A₀ \ {a, b}) Δ₀ ∧ Disjoint (A₁ \ {a, b}) Δ₁ := by
  have c₀ : IsClosed Δ₀ := d₀.isCompact.isClosed
  have c₁ : IsClosed Δ₁ := d₁.isCompact.isClosed
  have sub₀ : A₁ ∪ A₂ ⊆ Δ₀ := f₀ ▸ c₀.frontier_subset
  have sub₁ : A₂ ∪ A₀ ⊆ Δ₁ := f₁ ▸ c₁.frontier_subset
  have m₂ : ∀ x, x ∈ A₂ → x ∈ A₀ → x = a ∨ x = b := fun x h h' => by
    have : x ∈ A₂ ∩ A₀ := ⟨h, h'⟩
    rwa [i₂₀] at this
  have m₁ : ∀ x, x ∈ A₁ → x ∈ A₂ → x = a ∨ x = b := fun x h h' => by
    have : x ∈ A₁ ∩ A₂ := ⟨h, h'⟩
    rwa [i₁₂] at this
  have m₀ : ∀ x, x ∈ A₀ → x ∈ A₁ → x = a ∨ x = b := fun x h h' => by
    have : x ∈ A₀ ∩ A₁ := ⟨h, h'⟩
    rwa [i₀₁] at this
  have ha : a ∈ A₀ ∩ A₁ := by rw [i₀₁]; simp
  have hb : b ∈ A₀ ∩ A₁ := by rw [i₀₁]; simp
  have ha₂ : a ∈ A₁ ∩ A₂ := by rw [i₁₂]; simp
  have hb₂ : b ∈ A₁ ∩ A₂ := by rw [i₁₂]; simp
  have out₀ : Disjoint (A₀ \ {a, b}) Δ₀ := by
    have hdis : Disjoint (A₀ \ {a, b}) (frontier Δ₀) := by
      rw [f₀, disjoint_left]
      rintro x ⟨hx, hxn⟩ (h' | h')
      · exact hxn (m₀ x hx h')
      · exact hxn (m₂ x h' hx)
    refine (GM14.subset_or_disjoint_of_frontier c₀
      (GM14.IsLineWithEnds.isPreconnected_sdiff_pair l₀) hdis).resolve_left ?_
    intro hsub
    refine h₀ fun x hx => ?_
    by_cases hxab : x ∈ ({a, b} : Set S)
    · rcases hxab with rfl | rfl
      · exact sub₀ (Or.inl ha.2)
      · exact sub₀ (Or.inl hb.2)
    · exact hsub ⟨hx, hxab⟩
  have out₁ : Disjoint (A₁ \ {a, b}) Δ₁ := by
    have hdis : Disjoint (A₁ \ {a, b}) (frontier Δ₁) := by
      rw [f₁, disjoint_left]
      rintro x ⟨hx, hxn⟩ (h' | h')
      · exact hxn (m₁ x hx h')
      · exact hxn (m₀ x h' hx)
    refine (GM14.subset_or_disjoint_of_frontier c₁
      (GM14.IsLineWithEnds.isPreconnected_sdiff_pair l₁) hdis).resolve_left ?_
    intro hsub
    refine h₁ fun x hx => ?_
    by_cases hxab : x ∈ ({a, b} : Set S)
    · rcases hxab with rfl | rfl
      · exact sub₁ (Or.inl ha₂.2)
      · exact sub₁ (Or.inl hb₂.2)
    · exact hsub ⟨hx, hxab⟩
  have hint : Disjoint (Δ₁ \ frontier Δ₁) Δ₀ := by
    have hdis : Disjoint (Δ₁ \ frontier Δ₁) (frontier Δ₀) := by
      rw [f₀, disjoint_left]
      rintro x ⟨hxD, hxf⟩ (h' | h')
      · by_cases hxab : x ∈ ({a, b} : Set S)
        · apply hxf
          rw [f₁]
          rcases hxab with rfl | rfl
          · exact Or.inl ha₂.2
          · exact Or.inl hb₂.2
        · exact disjoint_left.mp out₁ ⟨h', hxab⟩ hxD
      · exact hxf (f₁ ▸ Or.inl h')
    refine (GM14.subset_or_disjoint_of_frontier c₀
      (GM14.IsClosedDisc.isPreconnected_diff_frontier hS d₁) hdis).resolve_left ?_
    intro hsub
    refine h₀ fun x hx => ?_
    have hxD : x ∈ Δ₁ := sub₁ (Or.inr hx)
    exact c₀.closure_subset_iff.mpr hsub
      (GM14.IsClosedDisc.subset_closure_diff_frontier hS d₁ hxD)
  have hcap : Δ₀ ∩ Δ₁ = A₂ := by
    apply subset_antisymm
    · rintro x ⟨hx₀, hx₁⟩
      have hxf : x ∈ frontier Δ₁ := by
        by_contra hn
        exact disjoint_left.mp hint ⟨hx₁, hn⟩ hx₀
      rw [f₁] at hxf
      rcases hxf with h' | h'
      · exact h'
      · by_cases hxab : x ∈ ({a, b} : Set S)
        · rcases hxab with rfl | rfl
          · exact ha₂.2
          · exact hb₂.2
        · exact absurd hx₀ (disjoint_left.mp out₀ ⟨h', hxab⟩)
    · exact fun x hx => ⟨sub₀ (Or.inr hx), sub₁ (Or.inl hx)⟩
  have e₀ := GM14.IsClosedDisc.frontier_eq_discBd hS d₀
  have e₁ := GM14.IsClosedDisc.frontier_eq_discBd hS d₁
  have e₂ := GM14.IsClosedDisc.frontier_eq_discBd hS d₂
  obtain ⟨dU, hU⟩ := disc_union Δ₀ Δ₁ A₂ a b d₀ d₁ l₂ hcap
    (by rw [← e₀, f₀]; exact subset_union_right) (by rw [← e₁, f₁]; exact subset_union_left)
  have hbd : discBd (Δ₀ ∪ Δ₁) = discBd Δ₂ := by
    rw [hU, ← e₀, ← e₁, ← e₂, f₀, f₁, f₂]
    ext x
    constructor
    · rintro ⟨(h' | h') | h' | h', hn⟩
      · exact Or.inr h'
      · have hab : x ∈ ({a, b} : Set S) := by
          by_contra hab
          exact hn ⟨h', hab⟩
        rcases hab with rfl | rfl
        · exact Or.inr ha.2
        · exact Or.inr hb.2
      · have hab : x ∈ ({a, b} : Set S) := by
          by_contra hab
          exact hn ⟨h', hab⟩
        rcases hab with rfl | rfl
        · exact Or.inr ha.2
        · exact Or.inr hb.2
      · exact Or.inl h'
    · rintro (h' | h')
      · refine ⟨Or.inr (Or.inr h'), fun hx => hx.2 (m₂ x hx.1 h')⟩
      · refine ⟨Or.inl (Or.inl h'), fun hx => hx.2 (m₁ x h' hx.1)⟩
  exact ⟨dU, hbd, hcap, out₀, out₁⟩

theorem discIns_mono {Δ_out : Set S} (hΔ_out : IsClosedDisc Δ_out) {C₁ C₂ : Drawing S}
    (hC₁ : C₁.IsCircuit) (hC₁_U : C₁.U ⊆ Δ_out)
    (hC₂ : C₂.IsCircuit) (hC₂_U : C₂.U ⊆ Δ_out)
    (hsub : C₁.U ⊆ GM14.discIns Δ_out C₂) :
    GM14.discIns Δ_out C₁ ⊆ GM14.discIns Δ_out C₂ := by
  obtain ⟨_, huniq₁⟩ := GM14.discIns_spec hΔ_out hC₁ hC₁_U
  obtain ⟨⟨h2, hdisc₂, _⟩, _⟩ := GM14.discIns_spec hΔ_out hC₂ hC₂_U
  obtain ⟨D, ⟨hD₂, dD, bD, -⟩, -⟩ :=
    disc_oArc (GM14.discIns Δ_out C₂) C₁.U hdisc₂ hsub (GM14.isOArc_of_isCircuit hC₁)
  have heq : D = GM14.discIns Δ_out C₁ := huniq₁ D (hD₂.trans h2) dD bD
  exact heq ▸ hD₂

omit [T2Space S] in
/-- **Move 1 (Boundary shortening move, GM03 (4.1) paragraph 2, page 60)**:
Replacing `P i` by a subdrawing `P'_i` of `P i` that omits an edge `e ∈ (P i).E` not belonging to
any `(C m).E` preserves pairwise vertex-disjointness and strictly decreases `totalDrawingEdges C P`.
-/
theorem totalDrawingEdges_lt_of_replace_subpath {s r : ℕ} [DecidableEq (Fin r)] {H : Drawing S}
    {C : Fin s → Drawing S} {P : Fin r → Drawing S}
    (hCH : ∀ m, (C m).IsSubdrawing H) (hPH : ∀ k, (P k).IsSubdrawing H)
    (hP_disj : Pairwise (fun k₁ k₂ => Disjoint (P k₁).V (P k₂).V))
    {i : Fin r} {P'_i : Drawing S} (hP'_sub : P'_i.IsSubdrawing (P i))
    {e : Set S} (he_Pi : e ∈ (P i).E) (he_not_P' : e ∉ P'_i.E)
    (he_not_C : ∀ m : Fin s, e ∉ (C m).E) :
    Pairwise (fun k₁ k₂ => Disjoint (Function.update P i P'_i k₁).V (Function.update P i P'_i
      k₂).V) ∧
      totalDrawingEdges C (Function.update P i P'_i) < totalDrawingEdges C P := by
  refine ⟨?_, ?_⟩
  · intro k₁ k₂ hk₁₂
    by_cases hk₁ : k₁ = i
    · subst hk₁
      rw [Function.update_self, Function.update_of_ne hk₁₂.symm]
      exact disjoint_of_subset_left hP'_sub.1 (hP_disj hk₁₂)
    · by_cases hk₂ : k₂ = i
      · subst hk₂
        rw [Function.update_of_ne hk₁, Function.update_self]
        exact disjoint_of_subset_right hP'_sub.1 (hP_disj hk₁₂)
      · rw [Function.update_of_ne hk₁, Function.update_of_ne hk₂]
        exact hP_disj hk₁₂
  · have hsub : totalDrawingEdgeSet C (Function.update P i P'_i) ⊆ totalDrawingEdgeSet C P := by
      rintro f (hfC | hfP)
      · exact Or.inl hfC
      · obtain ⟨k, hfk⟩ := mem_iUnion.mp hfP
        by_cases hki : k = i
        · subst hki
          rw [Function.update_self] at hfk
          exact Or.inr (mem_iUnion.mpr ⟨k, hP'_sub.2 hfk⟩)
        · rw [Function.update_of_ne hki] at hfk
          exact Or.inr (mem_iUnion.mpr ⟨k, hfk⟩)
    have he_in : e ∈ totalDrawingEdgeSet C P := Or.inr (mem_iUnion.mpr ⟨i, he_Pi⟩)
    have he_not_in : e ∉ totalDrawingEdgeSet C (Function.update P i P'_i) := by
      rintro (heC | heP)
      · obtain ⟨m, hem⟩ := mem_iUnion.mp heC
        exact he_not_C m hem
      · obtain ⟨k, hek⟩ := mem_iUnion.mp heP
        by_cases hki : k = i
        · subst hki
          rw [Function.update_self] at hek
          exact he_not_P' hek
        · rw [Function.update_of_ne hki] at hek
          have hdisjE := disjoint_E_of_disjoint_V (hPH i) (hPH k) (hP_disj (Ne.symm hki))
          exact disjoint_left.mp hdisjE he_Pi hek
    exact Set.ncard_lt_ncard ⟨hsub, fun h => he_not_in (h he_in)⟩
      (totalDrawingEdgeSet_finite hCH hPH)

/-- If `P` is a path in `H` from `a ∈ C.V` to `b` and `Drawing.inf H C P` is not a path, then there
is a subdrawing `P' ≤ P` which is a path from some `v ∈ C.V` to `b` and omits an edge `e ∈ P.E \
C.E`
incident with some `u ∈ C.V`. -/
theorem exists_shorter_subpath_of_not_isDrawingPath_inf {H C P : Drawing S}
    (hC : C.IsSubdrawing H) (hP : P.IsSubdrawing H)
    {a b : S} (hP_path : P.IsPathBetween a b) (ha : a ∈ C.V)
    (hnot : ¬ IsDrawingPath (Drawing.inf H C P)) :
    ∃ u ∈ C.V, ∃ v ∈ C.V, ∃ e ∈ P.E, e ∉ C.E ∧ (∃ w : S, H.toGraph.IsLink e u w) ∧
      ∃ P' : Drawing S, P'.IsSubdrawing P ∧ P'.IsPathBetween v b ∧ e ∉ P'.E := by
  have haP : a ∈ P.V := by
    obtain ⟨W₀, _, hVP, _⟩ := hP_path
    rw [hVP]; exact W₀.start_mem_support
  rcases path_inf_isPath_or_exists_detour hC hP hP_path ⟨a, ha, haP⟩ with
    hpath | ⟨u, ⟨huC, _⟩, v, ⟨hvC, _⟩, _, W₁, W_sub, W₂, hWs, hP_eq, _, hEC, e, he_sub, w, hl⟩
  · exact (hnot hpath).elim
  · have hsp1 := isSimple_of_append hWs
    have hsp2 := isSimple_of_append hsp1.2
    have hnd_E : (W₁.edges ++ (W_sub.edges ++ W₂.edges)).Nodup := by
      have h := hWs.edges_nodup
      rwa [GraphWalk.edges_append, GraphWalk.edges_append] at h
    have hd₁ := List.nodup_append.mp hnd_E
    have hd₂ := List.nodup_append.mp hd₁.2.1
    let P' := walkDrawing H W₂
    have hP'_sub : P'.IsSubdrawing P := by
      rw [hP_eq]
      refine ⟨fun x hx => ?_, fun f hf => ?_⟩
      · rw [walkDrawing_V, mem_ofPred_eq] at hx ⊢
        rw [GraphWalk.mem_support_append, GraphWalk.mem_support_append]
        exact Or.inr (Or.inr hx)
      · rw [walkDrawing_E, mem_ofPred_eq] at hf ⊢
        rw [GraphWalk.edges_append, GraphWalk.edges_append,
          List.mem_append, List.mem_append]
        exact Or.inr (Or.inr hf)
    have he_P : e ∈ P.E := by
      rw [walkDrawing_E, mem_ofPred_eq] at he_sub
      rw [hP_eq, walkDrawing_E, mem_ofPred_eq, GraphWalk.edges_append,
        GraphWalk.edges_append, List.mem_append, List.mem_append]
      exact Or.inr (Or.inl he_sub)
    have heC : e ∉ C.E := disjoint_left.mp hEC he_sub
    have he_not_P' : e ∉ P'.E := by
      rw [walkDrawing_E, mem_ofPred_eq] at he_sub ⊢
      exact fun he_W₂ => hd₂.2.2 e he_sub e he_W₂ rfl
    exact ⟨u, huC, v, hvC, e, he_P, heC, ⟨w, hl⟩, P', hP'_sub,
      walkDrawing_isPathBetween H hsp2.2, he_not_P'⟩

/-- A nested sequence `C : Fin s → Drawing S` of `s` pairwise vertex-disjoint circuits of `H` in a
closed disc `Δ_out`, indexed from inner (`C 0 = C_in`) to outer (`C (s - 1) = C_out`). -/
def IsDiscNest {s : ℕ} (H : Drawing S) (Δ_out : Set S) (C_in C_out : Drawing S)
    (C : Fin s → Drawing S) : Prop :=
  (∀ j : Fin s, (C j).IsSubdrawing H ∧ (C j).IsCircuit ∧ (C j).U ⊆ Δ_out) ∧
  Pairwise (fun j₁ j₂ : Fin s => Disjoint (C j₁).V (C j₂).V) ∧
  Monotone (fun j : Fin s => GM14.discIns Δ_out (C j)) ∧
  (∀ hs : 0 < s, C ⟨0, hs⟩ = C_in ∧ C ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ = C_out)

/-- A family `P : Fin r → Drawing S` of `r` pairwise vertex-disjoint paths of `H` in `Δ_out`, each
between `C_in.V` and `C_out.V`. -/
def IsDiscPaths {r : ℕ} (H : Drawing S) (Δ_out : Set S) (C_in C_out : Drawing S)
    (P : Fin r → Drawing S) : Prop :=
  (∀ i : Fin r, (P i).IsSubdrawing H ∧ (P i).U ⊆ Δ_out ∧
    ∃ a ∈ C_in.V, ∃ b ∈ C_out.V, (P i).IsPathBetween a b) ∧
  Pairwise (fun i₁ i₂ : Fin r => Disjoint (P i₁).V (P i₂).V)

theorem IsDiscNest.disc_props {s : ℕ} {H : Drawing S} {Δ_out : Set S} {C_in C_out : Drawing S}
    {C : Fin s → Drawing S} (hS : IsClosedSurface S) (hΔ_out : IsClosedDisc Δ_out)
    (hC : IsDiscNest H Δ_out C_in C_out C) (m : Fin s) :
    GM14.discIns Δ_out (C m) ⊆ Δ_out ∧
      IsClosedDisc (GM14.discIns Δ_out (C m)) ∧
      discBd (GM14.discIns Δ_out (C m)) = (C m).U ∧
      frontier (GM14.discIns Δ_out (C m)) = (C m).U ∧
      IsClosed (GM14.discIns Δ_out (C m)) ∧
      (C m).U ⊆ GM14.discIns Δ_out (C m) := by
  obtain ⟨⟨hsub, hdisc, hbd⟩, _⟩ := GM14.discIns_spec hΔ_out (hC.1 m).2.1 (hC.1 m).2.2
  have hfr : frontier (GM14.discIns Δ_out (C m)) = (C m).U :=
    (GM14.IsClosedDisc.frontier_eq_discBd hS hdisc).trans hbd
  have hcl : IsClosed (GM14.discIns Δ_out (C m)) := hdisc.isCompact.isClosed
  exact ⟨hsub, hdisc, hbd, hfr, hcl, hfr ▸ hcl.frontier_subset⟩

omit [T2Space S] in
theorem IsDiscNest.disjoint_U {s : ℕ} {H : Drawing S} {Δ_out : Set S} {C_in C_out : Drawing S}
    {C : Fin s → Drawing S} (hC : IsDiscNest H Δ_out C_in C_out C)
    {m₁ m₂ : Fin s} (hne : m₁ ≠ m₂) :
    Disjoint (C m₁).E (C m₂).E ∧ Disjoint (C m₁).U (C m₂).U := by
  have hE := disjoint_E_of_disjoint_V (hC.1 m₁).1 (hC.1 m₂).1 (hC.2.1 hne)
  refine ⟨hE, ?_⟩
  rw [Set.disjoint_iff_inter_eq_empty, GM14.U_inter_of_disjoint (hC.1 m₁).1 (hC.1 m₂).1 hE,
    ← Set.disjoint_iff_inter_eq_empty]
  exact hC.2.1 hne

theorem IsDiscNest.discIns_subset_diff {s : ℕ} {H : Drawing S} {Δ_out : Set S}
    {C_in C_out : Drawing S} {C : Fin s → Drawing S}
    (hS : IsClosedSurface S) (hΔ_out : IsClosedDisc Δ_out)
    (hC : IsDiscNest H Δ_out C_in C_out C) {m₁ m₂ : Fin s} (hlt : m₁ < m₂) :
    Disjoint (GM14.discIns Δ_out (C m₁)) (C m₂).U ∧
      GM14.discIns Δ_out (C m₁) ⊆ GM14.discIns Δ_out (C m₂) \ (C m₂).U := by
  have hp₁ := hC.disc_props hS hΔ_out m₁
  have hp₂ := hC.disc_props hS hΔ_out m₂
  have hsub : GM14.discIns Δ_out (C m₁) ⊆ GM14.discIns Δ_out (C m₂) := hC.2.2.1 hlt.le
  have hdisj_U := (hC.disjoint_U hlt.ne).2
  have hdisj : Disjoint (GM14.discIns Δ_out (C m₁)) (C m₂).U := by
    refine disjoint_left.mpr fun x hx₁ hx₂ => ?_
    have hx_fr₂ : x ∈ frontier (GM14.discIns Δ_out (C m₂)) := hp₂.2.2.2.1.symm ▸ hx₂
    have hx_fr₁ : x ∈ frontier (GM14.discIns Δ_out (C m₁)) :=
      frontier_inter_subset_frontier_of_subset hsub ⟨hx₁, hx_fr₂⟩
    rw [hp₁.2.2.2.1] at hx_fr₁
    exact disjoint_left.mp hdisj_U hx_fr₁ hx₂
  exact ⟨hdisj, fun x hx => ⟨hsub hx, disjoint_left.mp hdisj hx⟩⟩

theorem IsDiscNest.discIns_last_eq {s : ℕ} {H : Drawing S} {Δ_out : Set S}
    {C_in C_out : Drawing S} {C : Fin s → Drawing S} (hs : 0 < s)
    (hΔ_out : IsClosedDisc Δ_out) (hbd_out : discBd Δ_out = C_out.U)
    (hC : IsDiscNest H Δ_out C_in C_out C) :
    GM14.discIns Δ_out (C ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩) = Δ_out := by
  let m_last : Fin s := ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩
  obtain ⟨_, huniq⟩ := GM14.discIns_spec hΔ_out (hC.1 m_last).2.1 (hC.1 m_last).2.2
  refine (huniq Δ_out Subset.rfl hΔ_out ?_).symm
  rw [(hC.2.2.2 hs).2, hbd_out]

/-- **Move 1 step**: if `Drawing.inf H (C 0) (P i)` or `Drawing.inf H (C (s - 1)) (P i)` is not a
path, shortening `P i` produces a valid path family `P'` with strictly fewer total edges. -/
theorem move1_step {s r : ℕ} {H : Drawing S} {Δ_out : Set S}
    {C_in C_out : Drawing S} {C : Fin s → Drawing S} {P : Fin r → Drawing S}
    (hs : 0 < s) (hC : IsDiscNest H Δ_out C_in C_out C)
    (hP : IsDiscPaths H Δ_out C_in C_out P) {i : Fin r}
    (hnot : ¬ IsDrawingPath (Drawing.inf H (C ⟨0, hs⟩) (P i)) ∨
      ¬ IsDrawingPath (Drawing.inf H (C ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩) (P i))) :
    ∃ P' : Fin r → Drawing S,
      IsDiscPaths H Δ_out C_in C_out P' ∧ totalDrawingEdges C P' < totalDrawingEdges C P := by
  obtain ⟨hPi_H, hPi_U, a, ha, b, hb, hPi_path⟩ := hP.1 i
  obtain ⟨hC0_eq, hCs_eq⟩ := hC.2.2.2 hs
  rcases hnot with hnot0 | hnots
  · have ha0 : a ∈ (C ⟨0, hs⟩).V := hC0_eq.symm ▸ ha
    obtain ⟨u, huC, v, hvC, e, he_Pi, he_not_C0, ⟨w, hl⟩, P'_i, hP'_sub, hP'_path, he_not_P'⟩ :=
      exists_shorter_subpath_of_not_isDrawingPath_inf (hC.1 ⟨0, hs⟩).1 hPi_H hPi_path ha0 hnot0
    have he_not_C : ∀ m : Fin s, e ∉ (C m).E := by
      intro m hem
      by_cases hm0 : m = ⟨0, hs⟩
      · exact he_not_C0 (hm0 ▸ hem)
      · have hlm : (C m).toGraph.IsLink e u w := ((hC.1 m).1.isLink_iff hem).mpr hl
        exact disjoint_left.mp (hC.2.1 hm0) hlm.2.1 huC
    obtain ⟨hdisj', hlt⟩ :=
      totalDrawingEdges_lt_of_replace_subpath (fun m => (hC.1 m).1) (fun k => (hP.1 k).1)
        hP.2 hP'_sub he_Pi he_not_P' he_not_C
    refine ⟨Function.update P i P'_i, ⟨fun k => ?_, hdisj'⟩, hlt⟩
    by_cases hki : k = i
    · subst hki
      rw [Function.update_self]
      exact ⟨hP'_sub.trans hPi_H, hP'_sub.U_subset.trans hPi_U, v, hC0_eq ▸ hvC, b, hb, hP'_path⟩
    · rw [Function.update_of_ne hki]
      exact hP.1 k
  · let m_last : Fin s := ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩
    have hbs : b ∈ (C m_last).V := hCs_eq.symm ▸ hb
    obtain ⟨u, huC, v, hvC, e, he_Pi, he_not_Cs, ⟨w, hl⟩, P'_i, hP'_sub, hP'_path, he_not_P'⟩ :=
      exists_shorter_subpath_of_not_isDrawingPath_inf (hC.1 m_last).1 hPi_H
        (Drawing.IsPathBetween.symm hPi_path) hbs hnots
    have he_not_C : ∀ m : Fin s, e ∉ (C m).E := by
      intro m hem
      by_cases hms : m = m_last
      · exact he_not_Cs (hms ▸ hem)
      · have hlm : (C m).toGraph.IsLink e u w := ((hC.1 m).1.isLink_iff hem).mpr hl
        exact disjoint_left.mp (hC.2.1 hms) hlm.2.1 huC
    obtain ⟨hdisj', hlt⟩ :=
      totalDrawingEdges_lt_of_replace_subpath (fun m => (hC.1 m).1) (fun k => (hP.1 k).1)
        hP.2 hP'_sub he_Pi he_not_P' he_not_C
    refine ⟨Function.update P i P'_i, ⟨fun k => ?_, hdisj'⟩, hlt⟩
    by_cases hki : k = i
    · subst hki
      rw [Function.update_self]
      exact ⟨hP'_sub.trans hPi_H, hP'_sub.U_subset.trans hPi_U, a, ha, v, hCs_eq ▸ hvC,
        Drawing.IsPathBetween.symm hP'_path⟩
    · rw [Function.update_of_ne hki]
      exact hP.1 k

private theorem replace_nest_circuit_of_outer_detour
    {s r : ℕ} (hS : IsClosedSurface S) {H P_sub : Drawing S} {Δ_out : Set S}
    (hΔ_out : IsClosedDisc Δ_out) {C_in C_out : Drawing S}
    {C : Fin s → Drawing S} {P : Fin r → Drawing S}
    (hC : IsDiscNest H Δ_out C_in C_out C) (hP : IsDiscPaths H Δ_out C_in C_out P)
    {j : Fin s} (hj0 : 0 < j.1) (hj1 : j.1 + 1 < s) {i : Fin r} {v v' : S}
    (hvv' : v ≠ v') (hP_sub_Pi : P_sub.IsSubdrawing (P i))
    (hv_Pi : v ∈ (P i).V)
    (hP_sub_in_next : P_sub.U ⊆ GM14.discIns Δ_out (C ⟨j.1 + 1, hj1⟩))
    (hdisj_sub_other_C : ∀ m : Fin s, m ≠ j → Disjoint P_sub.V (C m).V) :
    ∀ (Q_k Q_other : Drawing S),
      Q_k.IsSubdrawing (C j) → Q_other.IsSubdrawing (C j) →
      Q_other.IsPathBetween v v' → Disjoint Q_k.E Q_other.E →
      (H.sup P_sub Q_k).IsCircuit → (H.sup P_sub Q_other).IsCircuit →
      GM14.discIns Δ_out (C j) ⊆ GM14.discIns Δ_out (H.sup P_sub Q_k) →
      IsDiscNest H Δ_out C_in C_out (Function.update C j (H.sup P_sub Q_k)) ∧
        (∀ m : Fin s, GM14.discIns Δ_out (C m) ⊆
          GM14.discIns Δ_out (Function.update C j (H.sup P_sub Q_k) m)) ∧
        totalDrawingEdges (Function.update C j (H.sup P_sub Q_k)) P < totalDrawingEdges C P := by
  let j_next : Fin s := ⟨j.1 + 1, hj1⟩
  have hj_lt_next : j < j_next := by change j.1 < j.1 + 1; omega
  have hp_j := hC.disc_props hS hΔ_out j
  have hp_next := hC.disc_props hS hΔ_out j_next
  have hP_sub_H := hP_sub_Pi.trans (hP.1 i).1
  intro Q_k Q_other hQk_s hQo_s hQo_path hQ_disjE hcirc_k hcirc_o hsub_j
  let C'_j := H.sup P_sub Q_k
  have hQk_H : Q_k.IsSubdrawing H := hQk_s.trans (hC.1 j).1
  have hQo_H : Q_other.IsSubdrawing H := hQo_s.trans (hC.1 j).1
  have hC'_H : C'_j.IsSubdrawing H := H.sup_isSubdrawing P_sub Q_k
  have hC'_U_next : C'_j.U ⊆ GM14.discIns Δ_out (C j_next) := by
    rw [Drawing.sup_U hP_sub_H hQk_H]
    refine union_subset hP_sub_in_next ?_
    exact hQk_s.U_subset.trans (hp_j.2.2.2.2.2.trans (hC.2.2.1 hj_lt_next.le))
  have hC'_U_out : C'_j.U ⊆ Δ_out := hC'_U_next.trans hp_next.1
  have hsub_next : GM14.discIns Δ_out C'_j ⊆ GM14.discIns Δ_out (C j_next) :=
    discIns_mono hΔ_out hcirc_k hC'_U_out (hC.1 j_next).2.1 (hC.1 j_next).2.2 hC'_U_next
  obtain ⟨e₀, he₀_Qo, he₀_not_P⟩ :=
    exists_edge_not_in_paths_of_theta (fun m => (hP.1 m).1)
      (fun m => by obtain ⟨a, _, b, _, hp⟩ := (hP.1 m).2.2; exact ⟨a, b, hp⟩)
      hP.2 hvv' hP_sub_Pi hQo_H hQo_path hv_Pi hcirc_o
  have hlt_edges :=
    totalDrawingEdges_lt_of_replace_circuit (fun m => (hC.1 m).1) (fun m => (hP.1 m).1)
      hC.2.1 hP_sub_Pi hQk_s hQo_s hQ_disjE he₀_Qo he₀_not_P
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, hlt_edges⟩
  · intro m
    by_cases hmj : m = j
    · subst hmj
      rw [Function.update_self]
      exact ⟨hC'_H, hcirc_k, hC'_U_out⟩
    · rw [Function.update_of_ne hmj]
      exact hC.1 m
  · intro m₁ m₂ hm₁₂
    by_cases hm₁ : m₁ = j
    · subst hm₁
      have hm₂ : m₂ ≠ m₁ := hm₁₂.symm
      rw [Function.update_self, Function.update_of_ne hm₂, H.sup_V hP_sub_H hQk_H]
      exact disjoint_union_left.mpr
        ⟨hdisj_sub_other_C m₂ hm₂, disjoint_of_subset_left hQk_s.1 (hC.2.1 hm₁₂)⟩
    · by_cases hm₂ : m₂ = j
      · subst hm₂
        rw [Function.update_of_ne hm₁, Function.update_self, H.sup_V hP_sub_H hQk_H]
        exact disjoint_union_right.mpr
          ⟨(hdisj_sub_other_C m₁ hm₁).symm, disjoint_of_subset_right hQk_s.1 (hC.2.1 hm₁₂)⟩
      · rw [Function.update_of_ne hm₁, Function.update_of_ne hm₂]
        exact hC.2.1 hm₁₂
  · intro m₁ m₂ hm₁₂
    dsimp only
    by_cases hm₁ : m₁ = j
    · subst hm₁
      rw [Function.update_self]
      by_cases hm₂ : m₂ = m₁
      · subst hm₂; rw [Function.update_self]
      · rw [Function.update_of_ne hm₂]
        have hnext_le_m₂ : j_next ≤ m₂ := by
          change m₁.1 + 1 ≤ m₂.1
          have : m₁ < m₂ := lt_of_le_of_ne hm₁₂ (Ne.symm hm₂)
          exact this
        exact hsub_next.trans (hC.2.2.1 hnext_le_m₂)
    · rw [Function.update_of_ne hm₁]
      by_cases hm₂ : m₂ = j
      · subst hm₂
        rw [Function.update_self]
        exact (hC.2.2.1 hm₁₂).trans hsub_j
      · rw [Function.update_of_ne hm₂]
        exact hC.2.2.1 hm₁₂
  · intro hs'
    have h0_ne_j : (⟨0, hs'⟩ : Fin s) ≠ j := fun h => by
      have := congrArg Fin.val h; dsimp at this; omega
    have hlast_ne_j : (⟨s - 1, Nat.sub_lt hs' zero_lt_one⟩ : Fin s) ≠ j := fun h => by
      have := congrArg Fin.val h; dsimp at this; omega
    rw [Function.update_of_ne h0_ne_j, Function.update_of_ne hlast_ne_j]
    exact hC.2.2.2 hs'
  · intro m
    by_cases hmj : m = j
    · subst hmj; rw [Function.update_self]; exact hsub_j
    · rw [Function.update_of_ne hmj]

/-- **Move 2 step (Outer detour replacement, GM03 (4.1) paragraph 4, page 60)**:
When `0 < j.1`, `j.1 + 1 < s`, `Drawing.inf H (C ⟨j.1 + 1, _⟩) (P i)` is a path, and `P i`
(oriented from `b_i ∈ C_out.V` to `a_i ∈ C_in.V`) has an outer detour `W_sub` on `C j`
(`¬ (walkDrawing H W_sub).U ⊆ discIns Δ_out (C j)`), replacing `C j` by one of `H.sup P_sub Q₁` or
`H.sup P_sub Q₂` preserves `IsDiscNest` and strictly decreases `totalDrawingEdges`. -/
theorem move2_outer_detour {s r : ℕ} (hS : IsClosedSurface S)
    {H : Drawing S} {Δ_out : Set S} (hΔ_out : IsClosedDisc Δ_out)
    {C_in C_out : Drawing S} (_hbd_out : discBd Δ_out = C_out.U)
    {C : Fin s → Drawing S} {P : Fin r → Drawing S}
    (hs : 0 < s) (hC : IsDiscNest H Δ_out C_in C_out C)
    (hP : IsDiscPaths H Δ_out C_in C_out P)
    {j : Fin s} (hj0 : 0 < j.1) (hj1 : j.1 + 1 < s) {i : Fin r}
    (hinf_next : IsDrawingPath (Drawing.inf H (C ⟨j.1 + 1, hj1⟩) (P i)))
    {a_i b_i v v' : S} (hb_i : b_i ∈ C_out.V)
    {W : GraphWalk H.toGraph b_i a_i} (hWs : W.IsSimple) (hPi_eq : P i = walkDrawing H W)
    (hvC : v ∈ (C j).V) (hv'C : v' ∈ (C j).V) (hvv' : v ≠ v')
    {W₁ : GraphWalk H.toGraph b_i v} {W_sub : GraphWalk H.toGraph v v'}
    {W₂ : GraphWalk H.toGraph v' a_i} (hW_eq : W = W₁.append (W_sub.append W₂))
    (hVC : (walkDrawing H W_sub).V ∩ (C j).V = {v, v'})
    (hEC : Disjoint (walkDrawing H W_sub).E (C j).E)
    (hnot_in : ¬ (walkDrawing H W_sub).U ⊆ GM14.discIns Δ_out (C j)) :
    ∃ C' : Fin s → Drawing S,
      IsDiscNest H Δ_out C_in C_out C' ∧
      (∀ m : Fin s, GM14.discIns Δ_out (C m) ⊆ GM14.discIns Δ_out (C' m)) ∧
      totalDrawingEdges C' P < totalDrawingEdges C P := by
  let j_prev : Fin s := ⟨j.1 - 1, by omega⟩
  let j_next : Fin s := ⟨j.1 + 1, hj1⟩
  let m_last : Fin s := ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩
  have hj_lt_next : j < j_next := by change j.1 < j.1 + 1; omega
  have hprev_lt_j : j_prev < j := by change j.1 - 1 < j.1; omega
  let P_sub := walkDrawing H W_sub
  have hsp1 := isSimple_of_append (hW_eq ▸ hWs)
  have hsp2 := isSimple_of_append hsp1.2
  have hP_sub_path : P_sub.IsPathBetween v v' := walkDrawing_isPathBetween H hsp2.1
  have hP_sub_Pi : P_sub.IsSubdrawing (P i) := by
    rw [hPi_eq, hW_eq]
    refine ⟨fun x hx => ?_, fun e he => ?_⟩
    · rw [walkDrawing_V, mem_ofPred_eq] at hx ⊢
      rw [GraphWalk.mem_support_append, GraphWalk.mem_support_append]
      exact Or.inr (Or.inl hx)
    · rw [walkDrawing_E, mem_ofPred_eq] at he ⊢
      rw [GraphWalk.edges_append, GraphWalk.edges_append, List.mem_append, List.mem_append]
      exact Or.inr (Or.inl he)
  have hP_sub_H : P_sub.IsSubdrawing H := walkDrawing_isSubdrawing H W_sub
  have hp_j := hC.disc_props hS hΔ_out j
  have hp_next := hC.disc_props hS hΔ_out j_next
  have hsub_j_next := (hC.discIns_subset_diff hS hΔ_out hj_lt_next).2
  have hv_in_next : v ∈ GM14.discIns Δ_out (C j_next) \ (C j_next).U :=
    hsub_j_next (hp_j.2.2.2.2.2 ((C j).V_subset_U hvC))
  have hmeet₁ : ((walkDrawing H W₁).U ∩ (C j_next).U).Nonempty := by
    have hb_W₁ : b_i ∈ (walkDrawing H W₁).U :=
      (walkDrawing H W₁).V_subset_U (by rw [walkDrawing_V]; exact W₁.start_mem_support)
    have hv_W₁ : v ∈ (walkDrawing H W₁).U :=
      (walkDrawing H W₁).V_subset_U (by rw [walkDrawing_V]; exact W₁.end_mem_support)
    have hb_last : b_i ∈ (C m_last).U := (hC.2.2.2 hs).2.symm ▸ C_out.V_subset_U hb_i
    by_cases hnext_last : j_next = m_last
    · exact ⟨b_i, hb_W₁, hnext_last.symm ▸ hb_last⟩
    · have hnext_lt_last : j_next < m_last :=
        lt_of_le_of_ne (by change j.1 + 1 ≤ s - 1; omega) hnext_last
      have hdisj_last := (hC.discIns_subset_diff hS hΔ_out hnext_lt_last).1
      have hb_not_next : b_i ∉ GM14.discIns Δ_out (C j_next) :=
        fun hb_in => disjoint_left.mp hdisj_last hb_in hb_last
      by_contra h_empty
      rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty,
        ← hp_next.2.2.2.1] at h_empty
      have hpre₁ := Drawing.IsPathBetween.isPreconnected_U (walkDrawing_isPathBetween H hsp1.1)
      rcases GM14.subset_or_disjoint_of_frontier hp_next.2.2.2.2.1 hpre₁ h_empty with hsub | hdis
      · exact hb_not_next (hsub hb_W₁)
      · exact disjoint_left.mp hdis hv_W₁ hv_in_next.1
  have hinf_next' :
      IsDrawingPath (Drawing.inf H (C j_next) (walkDrawing H (W₁.append (W_sub.append W₂)))) := by
    rwa [← hW_eq, ← hPi_eq]
  have hdisj_rest_next : Disjoint (walkDrawing H (W_sub.append W₂)).U (C j_next).U :=
    disjoint_tail_of_inf_isPath (hC.1 j_next).1 W₁ (W_sub.append W₂) (hW_eq ▸ hWs)
      hinf_next' hmeet₁ hv_in_next.2
  have hdisj_sub_next : Disjoint P_sub.U (C j_next).U := by
    refine disjoint_of_subset_left ?_ hdisj_rest_next
    rw [walkDrawing_append_U]
    exact subset_union_left
  have hP_sub_in_next : P_sub.U ⊆ GM14.discIns Δ_out (C j_next) \ (C j_next).U := by
    have hdis_fr : Disjoint P_sub.U (frontier (GM14.discIns Δ_out (C j_next))) := by
      rw [hp_next.2.2.2.1]
      exact hdisj_sub_next
    have hv_sub : v ∈ P_sub.U := P_sub.V_subset_U (by rw [walkDrawing_V]; exact
      W_sub.start_mem_support)
    rcases GM14.subset_or_disjoint_of_frontier hp_next.2.2.2.2.1
        (Drawing.IsPathBetween.isPreconnected_U hP_sub_path) hdis_fr with hsub | hdis
    · exact fun x hx => ⟨hsub hx, disjoint_left.mp hdisj_sub_next hx⟩
    · exact (disjoint_left.mp hdis hv_sub hv_in_next.1).elim
  have hP_sub_out_j : Disjoint (P_sub.U \ {v, v'}) (GM14.discIns Δ_out (C j)) := by
    have hU_inter_j : P_sub.U ∩ (C j).U = {v, v'} := by
      rw [GM14.U_inter_of_disjoint hP_sub_H (hC.1 j).1 hEC, hVC]
    have hdis_fr : Disjoint (P_sub.U \ {v, v'}) (frontier (GM14.discIns Δ_out (C j))) := by
      rw [hp_j.2.2.2.1, disjoint_left]
      intro x hx hxC
      have : x ∈ P_sub.U ∩ (C j).U := ⟨hx.1, hxC⟩
      rw [hU_inter_j] at this
      exact hx.2 this
    have hL_sub := GM14.isLine_of_isPathBetween hP_sub_path hvv'
    refine (GM14.subset_or_disjoint_of_frontier hp_j.2.2.2.2.1
      (GM14.IsLineWithEnds.isPreconnected_sdiff_pair hL_sub) hdis_fr).resolve_left ?_
    intro hsub
    refine hnot_in fun x hx => ?_
    by_cases hxvv' : x ∈ ({v, v'} : Set S)
    · rcases hxvv' with rfl | rfl
      · exact hp_j.2.2.2.2.2 ((C j).V_subset_U hvC)
      · exact hp_j.2.2.2.2.2 ((C j).V_subset_U hv'C)
    · exact hsub ⟨hx, hxvv'⟩
  have hdisj_sub_other_C : ∀ m : Fin s, m ≠ j → Disjoint P_sub.V (C m).V := by
    intro m hmj
    rcases lt_or_gt_of_ne hmj with hlt | hgt
    · have hm_in_j := (hC.discIns_subset_diff hS hΔ_out hlt).2
      have hp_m := hC.disc_props hS hΔ_out m
      refine disjoint_left.mpr fun x hx_sub hx_m => ?_
      have hx_in_j : x ∈ GM14.discIns Δ_out (C j) \ (C j).U :=
        hm_in_j (hp_m.2.2.2.2.2 ((C m).V_subset_U hx_m))
      have hx_not_vv' : x ∉ ({v, v'} : Set S) := by
        rintro (rfl | rfl)
        · exact hx_in_j.2 ((C j).V_subset_U hvC)
        · exact hx_in_j.2 ((C j).V_subset_U hv'C)
      exact disjoint_left.mp hP_sub_out_j ⟨P_sub.V_subset_U hx_sub, hx_not_vv'⟩ hx_in_j.1
    · have hnext_le_m : j_next ≤ m := by change j.1 + 1 ≤ m.1; exact hgt
      refine disjoint_left.mpr fun x hx_sub hx_m => ?_
      have hx_next := hP_sub_in_next (P_sub.V_subset_U hx_sub)
      have hx_mU : x ∈ (C m).U := (C m).V_subset_U hx_m
      by_cases hnext_m : j_next = m
      · exact hx_next.2 (hnext_m ▸ hx_mU)
      · have hnext_lt_m : j_next < m := lt_of_le_of_ne hnext_le_m hnext_m
        exact disjoint_left.mp (hC.discIns_subset_diff hS hΔ_out hnext_lt_m).1 hx_next.1 hx_mU
  obtain ⟨Q₁, Q₂, hQ₁_path, hQ₂_path, hQ₁s, hQ₂s, _, _, hQ_V, hQ_E, hQ_sup⟩ :=
    (hC.1 j).2.1.exists_two_paths hvC hv'C hvv'
  have hQ₁_H : Q₁.IsSubdrawing H := hQ₁s.trans (hC.1 j).1
  have hQ₂_H : Q₂.IsSubdrawing H := hQ₂s.trans (hC.1 j).1
  have hCj_U_eq : (C j).U = Q₁.U ∪ Q₂.U := by
    rw [← hQ_sup, Drawing.sup_U hQ₁s hQ₂s]
  have hV_20 : Q₂.V ∩ P_sub.V = {v, v'} := by
    apply subset_antisymm
    · intro x ⟨hx₂, hx₀⟩
      have : x ∈ P_sub.V ∩ (C j).V := ⟨hx₀, hQ₂s.1 hx₂⟩
      rwa [hVC] at this
    · rintro x (rfl | rfl)
      · exact ⟨by obtain ⟨W₀, _, hV₀, _⟩ := hQ₂_path; rw [hV₀]; exact W₀.start_mem_support,
          by rw [walkDrawing_V]; exact W_sub.start_mem_support⟩
      · exact ⟨by obtain ⟨W₀, _, hV₀, _⟩ := hQ₂_path; rw [hV₀]; exact W₀.end_mem_support,
          by rw [walkDrawing_V]; exact W_sub.end_mem_support⟩
  have hV_01 : P_sub.V ∩ Q₁.V = {v, v'} := by
    apply subset_antisymm
    · intro x ⟨hx₀, hx₁⟩
      have : x ∈ P_sub.V ∩ (C j).V := ⟨hx₀, hQ₁s.1 hx₁⟩
      rwa [hVC] at this
    · rintro x (rfl | rfl)
      · exact ⟨by rw [walkDrawing_V]; exact W_sub.start_mem_support,
          by obtain ⟨W₀, _, hV₀, _⟩ := hQ₁_path; rw [hV₀]; exact W₀.start_mem_support⟩
      · exact ⟨by rw [walkDrawing_V]; exact W_sub.end_mem_support,
          by obtain ⟨W₀, _, hV₀, _⟩ := hQ₁_path; rw [hV₀]; exact W₀.end_mem_support⟩
  have hE_20 : Disjoint Q₂.E P_sub.E := disjoint_of_subset_left hQ₂s.2 hEC.symm
  have hE_01 : Disjoint P_sub.E Q₁.E := disjoint_of_subset_right hQ₁s.2 hEC
  have hv_Pi : v ∈ (P i).V := hP_sub_Pi.1 (by rw [walkDrawing_V]; exact W_sub.start_mem_support)
  have hcirc₁ : (H.sup P_sub Q₁).IsCircuit :=
    Drawing.isCircuit_sup hP_sub_path hQ₁_path hP_sub_H hQ₁_H hvv' hV_01 hE_01
  have hcirc₂ : (H.sup P_sub Q₂).IsCircuit :=
    Drawing.isCircuit_sup hP_sub_path hQ₂_path hP_sub_H hQ₂_H hvv'
      (by rw [inter_comm, hV_20]) hE_20.symm
  have hU₁_out : (H.sup P_sub Q₁).U ⊆ Δ_out := by
    rw [Drawing.sup_U hP_sub_H hQ₁_H]
    exact union_subset (hP_sub_Pi.U_subset.trans (hP.1 i).2.1) (hQ₁s.U_subset.trans (hC.1 j).2.2)
  have hU₂_out : (H.sup P_sub Q₂).U ⊆ Δ_out := by
    rw [Drawing.sup_U hP_sub_H hQ₂_H]
    exact union_subset (hP_sub_Pi.U_subset.trans (hP.1 i).2.1) (hQ₂s.U_subset.trans (hC.1 j).2.2)
  have hreplace := replace_nest_circuit_of_outer_detour
    hS hΔ_out hC hP hj0 hj1 hvv' hP_sub_Pi hv_Pi
    (hP_sub_in_next.trans sdiff_subset) hdisj_sub_other_C
  obtain ⟨⟨sub_c₂, d_c₂, b_c₂⟩, _⟩ := GM14.discIns_spec hΔ_out hcirc₂ hU₂_out
  obtain ⟨⟨sub_c₁, d_c₁, b_c₁⟩, uniq_c₁⟩ := GM14.discIns_spec hΔ_out hcirc₁ hU₁_out
  have f_c₂ : frontier (GM14.discIns Δ_out (H.sup P_sub Q₂)) = Q₂.U ∪ P_sub.U := by
    rw [GM14.IsClosedDisc.frontier_eq_discBd hS d_c₂, b_c₂, Drawing.sup_U hP_sub_H hQ₂_H,
      union_comm]
  have f_c₁ : frontier (GM14.discIns Δ_out (H.sup P_sub Q₁)) = P_sub.U ∪ Q₁.U := by
    rw [GM14.IsClosedDisc.frontier_eq_discBd hS d_c₁, b_c₁, Drawing.sup_U hP_sub_H hQ₁_H]
  by_cases h₁ : Q₁.U ⊆ GM14.discIns Δ_out (H.sup P_sub Q₂)
  · have hCj_sub : (C j).U ⊆ GM14.discIns Δ_out (H.sup P_sub Q₂) := by
      rw [hCj_U_eq]
      refine union_subset h₁ ?_
      have hbd_sub : Q₂.U ∪ P_sub.U ⊆ GM14.discIns Δ_out (H.sup P_sub Q₂) :=
        f_c₂ ▸ d_c₂.isCompact.isClosed.frontier_subset
      exact subset_union_left.trans hbd_sub
    have hsub_j := discIns_mono hΔ_out (hC.1 j).2.1 (hC.1 j).2.2 hcirc₂ hU₂_out hCj_sub
    exact ⟨Function.update C j (H.sup P_sub Q₂),
      hreplace Q₂ Q₁ hQ₂s hQ₁s hQ₁_path hQ_E.symm hcirc₂ hcirc₁ hsub_j⟩
  by_cases h₂ : Q₂.U ⊆ GM14.discIns Δ_out (H.sup P_sub Q₁)
  · have hCj_sub : (C j).U ⊆ GM14.discIns Δ_out (H.sup P_sub Q₁) := by
      rw [hCj_U_eq]
      refine union_subset ?_ h₂
      have hbd_sub : P_sub.U ∪ Q₁.U ⊆ GM14.discIns Δ_out (H.sup P_sub Q₁) :=
        f_c₁ ▸ d_c₁.isCompact.isClosed.frontier_subset
      exact subset_union_right.trans hbd_sub
    have hsub_j := discIns_mono hΔ_out (hC.1 j).2.1 (hC.1 j).2.2 hcirc₁ hU₁_out hCj_sub
    exact ⟨Function.update C j (H.sup P_sub Q₁),
      hreplace Q₁ Q₂ hQ₁s hQ₂s hQ₂_path hQ_E hcirc₁ hcirc₂ hsub_j⟩
  exfalso
  obtain ⟨dU, hbdU, hneU⟩ :=
    GM14.theta_disc_union hS
      (GM14.isLine_of_isPathBetween hP_sub_path hvv')
      (GM14.isLine_of_isPathBetween hQ₁_path hvv')
      (GM14.isLine_of_isPathBetween hQ₂_path hvv')
      (by rw [GM14.U_inter_of_disjoint hP_sub_H hQ₁_H hE_01, hV_01])
      (by rw [GM14.U_inter_of_disjoint hQ₁_H hQ₂_H hQ_E, hQ_V])
      (by rw [GM14.U_inter_of_disjoint hQ₂_H hP_sub_H hE_20, hV_20])
      hp_j.2.1 d_c₂ d_c₁
      (hp_j.2.2.2.1.trans hCj_U_eq) f_c₂ f_c₁
      hnot_in h₁ h₂
  have heq := uniq_c₁ _ (union_subset hp_j.1 sub_c₂) dU (hbdU.trans b_c₁)
  exact hneU heq

/-- Property `(2)` of Graph Minors III, (4.1) (page 60):
When `0 < j.1`, `j.1 + 1 < s`, and `Drawing.inf H (C ⟨j.1 + 1, _⟩) (P i')` is a path for every `i'`,
either Move 2 applies to some `P i'` (strictly decreasing `totalDrawingEdges`), or for every
`i' : Fin r` and every `u ∈ (C j).V ∩ (P i').V`, there is a subdrawing `R ≤ P i'` which is a path
from `u` to some `a' ∈ C_in.V` with `R.U ⊆ discIns Δ_out (C j)`. -/
theorem exists_inner_subpath_or_outer_detour {s r : ℕ}
    (hS : IsClosedSurface S) {H : Drawing S} {Δ_out : Set S} (hΔ_out : IsClosedDisc Δ_out)
    {C_in C_out : Drawing S} (hbd_out : discBd Δ_out = C_out.U)
    {C : Fin s → Drawing S} {P : Fin r → Drawing S}
    (hs : 0 < s) (hC : IsDiscNest H Δ_out C_in C_out C)
    (hP : IsDiscPaths H Δ_out C_in C_out P)
    {j : Fin s} (hj0 : 0 < j.1) (hj1 : j.1 + 1 < s)
    (hinf_next : ∀ i' : Fin r, IsDrawingPath (Drawing.inf H (C ⟨j.1 + 1, hj1⟩) (P i'))) :
    (∃ C' : Fin s → Drawing S,
      IsDiscNest H Δ_out C_in C_out C' ∧
      (∀ m : Fin s, GM14.discIns Δ_out (C m) ⊆ GM14.discIns Δ_out (C' m)) ∧
      totalDrawingEdges C' P < totalDrawingEdges C P) ∨
    (∀ (i' : Fin r) (u : S), u ∈ (C j).V ∩ (P i').V →
      ∃ a' ∈ C_in.V, ∃ R : Drawing S,
        R.IsSubdrawing (P i') ∧ R.IsPathBetween u a' ∧ R.U ⊆ GM14.discIns Δ_out (C j)) := by
  by_contra hnot
  push Not at hnot
  obtain ⟨hno_C', i', u, ⟨huC, huP⟩, hno_R⟩ := hnot
  obtain ⟨hPi'_H, _, a', ha', b', hb', hPi'_path⟩ := hP.1 i'
  have hPi'_symm : (P i').IsPathBetween b' a' := Drawing.IsPathBetween.symm hPi'_path
  obtain ⟨W₀, hW₀s, hVP, hEP⟩ := hPi'_symm
  obtain ⟨W, hsW, heW⟩ := hPi'_H.exists_walk_up W₀
  have hWs : W.IsSimple := by change W.support.Nodup; rw [hsW]; exact hW₀s
  have hPi'_eq : P i' = walkDrawing H W := by
    apply Drawing.ext_of_V_E
    · rw [hVP, walkDrawing_V, hsW]
    · rw [hEP, walkDrawing_E, heW]
  have hu_supp : u ∈ W.support := by
    rw [hVP, mem_ofPred_eq, ← hsW] at huP
    exact huP
  obtain ⟨W_pre, W_suf, hW_split⟩ := W.exists_append_of_mem hu_supp
  have hsp := isSimple_of_append (hW_split ▸ hWs)
  have hp_j := hC.disc_props hS hΔ_out j
  have h0_lt_j : (⟨0, hs⟩ : Fin s) < j := hj0
  have hp_0 := hC.disc_props hS hΔ_out ⟨0, hs⟩
  have ha'_0 : a' ∈ (C ⟨0, hs⟩).U := (hC.2.2.2 hs).1.symm ▸ C_in.V_subset_U ha'
  have ha'_in_j : a' ∈ GM14.discIns Δ_out (C j) \ (C j).U :=
    (hC.discIns_subset_diff hS hΔ_out h0_lt_j).2 (hp_0.2.2.2.2.2 ha'_0)
  rcases walk_subset_disc_or_exists_outer_detour (hC.1 j).1 hp_j.2.2.2.2.1 hp_j.2.2.2.1
      W_suf hsp.2 huC ha'_in_j with hsub_in |
    ⟨v, hvC, v', hv'C, hvv', W_pre', W_sub, W_post, hWsuf_eq, hVC, hEC, hnot_in⟩
  · let R := walkDrawing H W_suf
    have hR_sub : R.IsSubdrawing (P i') := by
      rw [hPi'_eq, hW_split]
      refine ⟨fun x hx => ?_, fun e he => ?_⟩
      · rw [walkDrawing_V, mem_ofPred_eq] at hx ⊢
        rw [GraphWalk.mem_support_append]
        exact Or.inr hx
      · rw [walkDrawing_E, mem_ofPred_eq] at he ⊢
        rw [GraphWalk.edges_append, List.mem_append]
        exact Or.inr he
    exact hno_R a' ha' R hR_sub (walkDrawing_isPathBetween H hsp.2) hsub_in
  · have hW_eq : W = (W_pre.append W_pre').append (W_sub.append W_post) := by
      rw [GraphWalk.append_assoc, ← hWsuf_eq, ← hW_split]
    obtain ⟨C', hC', hmono, hlt⟩ :=
      move2_outer_detour hS hΔ_out hbd_out hs hC hP hj0 hj1 (hinf_next i') hb' hWs hPi'_eq
        hvC hv'C hvv' hW_eq hVC hEC hnot_in
    exact not_lt_of_ge (hno_C' C' hC' hmono) hlt

theorem walkDrawing_reverse (H : Drawing S) {a b : S} (W : GraphWalk H.toGraph a b) :
    walkDrawing H W.reverse = walkDrawing H W := by
  apply Drawing.ext_of_V_E
  · rw [walkDrawing_V, walkDrawing_V]; ext x; simp [GraphWalk.support_reverse]
  · rw [walkDrawing_E, walkDrawing_E]; ext e; simp [GraphWalk.edges_reverse]

private theorem walk_append_nil {α β : Type*} {G : Graph α β} {u v : α}
    (W : GraphWalk G u v) (hv : v ∈ V(G)) : W.append (.nil hv) = W := by
  induction W with
  | nil _ => rfl
  | cons h r ih => exact congrArg (GraphWalk.cons h) (ih hv)

private theorem walk_append_assoc {α β : Type*} {G : Graph α β} {u v w z : α}
    (W₁ : GraphWalk G u v) (W₂ : GraphWalk G v w) (W₃ : GraphWalk G w z) :
    (W₁.append W₂).append W₃ = W₁.append (W₂.append W₃) := by
  induction W₁ with
  | nil _ => rfl
  | cons h r ih => exact congrArg (GraphWalk.cons h) (ih W₂)

private theorem walk_reverse_append {α β : Type*} {G : Graph α β} {u v w : α}
    (W₁ : GraphWalk G u v) (W₂ : GraphWalk G v w) :
    (W₁.append W₂).reverse = W₂.reverse.append W₁.reverse := by
  induction W₁ with
  | nil hv => exact (walk_append_nil W₂.reverse hv).symm
  | cons h r ih =>
    change (r.append W₂).reverse.append (.cons h.symm (.nil h.left_mem)) =
      W₂.reverse.append (r.reverse.append (.cons h.symm (.nil h.left_mem)))
    rw [ih, walk_append_assoc]

private theorem not_arc_subset_chord_discIns (hS : IsClosedSurface S)
    {H C Q₁ Q₂ P_sub : Drawing S} {Δ_out : Set S} (hΔ_out : IsClosedDisc Δ_out)
    {v v' : S} (hvv' : v ≠ v')
    (hCH : C.IsSubdrawing H) (hC : C.IsCircuit) (hCU : C.U ⊆ Δ_out)
    (hQ₂_H : Q₂.IsSubdrawing H)
    (hCj_U : C.U = Q₁.U ∪ Q₂.U)
    (hP_sub_H : P_sub.IsSubdrawing H) (hP_sub_path : P_sub.IsPathBetween v v')
    (hVC : P_sub.V ∩ C.V = {v, v'}) (hEC : Disjoint P_sub.E C.E)
    (hcirc₂ : (H.sup P_sub Q₂).IsCircuit)
    (hU₂_in : (H.sup P_sub Q₂).U ⊆ GM14.discIns Δ_out C) :
    ¬ Q₁.U ⊆ GM14.discIns Δ_out (H.sup P_sub Q₂) := by
  intro hQ₁_in
  obtain ⟨⟨hD₀_out, hD₀_disc, hD₀_bd⟩, _⟩ := GM14.discIns_spec hΔ_out hC hCU
  have hU₂_out : (H.sup P_sub Q₂).U ⊆ Δ_out := hU₂_in.trans hD₀_out
  obtain ⟨⟨_, hD₁_disc, hD₁_bd⟩, _⟩ := GM14.discIns_spec hΔ_out hcirc₂ hU₂_out
  have hf₀ : frontier (GM14.discIns Δ_out C) = C.U :=
    (GM14.IsClosedDisc.frontier_eq_discBd hS hD₀_disc).trans hD₀_bd
  have hf₁ : frontier (GM14.discIns Δ_out (H.sup P_sub Q₂)) = P_sub.U ∪ Q₂.U := by
    rw [GM14.IsClosedDisc.frontier_eq_discBd hS hD₁_disc, hD₁_bd, Drawing.sup_U hP_sub_H hQ₂_H]
  have hQ₂_in : Q₂.U ⊆ GM14.discIns Δ_out (H.sup P_sub Q₂) :=
    subset_union_right.trans (hf₁ ▸ hD₁_disc.isCompact.isClosed.frontier_subset)
  have hCU_in : C.U ⊆ GM14.discIns Δ_out (H.sup P_sub Q₂) :=
    hCj_U ▸ union_subset hQ₁_in hQ₂_in
  have hD₀_le_D₁ := discIns_mono hΔ_out hC hCU hcirc₂ hU₂_out hCU_in
  have hD₁_le_D₀ := discIns_mono hΔ_out hcirc₂ hU₂_out hC hCU hU₂_in
  have hD_eq : GM14.discIns Δ_out (H.sup P_sub Q₂) = GM14.discIns Δ_out C :=
    Subset.antisymm hD₁_le_D₀ hD₀_le_D₁
  have hP_sub_CU : P_sub.U ⊆ C.U := by
    have : P_sub.U ⊆ frontier (GM14.discIns Δ_out (H.sup P_sub Q₂)) :=
      hf₁.symm ▸ subset_union_left
    rwa [hD_eq, hf₀] at this
  have hU_inter : P_sub.U ∩ C.U = {v, v'} := by
    rw [GM14.U_inter_of_disjoint hP_sub_H hCH hEC, hVC]
  obtain ⟨φ, hφ0, hφ1⟩ := GM14.isLine_of_isPathBetween hP_sub_path hvv'
  let t_mid : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have hx_in : (φ t_mid).1 ∈ P_sub.U ∩ C.U := ⟨(φ t_mid).2, hP_sub_CU (φ t_mid).2⟩
  rw [hU_inter] at hx_in
  rcases hx_in with h_eq | h_eq
  · have ht : t_mid = 0 := φ.injective (Subtype.ext (h_eq.trans hφ0.symm))
    exact absurd (congrArg Subtype.val ht) (by norm_num [t_mid])
  · have ht : t_mid = 1 := φ.injective (Subtype.ext (h_eq.trans hφ1.symm))
    exact absurd (congrArg Subtype.val ht) (by norm_num [t_mid])

private theorem reroute_path_across_inner_detour {s r : ℕ}
    {H : Drawing S} {Δ_out : Set S} {C_in C_out : Drawing S}
    {C : Fin s → Drawing S} {P : Fin r → Drawing S}
    (hC : IsDiscNest H Δ_out C_in C_out C) (hP : IsDiscPaths H Δ_out C_in C_out P)
    {j : Fin s} {i : Fin r} {a_i b_i v v' w₁ : S} {e₁ : Set S}
    (ha_i : a_i ∈ C_in.V) (hb_i : b_i ∈ C_out.V)
    (hvC : v ∈ (C j).V) (hvP : v ∈ (P i).V) (hv'P : v' ∈ (P i).V)
    {W₁ : GraphWalk H.toGraph a_i v} {W_sub : GraphWalk H.toGraph v v'}
    {W₂ : GraphWalk H.toGraph v' b_i}
    (hWs : (W₁.append (W_sub.append W₂)).IsSimple)
    (hPi_eq : P i = walkDrawing H (W₁.append (W_sub.append W₂)))
    (hP_sub_Pi : (walkDrawing H W_sub).IsSubdrawing (P i))
    (hEC : Disjoint (walkDrawing H W_sub).E (C j).E)
    (he₁_sub : e₁ ∈ (walkDrawing H W_sub).E) (hl₁ : H.toGraph.IsLink e₁ v w₁)
    (hno_outer : ∀ i' : Fin r, ∀ u ∈ (C j).V ∩ (P i').V,
      ∃ a' ∈ C_in.V, ∃ R : Drawing S,
        R.IsSubdrawing (P i') ∧ R.IsPathBetween u a' ∧ R.U ⊆ GM14.discIns Δ_out (C j)) :
    let P_sub := walkDrawing H W_sub
    let D₀ := GM14.discIns Δ_out (C j)
    ∀ (Q_k : Drawing S) (D_in D_other : Set S),
        Q_k.IsSubdrawing (C j) → Q_k.IsPathBetween v v' →
        IsClosed D_in → IsClosed D_other → D_in ∪ D_other = D₀ → D_in ∩ D_other = P_sub.U →
        C_in.U ⊆ D_in → Disjoint (Q_k.U \ {v, v'}) D_in →
        ∃ P' : Fin r → Drawing S,
          IsDiscPaths H Δ_out C_in C_out P' ∧ totalDrawingEdges C P' < totalDrawingEdges C P := by
  intro P_sub D₀
  have hPi_H := (hP.1 i).1
  have hPi_U := (hP.1 i).2.1
  intro Q_k D_in D_other hQk_s hQk_path hcl_in hcl_other hU_D hI_D hCin_in hout_Qk
  have hQk_H : Q_k.IsSubdrawing H := hQk_s.trans (hC.1 j).1
  have hQk_disj_other : ∀ i' : Fin r, i' ≠ i → Disjoint Q_k.V (P i').V := by
    intro i' hi'
    refine disjoint_left.mpr fun u hu_Qk hu_Pi' => ?_
    obtain ⟨a', ha', R, hR_sub, hR_path, hR_D₀⟩ :=
      hno_outer i' u ⟨hQk_s.1 hu_Qk, hu_Pi'⟩
    have hR_H : R.IsSubdrawing H := hR_sub.trans (hP.1 i').1
    have hdisj_Pi'_Pi : Disjoint (P i').U (P i).U := by
      have hE_disj := disjoint_E_of_disjoint_V (hP.1 i').1 hPi_H (hP.2 hi')
      rw [Set.disjoint_iff_inter_eq_empty,
        GM14.U_inter_of_disjoint (hP.1 i').1 hPi_H hE_disj, ← Set.disjoint_iff_inter_eq_empty]
      exact hP.2 hi'
    have hdisj_R_sub : Disjoint R.U P_sub.U :=
      disjoint_of_subset hR_sub.U_subset hP_sub_Pi.U_subset hdisj_Pi'_Pi
    have hR_union : R.U ⊆ D_in ∪ D_other := hU_D.symm ▸ hR_D₀
    have ha'_R : a' ∈ R.U := R.V_subset_U
      (by obtain ⟨W₀, _, hV₀, _⟩ := hR_path; rw [hV₀]; exact W₀.end_mem_support)
    have hu_R : u ∈ R.U := R.V_subset_U
      (by obtain ⟨W₀, _, hV₀, _⟩ := hR_path; rw [hV₀]; exact W₀.start_mem_support)
    have ha'_Din : a' ∈ D_in := hCin_in (C_in.V_subset_U ha')
    have hu_Din : u ∈ D_in := by
      by_contra hu_not_in
      have hu_other : u ∈ D_other := (hR_union hu_R).resolve_left hu_not_in
      obtain ⟨z, hz_R, hz_in, hz_other⟩ :=
        isPreconnected_closed_iff.mp (Drawing.IsPathBetween.isPreconnected_U hR_path)
          D_in D_other hcl_in hcl_other hR_union ⟨a', ha'_R, ha'_Din⟩ ⟨u, hu_R, hu_other⟩
      have hz_P : z ∈ P_sub.U := by rw [← hI_D]; exact ⟨hz_in, hz_other⟩
      exact disjoint_left.mp hdisj_R_sub hz_R hz_P
    have hu_not_vv' : u ∉ ({v, v'} : Set S) := by
      rintro (rfl | rfl)
      · exact disjoint_left.mp (hP.2 hi') hu_Pi' hvP
      · exact disjoint_left.mp (hP.2 hi') hu_Pi' hv'P
    exact disjoint_left.mp hout_Qk ⟨Q_k.V_subset_U hu_Qk, hu_not_vv'⟩ hu_Din
  obtain ⟨P'_i, hP'_H, hP'_path, hP'_V, hP'_E⟩ :=
    reroute_drawing_path hWs hPi_eq hQk_H hQk_path
  have he₁_not_C : ∀ m : Fin s, e₁ ∉ (C m).E := by
    intro m hem
    by_cases hmj : m = j
    · exact disjoint_left.mp hEC he₁_sub (hmj ▸ hem)
    · have hlm : (C m).toGraph.IsLink e₁ v w₁ := ((hC.1 m).1.isLink_iff hem).mpr hl₁
      exact disjoint_left.mp (hC.2.1 hmj) hlm.2.1 hvC
  obtain ⟨hdisj_P', hlt_edges⟩ :=
    totalDrawingEdges_lt_of_reroute_path (fun m => (hC.1 m).1) (fun m => (hP.1 m).1)
      hP.2 hP_sub_Pi hQk_s hP'_V hP'_E hQk_disj_other he₁_sub he₁_not_C
  have hP'_U : P'_i.U ⊆ Δ_out := by
    intro x hx
    rw [P'_i.U_eq, mem_union, mem_iUnion₂] at hx
    rcases hx with hxV | ⟨e, he, hxe⟩
    · rcases hP'_V hxV with hx_Pi | hx_Qk
      · exact hPi_U ((P i).V_subset_U hx_Pi)
      · exact (hC.1 j).2.2 ((C j).V_subset_U (hQk_s.1 hx_Qk))
    · rcases hP'_E he with ⟨he_Pi, _⟩ | he_Qk
      · exact hPi_U ((P i).closure_subset_U he_Pi hxe)
      · exact (hC.1 j).2.2 ((C j).closure_subset_U (hQk_s.2 he_Qk) hxe)
  refine ⟨Function.update P i P'_i, ⟨fun k => ?_, hdisj_P'⟩, hlt_edges⟩
  by_cases hki : k = i
  · subst hki
    rw [Function.update_self]
    exact ⟨hP'_H, hP'_U, a_i, ha_i, b_i, hb_i, hP'_path⟩
  · rw [Function.update_of_ne hki]
    exact hP.1 k

/-- **Combined Move 2 / Move 3 step (GM03 (4.1) paragraphs 4–6, pages 60–61)**:
When `0 < j.1`, `j.1 + 1 < s`, `Drawing.inf H (C 0) (P i')` and `Drawing.inf H (C ⟨j.1 + 1, _⟩) (P
i')`
are paths for all `i'`, and `Drawing.inf H (C j) (P i)` is not a path, either Move 2 replaces `C j`
or Move 3 reroutes `P i`, strictly decreasing `totalDrawingEdges`. -/
theorem move2_or_move3_step {s r : ℕ}
    (hS : IsClosedSurface S) {H : Drawing S} {Δ_out : Set S} (hΔ_out : IsClosedDisc Δ_out)
    {C_in C_out : Drawing S} (hbd_out : discBd Δ_out = C_out.U)
    {C : Fin s → Drawing S} {P : Fin r → Drawing S}
    (hs : 0 < s) (hC : IsDiscNest H Δ_out C_in C_out C)
    (hP : IsDiscPaths H Δ_out C_in C_out P)
    {j : Fin s} (hj0 : 0 < j.1) (hj1 : j.1 + 1 < s)
    (hinf_in : ∀ i' : Fin r, IsDrawingPath (Drawing.inf H (C ⟨0, hs⟩) (P i')))
    (hinf_next : ∀ i' : Fin r, IsDrawingPath (Drawing.inf H (C ⟨j.1 + 1, hj1⟩) (P i')))
    {i : Fin r} (hnot_path : ¬ IsDrawingPath (Drawing.inf H (C j) (P i))) :
    ∃ (C' : Fin s → Drawing S) (P' : Fin r → Drawing S),
      IsDiscNest H Δ_out C_in C_out C' ∧
      (∀ m : Fin s, GM14.discIns Δ_out (C m) ⊆ GM14.discIns Δ_out (C' m)) ∧
      IsDiscPaths H Δ_out C_in C_out P' ∧
      totalDrawingEdges C' P' < totalDrawingEdges C P := by
  rcases exists_inner_subpath_or_outer_detour hS hΔ_out hbd_out hs hC hP hj0 hj1 hinf_next with
    ⟨C', hC', hmono, hlt⟩ | hno_outer
  · exact ⟨C', P, hC', hmono, hP, hlt⟩
  obtain ⟨hPi_H, hPi_U, a_i, ha_i, b_i, hb_i, hPi_path⟩ := hP.1 i
  have hp_j := hC.disc_props hS hΔ_out j
  have hp_0 := hC.disc_props hS hΔ_out ⟨0, hs⟩
  let m_last : Fin s := ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩
  have h0_lt_j : (⟨0, hs⟩ : Fin s) < j := hj0
  have hj_lt_last : j < m_last := by change j.1 < s - 1; omega
  have ha_0 : a_i ∈ (C ⟨0, hs⟩).U := (hC.2.2.2 hs).1.symm ▸ C_in.V_subset_U ha_i
  have ha_in_j : a_i ∈ GM14.discIns Δ_out (C j) \ (C j).U :=
    (hC.discIns_subset_diff hS hΔ_out h0_lt_j).2 (hp_0.2.2.2.2.2 ha_0)
  have hb_last : b_i ∈ (C m_last).U := (hC.2.2.2 hs).2.symm ▸ C_out.V_subset_U hb_i
  have hb_not_j : b_i ∉ GM14.discIns Δ_out (C j) :=
    fun hb_in => disjoint_left.mp (hC.discIns_subset_diff hS hΔ_out hj_lt_last).1 hb_in hb_last
  have hne_V : ((C j).V ∩ (P i).V).Nonempty := by
    have ha_Pi : a_i ∈ (P i).U := (P i).V_subset_U
      (by obtain ⟨W₀, _, hV₀, _⟩ := hPi_path; rw [hV₀]; exact W₀.start_mem_support)
    have hb_Pi : b_i ∈ (P i).U := (P i).V_subset_U
      (by obtain ⟨W₀, _, hV₀, _⟩ := hPi_path; rw [hV₀]; exact W₀.end_mem_support)
    have hne_U : ((Drawing.inf H (C j) (P i)).U).Nonempty := by
      rw [Drawing.inf_U (hC.1 j).1 hPi_H, inter_comm]
      by_contra h_empty
      rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty,
        ← hp_j.2.2.2.1] at h_empty
      rcases GM14.subset_or_disjoint_of_frontier hp_j.2.2.2.2.1
          (Drawing.IsPathBetween.isPreconnected_U hPi_path) h_empty with hsub | hdis
      · exact hb_not_j (hsub hb_Pi)
      · exact disjoint_left.mp hdis ha_Pi ha_in_j.1
    obtain ⟨x, hx⟩ := hne_U
    rcases hx with hxV | ⟨_, ⟨e, rfl⟩, _, ⟨he, rfl⟩, _⟩
    · change x ∈ (Drawing.inf H (C j) (P i)).V at hxV
      rw [Drawing.inf_V (hC.1 j).1 hPi_H] at hxV
      exact ⟨x, hxV⟩
    · obtain ⟨u, w, hlu⟩ := (H.toGraph.edge_mem_iff_exists_isLink e).mp he.2
      exact ⟨u, (((hC.1 j).1.isLink_iff he.1.1).mpr hlu).2.1,
        ((hPi_H.isLink_iff he.1.2).mpr hlu).2.1⟩
  rcases path_inf_isPath_or_exists_detour (hC.1 j).1 hPi_H hPi_path hne_V with
    hpath | ⟨v, ⟨hvC, hvP⟩, v', ⟨hv'C, hv'P⟩, hvv', W₁, W_sub, W₂, hWs, hPi_eq, hVC, hEC,
      e₁, he₁_sub, w₁, hl₁⟩
  · exact (hnot_path hpath).elim
  let P_sub := walkDrawing H W_sub
  by_cases hP_sub_in_j : P_sub.U ⊆ GM14.discIns Δ_out (C j)
  · have hsp1 := isSimple_of_append hWs
    have hsp2 := isSimple_of_append hsp1.2
    have hP_sub_path : P_sub.IsPathBetween v v' := walkDrawing_isPathBetween H hsp2.1
    have hP_sub_H : P_sub.IsSubdrawing H := walkDrawing_isSubdrawing H W_sub
    have hP_sub_Pi : P_sub.IsSubdrawing (P i) := by
      rw [hPi_eq]
      refine ⟨fun x hx => ?_, fun e he => ?_⟩
      · rw [walkDrawing_V, mem_ofPred_eq] at hx ⊢
        rw [GraphWalk.mem_support_append, GraphWalk.mem_support_append]
        exact Or.inr (Or.inl hx)
      · rw [walkDrawing_E, mem_ofPred_eq] at he ⊢
        rw [GraphWalk.edges_append, GraphWalk.edges_append, List.mem_append, List.mem_append]
        exact Or.inr (Or.inl he)
    have hmeet_0 : ((walkDrawing H W₁).U ∩ (C ⟨0, hs⟩).U).Nonempty :=
      ⟨a_i, (walkDrawing H W₁).V_subset_U (by rw [walkDrawing_V]; exact W₁.start_mem_support), ha_0⟩
    have hv_not_0 : v ∉ (C ⟨0, hs⟩).U :=
      disjoint_right.mp (hC.disjoint_U h0_lt_j.ne).2 ((C j).V_subset_U hvC)
    have hdisj_rest_0 : Disjoint (walkDrawing H (W_sub.append W₂)).U (C ⟨0, hs⟩).U :=
      disjoint_tail_of_inf_isPath (hC.1 ⟨0, hs⟩).1 W₁ (W_sub.append W₂) hWs
        (hPi_eq ▸ hinf_in i) hmeet_0 hv_not_0
    have hdisj_sub_Cin : Disjoint P_sub.U C_in.U := by
      rw [← (hC.2.2.2 hs).1]
      refine disjoint_of_subset_left ?_ hdisj_rest_0
      rw [walkDrawing_append_U]
      exact subset_union_left
    obtain ⟨Q₁, Q₂, hQ₁_path, hQ₂_path, hQ₁s, hQ₂s, _, _, hQ_V, hQ_E, hQ_sup⟩ :=
      (hC.1 j).2.1.exists_two_paths hvC hv'C hvv'
    have hQ₁_H : Q₁.IsSubdrawing H := hQ₁s.trans (hC.1 j).1
    have hQ₂_H : Q₂.IsSubdrawing H := hQ₂s.trans (hC.1 j).1
    have hCj_U_eq : (C j).U = Q₁.U ∪ Q₂.U := by
      rw [← hQ_sup, Drawing.sup_U hQ₁s hQ₂s]
    have hV_20 : Q₂.V ∩ P_sub.V = {v, v'} := by
      apply subset_antisymm
      · intro x ⟨hx₂, hx₀⟩
        have : x ∈ P_sub.V ∩ (C j).V := ⟨hx₀, hQ₂s.1 hx₂⟩
        rwa [hVC] at this
      · rintro x (rfl | rfl)
        · exact ⟨by obtain ⟨W₀, _, hV₀, _⟩ := hQ₂_path; rw [hV₀]; exact W₀.start_mem_support,
            by rw [walkDrawing_V]; exact W_sub.start_mem_support⟩
        · exact ⟨by obtain ⟨W₀, _, hV₀, _⟩ := hQ₂_path; rw [hV₀]; exact W₀.end_mem_support,
            by rw [walkDrawing_V]; exact W_sub.end_mem_support⟩
    have hV_01 : P_sub.V ∩ Q₁.V = {v, v'} := by
      apply subset_antisymm
      · intro x ⟨hx₀, hx₁⟩
        have : x ∈ P_sub.V ∩ (C j).V := ⟨hx₀, hQ₁s.1 hx₁⟩
        rwa [hVC] at this
      · rintro x (rfl | rfl)
        · exact ⟨by rw [walkDrawing_V]; exact W_sub.start_mem_support,
            by obtain ⟨W₀, _, hV₀, _⟩ := hQ₁_path; rw [hV₀]; exact W₀.start_mem_support⟩
        · exact ⟨by rw [walkDrawing_V]; exact W_sub.end_mem_support,
            by obtain ⟨W₀, _, hV₀, _⟩ := hQ₁_path; rw [hV₀]; exact W₀.end_mem_support⟩
    have hE_20 : Disjoint Q₂.E P_sub.E := disjoint_of_subset_left hQ₂s.2 hEC.symm
    have hE_01 : Disjoint P_sub.E Q₁.E := disjoint_of_subset_right hQ₁s.2 hEC
    have hcirc₁ : (H.sup P_sub Q₁).IsCircuit :=
      Drawing.isCircuit_sup hP_sub_path hQ₁_path hP_sub_H hQ₁_H hvv' hV_01 hE_01
    have hcirc₂ : (H.sup P_sub Q₂).IsCircuit :=
      Drawing.isCircuit_sup hP_sub_path hQ₂_path hP_sub_H hQ₂_H hvv'
        (by rw [inter_comm, hV_20]) hE_20.symm
    have hU₁_in_j : (H.sup P_sub Q₁).U ⊆ GM14.discIns Δ_out (C j) := by
      rw [Drawing.sup_U hP_sub_H hQ₁_H]
      exact union_subset hP_sub_in_j (hQ₁s.U_subset.trans hp_j.2.2.2.2.2)
    have hU₂_in_j : (H.sup P_sub Q₂).U ⊆ GM14.discIns Δ_out (C j) := by
      rw [Drawing.sup_U hP_sub_H hQ₂_H]
      exact union_subset hP_sub_in_j (hQ₂s.U_subset.trans hp_j.2.2.2.2.2)
    let D₁ := GM14.discIns Δ_out (H.sup P_sub Q₂)
    let D₂ := GM14.discIns Δ_out (H.sup P_sub Q₁)
    let D₀ := GM14.discIns Δ_out (C j)
    have hU₁_out : (H.sup P_sub Q₁).U ⊆ Δ_out := hU₁_in_j.trans hp_j.1
    have hU₂_out : (H.sup P_sub Q₂).U ⊆ Δ_out := hU₂_in_j.trans hp_j.1
    obtain ⟨⟨sub_D₁, d_D₁, b_D₁⟩, _⟩ := GM14.discIns_spec hΔ_out hcirc₂ hU₂_out
    obtain ⟨⟨sub_D₂, d_D₂, b_D₂⟩, _⟩ := GM14.discIns_spec hΔ_out hcirc₁ hU₁_out
    obtain ⟨_, uniq_D₀⟩ := GM14.discIns_spec hΔ_out (hC.1 j).2.1 (hC.1 j).2.2
    have f_D₁ : frontier D₁ = Q₂.U ∪ P_sub.U := by
      rw [GM14.IsClosedDisc.frontier_eq_discBd hS d_D₁, b_D₁, Drawing.sup_U hP_sub_H hQ₂_H,
        union_comm]
    have f_D₂ : frontier D₂ = P_sub.U ∪ Q₁.U := by
      rw [GM14.IsClosedDisc.frontier_eq_discBd hS d_D₂, b_D₂, Drawing.sup_U hP_sub_H hQ₁_H]
    have hnot_Q₁_D₁ : ¬ Q₁.U ⊆ D₁ :=
      not_arc_subset_chord_discIns hS hΔ_out hvv' (hC.1 j).1 (hC.1 j).2.1 (hC.1 j).2.2
        hQ₂_H hCj_U_eq hP_sub_H hP_sub_path hVC hEC hcirc₂ hU₂_in_j
    have hnot_Q₂_D₂ : ¬ Q₂.U ⊆ D₂ :=
      not_arc_subset_chord_discIns hS hΔ_out hvv' (hC.1 j).1 (hC.1 j).2.1 (hC.1 j).2.2
        hQ₁_H (by rw [hCj_U_eq, union_comm]) hP_sub_H hP_sub_path hVC hEC hcirc₁ hU₁_in_j
    obtain ⟨dU, hbdU, hcap_D, out_Q₁, out_Q₂⟩ :=
      theta_inner_chord_split hS
        (GM14.isLine_of_isPathBetween hQ₁_path hvv')
        (GM14.isLine_of_isPathBetween hQ₂_path hvv')
        (GM14.isLine_of_isPathBetween hP_sub_path hvv')
        (by rw [GM14.U_inter_of_disjoint hQ₁_H hQ₂_H hQ_E, hQ_V])
        (by rw [GM14.U_inter_of_disjoint hQ₂_H hP_sub_H hE_20, hV_20])
        (by rw [GM14.U_inter_of_disjoint hP_sub_H hQ₁_H hE_01, hV_01])
        d_D₁ d_D₂ hp_j.2.1
        f_D₁ f_D₂ (hp_j.2.2.2.1.trans hCj_U_eq)
        hnot_Q₁_D₁ hnot_Q₂_D₂
    have hD_union : D₁ ∪ D₂ = D₀ :=
      uniq_D₀ (D₁ ∪ D₂) (union_subset sub_D₁ sub_D₂) dU (hbdU.trans hp_j.2.2.1)
    have hCin_sub_D₀ : C_in.U ⊆ D₁ ∪ D₂ := by
      rw [hD_union, ← (hC.2.2.2 hs).1]
      exact hp_0.2.2.2.2.2.trans (hC.2.2.1 h0_lt_j.le)
    have hCin_pre : IsPreconnected C_in.U := by
      rw [← (hC.2.2.2 hs).1]
      obtain ⟨φ⟩ := GM14.isOArc_of_isCircuit (hC.1 ⟨0, hs⟩).2.1
      have h_eq : (C ⟨0, hs⟩).U = range (Subtype.val ∘ φ) := by
        ext x; constructor
        · intro hx; exact ⟨φ.symm ⟨x, hx⟩, congrArg Subtype.val (φ.apply_symm_apply ⟨x, hx⟩)⟩
        · rintro ⟨t, rfl⟩; exact (φ t).2
      rw [h_eq]
      exact isPreconnected_range (continuous_subtype_val.comp φ.continuous)
    have hCin_side : C_in.U ⊆ D₁ ∨ C_in.U ⊆ D₂ := by
      by_contra hnot_side
      rw [not_or, Set.not_subset, Set.not_subset] at hnot_side
      obtain ⟨⟨x₁, hx₁_in, hx₁_not₁⟩, ⟨x₂, hx₂_in, hx₂_not₂⟩⟩ := hnot_side
      have hx₁_D₂ : x₁ ∈ D₂ := (hCin_sub_D₀ hx₁_in).resolve_left hx₁_not₁
      have hx₂_D₁ : x₂ ∈ D₁ := (hCin_sub_D₀ hx₂_in).resolve_right hx₂_not₂
      obtain ⟨z, hz_in, hz_D₁, hz_D₂⟩ :=
        isPreconnected_closed_iff.mp hCin_pre D₁ D₂ d_D₁.isCompact.isClosed d_D₂.isCompact.isClosed
          hCin_sub_D₀ ⟨x₂, hx₂_in, hx₂_D₁⟩ ⟨x₁, hx₁_in, hx₁_D₂⟩
      have hz_P : z ∈ P_sub.U := by
        rw [← hcap_D]
        exact ⟨hz_D₁, hz_D₂⟩
      exact disjoint_left.mp hdisj_sub_Cin hz_P hz_in
    have hreroute := reroute_path_across_inner_detour hC hP ha_i hb_i hvC hvP hv'P
      hWs hPi_eq hP_sub_Pi hEC he₁_sub hl₁ hno_outer
    rcases hCin_side with hCin_1 | hCin_2
    · obtain ⟨P', hP', hlt⟩ :=
        hreroute Q₁ D₁ D₂ hQ₁s hQ₁_path d_D₁.isCompact.isClosed d_D₂.isCompact.isClosed
          hD_union hcap_D hCin_1 out_Q₁
      exact ⟨C, P', hC, fun _ => Subset.rfl, hP', hlt⟩
    · obtain ⟨P', hP', hlt⟩ :=
        hreroute Q₂ D₂ D₁ hQ₂s hQ₂_path d_D₂.isCompact.isClosed d_D₁.isCompact.isClosed
          (by rw [union_comm, hD_union]) (by rw [inter_comm, hcap_D]) hCin_2 out_Q₂
      exact ⟨C, P', hC, fun _ => Subset.rfl, hP', hlt⟩
  · let W := W₁.append (W_sub.append W₂)
    let W_rev := W₂.reverse.append (W_sub.reverse.append W₁.reverse)
    have hW_rev_eq : W.reverse = W_rev := by
      simp only [W, W_rev, walk_reverse_append, walk_append_assoc]
    have hW_rev_s : W_rev.IsSimple := hW_rev_eq ▸ hWs.reverse
    have hPi_rev_eq : P i = walkDrawing H W_rev := by
      rw [← hW_rev_eq, walkDrawing_reverse, ← hPi_eq]
    have hVC_rev : (walkDrawing H W_sub.reverse).V ∩ (C j).V = {v', v} := by
      rw [walkDrawing_reverse, hVC, Set.pair_comm]
    have hEC_rev : Disjoint (walkDrawing H W_sub.reverse).E (C j).E := by
      rw [walkDrawing_reverse]
      exact hEC
    have hnot_in_rev : ¬ (walkDrawing H W_sub.reverse).U ⊆ GM14.discIns Δ_out (C j) := by
      rw [walkDrawing_reverse]
      exact hP_sub_in_j
    obtain ⟨C', hC', hmono, hlt⟩ :=
      move2_outer_detour hS hΔ_out hbd_out hs hC hP hj0 hj1 (hinf_next i) hb_i hW_rev_s
        hPi_rev_eq hv'C hvC hvv'.symm rfl hVC_rev hEC_rev hnot_in_rev
    exact ⟨C', P, hC', hmono, hP, hlt⟩

/-- Monotonicity refinement of `planar_nest_uncrossing`: uncrossing only enlarges the closed discs
`discIns Δ_out (C j)` bounded by the circuits of the nest. -/
theorem planar_nest_uncrossing_mono {s r : ℕ} (hS : IsClosedSurface S)
    {H : Drawing S} {Δ_out : Set S} (hΔ_out : IsClosedDisc Δ_out)
    {C_in C_out : Drawing S} (hbd_out : discBd Δ_out = C_out.U)
    (C₀ : Fin s → Drawing S) (hC₀ : IsDiscNest H Δ_out C_in C_out C₀)
    (hex_P : ∃ P₀ : Fin r → Drawing S, IsDiscPaths H Δ_out C_in C_out P₀) :
    ∃ (C : Fin s → Drawing S) (P : Fin r → Drawing S),
      IsDiscNest H Δ_out C_in C_out C ∧
      (∀ j : Fin s, GM14.discIns Δ_out (C₀ j) ⊆ GM14.discIns Δ_out (C j)) ∧
      IsDiscPaths H Δ_out C_in C_out P ∧
      ∀ (j : Fin s) (i : Fin r), IsDrawingPath (Drawing.inf H (C j) (P i)) := by
  classical
  obtain ⟨P₀, hP₀⟩ := hex_P
  obtain ⟨C, P, ⟨hC, hmono, hP⟩, hmin⟩ :=
    exists_min_totalDrawingEdges
      (fun C P => IsDiscNest H Δ_out C_in C_out C ∧
        (∀ j : Fin s, GM14.discIns Δ_out (C₀ j) ⊆ GM14.discIns Δ_out (C j)) ∧
        IsDiscPaths H Δ_out C_in C_out P)
      ⟨C₀, P₀, hC₀, fun _ => Subset.rfl, hP₀⟩
  refine ⟨C, P, hC, hmono, hP, ?_⟩
  by_contra hnot_all
  push Not at hnot_all
  obtain ⟨j_bad, i_bad, hbad⟩ := hnot_all
  have hs : 0 < s := Nat.zero_lt_of_lt j_bad.2
  by_cases h_end : ∃ i : Fin r,
      ¬ IsDrawingPath (Drawing.inf H (C ⟨0, hs⟩) (P i)) ∨
      ¬ IsDrawingPath (Drawing.inf H (C ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩) (P i))
  · obtain ⟨i, hi⟩ := h_end
    obtain ⟨P', hP', hlt⟩ := move1_step hs hC hP hi
    exact Nat.lt_irrefl _ (lt_of_lt_of_le hlt (hmin C P' ⟨hC, hmono, hP'⟩))
  · push Not at h_end
    have hex_k : ∃ k : ℕ, ∃ (hk : k < s) (i : Fin r),
        ¬ IsDrawingPath (Drawing.inf H (C ⟨s - 1 - k, by omega⟩) (P i)) := by
      refine ⟨s - 1 - j_bad.1, by omega, i_bad, ?_⟩
      have hj_eq : (⟨s - 1 - (s - 1 - j_bad.1), by omega⟩ : Fin s) = j_bad :=
        Fin.ext (by dsimp; omega)
      rwa [hj_eq]
    let k₀ := Nat.find hex_k
    obtain ⟨hk₀, i₀, hi₀⟩ := Nat.find_spec hex_k
    let j₀ : Fin s := ⟨s - 1 - k₀, by omega⟩
    have hj₀_val : j₀.1 = s - 1 - k₀ := rfl
    have hi₀' : ¬ IsDrawingPath (Drawing.inf H (C j₀) (P i₀)) := hi₀
    have hj₀_0 : 0 < j₀.1 := by
      refine Nat.pos_of_ne_zero fun h0 => ?_
      have hj_eq : j₀ = ⟨0, hs⟩ := Fin.ext h0
      exact (hj_eq ▸ hi₀') (h_end i₀).1
    have hj₀_1 : j₀.1 + 1 < s := by
      have hne : j₀.1 ≠ s - 1 := fun hlast => by
        have hj_eq : j₀ = ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ := Fin.ext hlast
        exact (hj_eq ▸ hi₀') (h_end i₀).2
      omega
    have hinf_next : ∀ i' : Fin r,
        IsDrawingPath (Drawing.inf H (C ⟨j₀.1 + 1, hj₀_1⟩) (P i')) := by
      intro i'
      by_contra hnot_next
      have hk_lt : s - 1 - (j₀.1 + 1) < k₀ := by omega
      have hj_eq :
          (⟨s - 1 - (s - 1 - (j₀.1 + 1)), by omega⟩ : Fin s) = ⟨j₀.1 + 1, hj₀_1⟩ :=
        Fin.ext (by dsimp; omega)
      exact Nat.find_min hex_k hk_lt ⟨by omega, i', hj_eq.symm ▸ hnot_next⟩
    obtain ⟨C', P', hC', hmono', hP', hlt⟩ :=
      move2_or_move3_step hS hΔ_out hbd_out hs hC hP hj₀_0 hj₀_1
        (fun i' => (h_end i').1) hinf_next hi₀
    exact Nat.lt_irrefl _ (lt_of_lt_of_le hlt
      (hmin C' P' ⟨hC', fun j => (hmono j).trans (hmono' j), hP'⟩))

/-- **Closed-Disc Nest-and-Paths Uncrossing Theorem (Graph Minors III, Theorem (4.1), pages 60–61;
Graph Minors XIV, (9.5) Claim (3), page 46)**:
Given a closed disc `Δ_out` in a closed surface `S` with boundary circuit `C_out`, an inner circuit
`C_in`, an initial `s`-nest `C₀` of circuits of `H` in `Δ_out` from `C_in` to `C_out`, and an
initial family `P₀` of `r` pairwise vertex-disjoint paths of `H` in `Δ_out` between `C_in.V` and
`C_out.V`, there exist an `s`-nest `C` and a family `P` of `r` pairwise vertex-disjoint paths such
that `Drawing.inf H (C j) (P i)` is a path for all `j : Fin s` and `i : Fin r`. -/
theorem planar_nest_uncrossing {s r : ℕ} (hS : IsClosedSurface S)
    {H : Drawing S} {Δ_out : Set S} (hΔ_out : IsClosedDisc Δ_out)
    {C_in C_out : Drawing S} (hbd_out : discBd Δ_out = C_out.U)
    (hex_C : ∃ C₀ : Fin s → Drawing S, IsDiscNest H Δ_out C_in C_out C₀)
    (hex_P : ∃ P₀ : Fin r → Drawing S, IsDiscPaths H Δ_out C_in C_out P₀) :
    ∃ (C : Fin s → Drawing S) (P : Fin r → Drawing S),
      IsDiscNest H Δ_out C_in C_out C ∧
      IsDiscPaths H Δ_out C_in C_out P ∧
      ∀ (j : Fin s) (i : Fin r), IsDrawingPath (Drawing.inf H (C j) (P i)) := by
  obtain ⟨C₀, hC₀⟩ := hex_C
  obtain ⟨C, P, hC, _, hP, hinf⟩ := planar_nest_uncrossing_mono hS hΔ_out hbd_out C₀ hC₀ hex_P
  exact ⟨C, P, hC, hP, hinf⟩

end GraphMinor.GM09.PlanarNests
