/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Cited
public import LeanPool.GraphMinor.GM16.Section2
import LeanPool.GraphMinor.GM10.TangleLemmas
import LeanPool.GraphMinor.Menger.Basic
import LeanPool.GraphMinor.GM09.Basic

/-!
# Graph Minors XVI, Section 3: Surfaces, Societies, and Segregations

This file formalizes Section 3 ("Surfaces, societies and segregations", pages 48–52) of
N. Robertson and P. D. Seymour, *Graph Minors. XVI. Excluding a non-planar graph*, J. Combin.
Theory Ser. B 89 (2003) 43–76:

- Walk and connectedness equivalences between `G : Graph α β` and `(Hypergraph.ofGraph G hV
  hE).skeleton`.
- Equivalence between `GM16.ControlsMinor`, `GM12.ControlsMinor`, and `GM15.ControlsCliqueMinor`
  for tangles of order `≥ |V(L)|`.
- Derivation of linear decompositions for any given clockwise enumeration `t : Fin n → α` of a
  `ρ`-vortex `(G, Ω)` (`exists_isLinearDecomposition_of_isRhoVortex`), following the
  Menger/submodularity
  argument of Graph Minors IX, (8.1) (pages 60–62) via `GraphMinor.menger`.
- **Graph Minors XVI, (3.2)** (`theorem_3_2 : GM16Theorem32Statement.{u, v}`, pages 50–51), with
  its intermediate claims (1), (2), and (3) (`lemma_3_2_claim_1`, `lemma_3_2_claim_2`,
  `lemma_3_2_claim_3`).
-/

public section

namespace GraphMinor.GM16

open Set Function Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14 GraphMinor.GM15

universe u v w

variable {α : Type u} {β : Type v}

/-! ## Walk and Connectedness Equivalences between `Graph` and `Hypergraph.skeleton` -/

/-- If `u ≠ v` and `e` is incident with both `u` and `v` in `G : Graph α β`, then `G.IsLink e u v`.
-/
theorem isLink_of_inc_of_inc_of_ne {G : Graph α β} {e : β} {u v : α}
    (hu : G.Inc e u) (hv : G.Inc e v) (huv : u ≠ v) : G.IsLink e u v := by
  rcases hu with ⟨x, hux⟩
  rcases hv with ⟨y, hvy⟩
  rcases G.eq_or_eq_of_isLink_of_isLink hvy hux.symm with rfl | rfl
  · exact hux
  · exact (huv rfl).elim

/-- Reachability under `H.Adj` implies reachability in `(Hypergraph.ofGraph H hVH hEH).skeleton`. -/
theorem skeleton_reachable_of_reflTransGen_adj {H : Graph α β}
    (hVH : V(H).Finite) (hEH : E(H).Finite) {u v : α}
    (h : Relation.ReflTransGen H.Adj u v) :
    (Hypergraph.ofGraph H hVH hEH).skeleton.Reachable u v := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b c _ hadj ih =>
    by_cases hbc : b = c
    · subst hbc; exact ih
    · rcases hadj with ⟨e, hlink⟩
      have hadj_skel : (Hypergraph.ofGraph H hVH hEH).skeleton.Adj b c :=
        ⟨hbc, e, ⟨c, hlink⟩, ⟨b, hlink.symm⟩⟩
      exact ih.trans hadj_skel.reachable

/-- Reachability in `(Hypergraph.ofGraph H hVH hEH).skeleton` implies `Relation.ReflTransGen H.Adj`.
-/
theorem reflTransGen_adj_of_skeleton_walk {H : Graph α β}
    {hVH : V(H).Finite} {hEH : E(H).Finite} {u v : α}
    (w : (Hypergraph.ofGraph H hVH hEH).skeleton.Walk u v) :
    Relation.ReflTransGen H.Adj u v := by
  induction w with
  | nil => exact Relation.ReflTransGen.refl
  | @cons a b c hadj _ ih =>
    rcases hadj with ⟨hab, e, ha_inc, hb_inc⟩
    exact Relation.ReflTransGen.head ⟨e, isLink_of_inc_of_inc_of_ne ha_inc hb_inc hab⟩ ih

/-- Every walk in `(Hypergraph.ofGraph H hVH hEH).skeleton` from `u ∈ V(H)` to `v` lifts to a
`GraphWalk H u v` with the same vertex support. -/
theorem exists_graphWalk_of_skeleton_walk {H : Graph α β} (hVH : V(H).Finite) (hEH : E(H).Finite)
    {u v : α} (hu : u ∈ V(H)) (w : (Hypergraph.ofGraph H hVH hEH).skeleton.Walk u v) :
    ∃ W : GraphWalk H u v, W.support = w.support := by
  induction w with
  | nil => exact ⟨GraphWalk.nil hu, rfl⟩
  | @cons a b c hadj rest ih =>
    rcases hadj with ⟨hab, e, ha_inc, hb_inc⟩
    have hlink : H.IsLink e a b := isLink_of_inc_of_inc_of_ne ha_inc hb_inc hab
    obtain ⟨W_rest, hsupp⟩ := ih hlink.right_mem
    refine ⟨GraphWalk.cons hlink W_rest, ?_⟩
    change a :: W_rest.support = a :: rest.support
    rw [hsupp]

private theorem exists_graphWalk_in_sub {G P : Graph α β} {u v : α} (W : GraphWalk G u v)
    (hVP : ∀ x ∈ W.support, x ∈ V(P))
    (hlinkP : ∀ {e x y}, e ∈ W.edges → x ∈ W.support → y ∈ W.support →
      G.IsLink e x y → P.IsLink e x y) :
    ∃ W_P : GraphWalk P u v, W_P.support = W.support ∧ W_P.edges = W.edges := by
  induction W with
  | @nil a ha =>
    refine ⟨GraphWalk.nil (hVP a (by simp [GraphWalk.support])), rfl, rfl⟩
  | @cons a b c e hlink rest ih =>
    have hVP_rest : ∀ x ∈ rest.support, x ∈ V(P) := fun x hx =>
      hVP x (by simp [GraphWalk.support, hx])
    have hlinkP_rest : ∀ {e' x y}, e' ∈ rest.edges → x ∈ rest.support → y ∈ rest.support →
        G.IsLink e' x y → P.IsLink e' x y := fun he' hx hy hl =>
      hlinkP (by simp [GraphWalk.edges, he']) (by simp [GraphWalk.support, hx])
        (by simp [GraphWalk.support, hy]) hl
    obtain ⟨W_rest, hsupp, hedges⟩ := ih hVP_rest hlinkP_rest
    have ha_supp : a ∈ (GraphWalk.cons hlink rest).support := by simp [GraphWalk.support]
    have hb_supp : b ∈ (GraphWalk.cons hlink rest).support := by
      cases rest <;> simp [GraphWalk.support]
    have he_edges : e ∈ (GraphWalk.cons hlink rest).edges := by simp [GraphWalk.edges]
    have hlink_P : P.IsLink e a b := hlinkP he_edges ha_supp hb_supp hlink
    refine ⟨GraphWalk.cons hlink_P W_rest, ?_, ?_⟩
    · simp [GraphWalk.support, hsupp]
    · simp [GraphWalk.edges, hedges]

private theorem graphWalk_support_subset_vertexSet {G : Graph α β} {u v : α}
    (W : GraphWalk G u v) : ∀ x ∈ W.support, x ∈ V(G) := by
  induction W with
  | nil hv =>
    intro x hx
    simp only [GraphWalk.support, List.mem_singleton] at hx
    exact hx ▸ hv
  | cons hlink _ ih =>
    intro x hx
    simp only [GraphWalk.support, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hlink.left_mem
    · exact ih x hx

private theorem exists_isLink_of_mem_graphWalk_edges {G : Graph α β} {u v : α}
    (W : GraphWalk G u v) {e : β} (he : e ∈ W.edges) :
    ∃ x y, G.IsLink e x y ∧ x ∈ W.support ∧ y ∈ W.support := by
  induction W with
  | nil _ => simp [GraphWalk.edges] at he
  | @cons a b c e' hlink rest ih =>
    simp only [GraphWalk.edges, List.mem_cons] at he
    rcases he with rfl | he
    · refine ⟨a, b, hlink, by simp [GraphWalk.support], ?_⟩
      cases rest <;> simp [GraphWalk.support]
    · obtain ⟨x, y, hl, hx, hy⟩ := ih he
      exact ⟨x, y, hl, by simp [GraphWalk.support, hx], by simp [GraphWalk.support, hy]⟩

/-- Every simple path `w` in `(Hypergraph.ofGraph G hV hE).skeleton` from `a ∈ V(G)` to `b` lifts
to a graph path `P` of `G` with ends `a, b` and `V(P) = {x | x ∈ w.support}`. -/
theorem exists_isGraphPathWithEnds_of_skeleton_isPath {G : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite) {a b : α} (ha : a ∈ V(G))
    (w : (Hypergraph.ofGraph G hV hE).skeleton.Walk a b) (hw : w.IsPath) :
    ∃ P : Graph α β, IsGraphPathWithEnds G P a b ∧ V(P) = {x | x ∈ w.support} := by
  obtain ⟨W, hsupp⟩ := exists_graphWalk_of_skeleton_walk hV hE ha w
  let P : Graph α β := (G.induce {x | x ∈ W.support}).restrict {e | e ∈ W.edges}
  have hP_le : P ≤ G := restrict_le.trans (G.induce_le (graphWalk_support_subset_vertexSet W))
  obtain ⟨W_P, hsupp_P, hedges_P⟩ := exists_graphWalk_in_sub (P := P) W
    (fun x hx => hx)
    (fun he hx hy hlink => ⟨he, hlink, hx, hy⟩)
  refine ⟨P, ⟨hP_le, W_P, ?_, ?_, ?_⟩, ?_⟩
  · unfold GraphWalk.IsSimple
    rw [hsupp_P, hsupp]
    exact hw.support_nodup
  · change {x | x ∈ W.support} = {x | x ∈ W_P.support}
    rw [hsupp_P]
  · ext e
    simp only [P, edgeSet_restrict, mem_inter_iff, Graph.edgeSet_induce, Set.mem_ofPred_eq,
      hedges_P]
    exact ⟨fun h => h.2, fun he => ⟨exists_isLink_of_mem_graphWalk_edges W he, he⟩⟩
  · change {x | x ∈ W.support} = {x | x ∈ w.support}
    rw [hsupp]

/-- Equivalence between `GraphConnected H` and `GM12.IsConnectedSub` for a subhypergraph
`H_H ≤ Hypergraph.ofGraph G hV hE`. -/
theorem graphConnected_subgraphOfSubhypergraph_iff {G : Graph α β}
    {hV : V(G).Finite} {hE : E(G).Finite} {H_H : Hypergraph α β}
    (hH : H_H ≤ Hypergraph.ofGraph G hV hE) (hne : H_H.vertexSet.Nonempty) :
    GraphConnected (subgraphOfSubhypergraph G H_H) ↔ GM12.IsConnectedSub H_H := by
  let H := subgraphOfSubhypergraph G H_H
  have hVH : V(H).Finite := H_H.vertexSet_finite
  have hEH : E(H).Finite :=
    H_H.edgeSet_finite.subset (by rw [edgeSet_subgraphOfSubhypergraph hH])
  have hof : Hypergraph.ofGraph H hVH hEH = H_H := ofGraph_subgraphOfSubhypergraph hH
  constructor
  · rintro ⟨_, hconn⟩ u hu v hv
    rw [← hof]
    exact skeleton_reachable_of_reflTransGen_adj hVH hEH (hconn u hu v hv)
  · intro hconn
    refine ⟨hne, fun u hu v hv => ?_⟩
    rw [← hof] at hconn
    obtain ⟨w⟩ := hconn u hu v hv
    exact reflTransGen_adj_of_skeleton_walk w

/-! ## Equivalence of `GM16.ControlsMinor`, `GM12.ControlsMinor`, and `GM15.ControlsCliqueMinor` -/

/-- `GM12.ControlsMinor` implies `GM16.ControlsMinor`. -/
theorem controlsMinor_of_gm12 {α' β' : Type*} {G : Graph α β} {hV : V(G).Finite}
    {hE : E(G).Finite} {θ_star : ℕ} {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {L : Graph α' β'}
    (h : GM12.ControlsMinor (Hypergraph.ofGraph G hV hE) θ_star T_star L) :
    ControlsMinor G L T_star := by
  rcases h with ⟨a, b, ha_conn, ha_disj, hb_link, hb_loop, hb_inj, _, hno_small⟩
  let α_v : α' → Graph α β := fun v => subgraphOfSubhypergraph G (a v)
  refine ⟨α_v, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨hle, hne, hconn⟩ := ha_conn v hv
    exact ⟨subgraphOfSubhypergraph_le hle, hne,
      (graphConnected_subgraphOfSubhypergraph_iff hle hne).mpr hconn⟩
  · intro u hu v hv huv
    exact ha_disj u hu v hv huv
  · intro e he u hu v hv huv hlink
    obtain ⟨hbe, ⟨x, hx, hinc_x⟩, ⟨y, hy, hinc_y⟩⟩ := hb_link e u v hlink huv
    have hxy : x ≠ y := (ha_disj u hu v hv huv).ne_of_mem hx hy
    exact ⟨hbe, x, hx, y, hy, isLink_of_inc_of_inc_of_ne hinc_x hinc_y hxy⟩
  · intro e he v hv hloop
    obtain ⟨hbe, hnot_mem, hends⟩ := hb_loop e v hloop
    have hle : a v ≤ Hypergraph.ofGraph G hV hE := (ha_conn v hv).1
    rw [← edgeSet_subgraphOfSubhypergraph hle] at hnot_mem
    obtain ⟨x, y, hlink⟩ := exists_isLink_of_mem_edgeSet hbe
    exact ⟨⟨hbe, hnot_mem⟩, x, hends x ⟨y, hlink⟩, y, hends y ⟨x, hlink.symm⟩, hlink⟩
  · intro e he f hf hef
    exact by_contra fun hne => hb_inj e he f hf hne hef
  · intro A B hAB hord v hv
    exact hno_small A B hAB hord v hv

/-- `GM16.ControlsMinor` implies `GM12.ControlsMinor` when `V(L).ncard ≤ θ_star`. -/
theorem gm12_controlsMinor_of_controlsMinor {α' β' : Type*} {G : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite) {θ_star : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)} {L : Graph α' β'}
    (h : ControlsMinor G L T_star) (hθ : V(L).ncard ≤ θ_star) :
    GM12.ControlsMinor (Hypergraph.ofGraph G hV hE) θ_star T_star L := by
  classical
  rcases h with ⟨α_v, α_e, hα_conn, hα_disj, hα_link, hα_loop, hα_inj, hno_small⟩
  let a : α' → Hypergraph α β := fun v =>
    if hv : v ∈ V(L) then
      Hypergraph.ofGraph (α_v v) (hV.subset (hα_conn v hv).1.vertexSet_mono)
        (hE.subset (hα_conn v hv).1.edgeSet_mono)
    else ⊥
  have ha_eq : ∀ {v : α'} (hv : v ∈ V(L)),
      a v = Hypergraph.ofGraph (α_v v) (hV.subset (hα_conn v hv).1.vertexSet_mono)
        (hE.subset (hα_conn v hv).1.edgeSet_mono) := fun hv => dite_eq_left hv
  refine ⟨a, α_e, ?_, ?_, ?_, ?_, ?_, hθ, ?_⟩
  · intro v hv
    obtain ⟨hle, hne, hconn⟩ := hα_conn v hv
    have hle_H : a v ≤ Hypergraph.ofGraph G hV hE := by
      rw [ha_eq hv]
      exact ⟨hle.vertexSet_mono, hle.edgeSet_mono, fun e he => by
        ext x; exact (hle.inc_congr he).symm⟩
    have hsub_eq : subgraphOfSubhypergraph G (a v) = α_v v := by
      rw [ha_eq hv]
      exact subgraphOfSubhypergraph_ofGraph hle _ _
    have hne_H : (a v).vertexSet.Nonempty := by rw [ha_eq hv]; exact hne
    refine ⟨hle_H, hne_H, ?_⟩
    rw [← graphConnected_subgraphOfSubhypergraph_iff hle_H hne_H, hsub_eq]
    exact hconn
  · intro u hu v hv huv
    rw [ha_eq hu, ha_eq hv]
    exact hα_disj u hu v hv huv
  · intro e u v hlink huv
    obtain ⟨hbe, x, hx, y, hy, hlinkG⟩ :=
      hα_link e hlink.edge_mem u hlink.left_mem v hlink.right_mem huv hlink
    rw [ha_eq hlink.left_mem, ha_eq hlink.right_mem]
    exact ⟨hbe, ⟨x, hx, y, hlinkG⟩, ⟨y, hy, x, hlinkG.symm⟩⟩
  · intro e v hloop
    have hv : v ∈ V(L) := hloop.left_mem
    obtain ⟨⟨hbe, hnot_mem⟩, x, hx, y, hy, hlinkG⟩ := hα_loop e hloop.edge_mem v hv hloop
    rw [ha_eq hv]
    refine ⟨hbe, hnot_mem, fun z hz => ?_⟩
    rcases hz with ⟨w, hzw⟩
    rcases G.eq_or_eq_of_isLink_of_isLink hzw hlinkG with rfl | rfl
    · exact hx
    · exact hy
  · intro e he f hf hne heq
    exact hne (hα_inj he hf heq)
  · intro A B hAB hord v hv
    rw [ha_eq hv]
    exact hno_small hAB hord v hv

/-- Equivalence between `GM16.ControlsMinor` and `GM12.ControlsMinor` when `V(L).ncard ≤ θ_star`. -/
theorem controlsMinor_iff_gm12 {α' β' : Type*} {G : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite) {θ_star : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)} {L : Graph α' β'}
    (hθ : V(L).ncard ≤ θ_star) :
    ControlsMinor G L T_star ↔
      GM12.ControlsMinor (Hypergraph.ofGraph G hV hE) θ_star T_star L :=
  ⟨fun h => gm12_controlsMinor_of_controlsMinor hV hE h hθ, controlsMinor_of_gm12⟩

/-- `V(completeGraph p).ncard = p`. -/
@[simp]
theorem vertexSet_completeGraph_ncard (p : ℕ) : V(completeGraph p).ncard = p := by
  change (Set.univ : Set (Fin p)).ncard = p
  simp

/-- `GM16.ControlsMinor G (completeGraph p) T_star` implies `GM15.ControlsCliqueMinor G p T_star`.
-/
theorem controlsCliqueMinor_of_controlsMinor {G : Graph α β} {p : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    (h : ControlsMinor G (completeGraph p) T_star) :
    ControlsCliqueMinor G p T_star := by
  rcases h with ⟨α_v, α_e, hconn, hdisj, hlink, _, _, hno_small⟩
  refine ⟨α_v, fun i => hconn i (mem_univ i),
    fun i j hij => hdisj i (mem_univ i) j (mem_univ j) hij,
    fun i j hij => ?_,
    fun A B hAB hord i => hno_small hAB (by simpa using hord) i (mem_univ i)⟩
  have he : s(i, j) ∈ E(completeGraph p) := ⟨i, j, ne_of_lt hij, rfl⟩
  obtain ⟨hb, x, hx, y, hy, hlinkG⟩ :=
    hlink s(i, j) he i (mem_univ i) j (mem_univ j) (ne_of_lt hij) ⟨ne_of_lt hij, rfl⟩
  exact ⟨α_e s(i, j), hb, x, hx, y, hy, hlinkG⟩

/-- `GM12.ControlsMinor` for `completeGraph p` implies `GM15.ControlsCliqueMinor`. -/
theorem controlsCliqueMinor_of_gm12 {G : Graph α β}
    {hV : V(G).Finite} {hE : E(G).Finite} {θ_star p : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    (h : GM12.ControlsMinor (Hypergraph.ofGraph G hV hE) θ_star T_star (completeGraph p)) :
    ControlsCliqueMinor G p T_star :=
  controlsCliqueMinor_of_controlsMinor (controlsMinor_of_gm12 h)

/-- `GM15.ControlsCliqueMinor G p T_star` implies `GM16.ControlsMinor G (completeGraph p) T_star`
when `p ≠ 1` or `Nonempty β`. -/
theorem controlsMinor_of_controlsCliqueMinor {G : Graph α β} {p : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    (hp : p ≠ 1 ∨ Nonempty β) (h : ControlsCliqueMinor G p T_star) :
    ControlsMinor G (completeGraph p) T_star := by
  classical
  rcases h with ⟨X_sub, hconn, hdisj, hlink, hno_small⟩
  by_cases hp0 : p = 0
  · subst hp0
    refine ⟨X_sub, isEmptyElim, fun v _ => Fin.elim0 v, fun u _ => Fin.elim0 u,
      fun e he => ?_, fun e he => ?_, fun e he => ?_, fun A B _ _ v _ => Fin.elim0 v⟩
    · rcases he with ⟨x, _⟩; exact Fin.elim0 x
    · rcases he with ⟨x, _⟩; exact Fin.elim0 x
    · rcases he with ⟨x, _⟩; exact Fin.elim0 x
  have hβ : Nonempty β := by
    rcases hp with hp1 | hβ
    · have hp2 : 2 ≤ p := by omega
      obtain ⟨b, _, _⟩ := hlink ⟨0, by omega⟩ ⟨1, by omega⟩ (Fin.mk_lt_mk.mpr Nat.zero_lt_one)
      exact ⟨b⟩
    · exact hβ
  have hex_edge : ∀ e : Sym2 (Fin p), e ∈ E(completeGraph p) →
      ∃ b : β, b ∈ E(G) ∧ ∀ u v : Fin p, u ≠ v → e = s(u, v) →
        ∃ x ∈ V(X_sub u), ∃ y ∈ V(X_sub v), G.IsLink b x y := by
    rintro e ⟨i, j, hij, rfl⟩
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · obtain ⟨b, hb, x, hx, y, hy, hlinkG⟩ := hlink i j hlt
      refine ⟨b, hb, fun u v _ heq => ?_⟩
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨x, hx, y, hy, hlinkG⟩
      · exact ⟨y, hy, x, hx, hlinkG.symm⟩
    · obtain ⟨b, hb, x, hx, y, hy, hlinkG⟩ := hlink j i hgt
      refine ⟨b, hb, fun u v _ heq => ?_⟩
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨y, hy, x, hx, hlinkG.symm⟩
      · exact ⟨x, hx, y, hy, hlinkG⟩
  let α_e : Sym2 (Fin p) → β := fun e =>
    if he : e ∈ E(completeGraph p) then (hex_edge e he).choose else Classical.choice hβ
  refine ⟨X_sub, α_e, fun v _ => hconn v, fun u _ v _ huv => hdisj u v huv, ?_, ?_, ?_,
    fun A B hAB hord v _ => hno_small hAB (by simpa using hord) v⟩
  · intro e he u _ v _ huv hlinkL
    dsimp only [α_e]
    rw [dite_eq_left he]
    have hspec := (hex_edge e he).choose_spec
    exact ⟨hspec.1, hspec.2 u v huv hlinkL.2⟩
  · intro e _ v _ hloop
    exact False.elim (hloop.1 rfl)
  · intro e₁ he₁ e₂ he₂ heq
    dsimp only [α_e] at heq
    rw [dite_eq_left he₁, dite_eq_left he₂] at heq
    rcases he₁ with ⟨u₁, v₁, huv₁, rfl⟩
    rcases he₂ with ⟨u₂, v₂, huv₂, rfl⟩
    obtain ⟨x₁, hx₁, y₁, hy₁, hl₁⟩ :=
      (hex_edge s(u₁, v₁) ⟨u₁, v₁, huv₁, rfl⟩).choose_spec.2 u₁ v₁ huv₁ rfl
    obtain ⟨x₂, hx₂, y₂, hy₂, hl₂⟩ :=
      (hex_edge s(u₂, v₂) ⟨u₂, v₂, huv₂, rfl⟩).choose_spec.2 u₂ v₂ huv₂ rfl
    rw [← heq] at hl₂
    have hxy₁ : x₁ ≠ y₁ := fun h =>
      Set.disjoint_left.mp (hdisj u₁ v₁ huv₁) hx₁ (h ▸ hy₁)
    have hx_cases := G.eq_or_eq_of_isLink_of_isLink hl₁ hl₂
    have hy_cases := G.eq_or_eq_of_isLink_of_isLink hl₁.symm hl₂
    rw [Sym2.eq_iff]
    rcases hx_cases with rfl | rfl
    · have hy_eq : y₁ = y₂ := hy_cases.resolve_left hxy₁.symm
      subst hy_eq
      left
      exact ⟨by_contra fun hne => Set.disjoint_left.mp (hdisj u₁ u₂ hne) hx₁ hx₂,
        by_contra fun hne => Set.disjoint_left.mp (hdisj v₁ v₂ hne) hy₁ hy₂⟩
    · have hy_eq : y₁ = x₂ := hy_cases.resolve_right hxy₁.symm
      subst hy_eq
      right
      exact ⟨by_contra fun hne => Set.disjoint_left.mp (hdisj u₁ v₂ hne) hx₁ hy₂,
        by_contra fun hne => Set.disjoint_left.mp (hdisj v₁ u₂ hne) hy₁ hx₂⟩

/-! ## Linear Decompositions of `ρ`-Vortices and Graph Minors XVI, (3.2) (pages 50–51) -/

private lemma toFun_t_eq_of_isClockwiseSeq {S : Society α β} {n : ℕ} {t : Fin n → α}
    (hn : 1 ≤ n) (ht_range : range t = S.Ω.bar) (ht_cw : S.Ω.IsClockwiseSeq (List.ofFn t))
    (i : Fin n) :
    S.Ω.toFun (t i) = t ⟨(i.1 + 1) % n, Nat.mod_lt _ (by omega)⟩ := by
  have hbar : {v | v ∈ List.ofFn t} = S.Ω.bar := by
    ext v
    simp [List.mem_ofFn, ← ht_range]
  have hhit := ht_cw.2.2 i.1 (by simp)
  simp only [List.length_ofFn, List.getElem_ofFn, hbar] at hhit
  rcases hhit with ⟨k, hk1, hk_eq, _, hk_min⟩
  have hti_bar : t i ∈ S.Ω.bar := ht_range ▸ mem_range_self i
  have hnext_bar : S.Ω.toFun (t i) ∈ S.Ω.bar := S.Ω.bijOn.mapsTo hti_bar
  have hk_eq_one : k = 1 := by
    by_contra hne
    have hlt : 1 < k := by omega
    exact hk_min 1 le_rfl hlt hnext_bar
  subst hk_eq_one
  exact hk_eq

private lemma iterate_toFun_t_eq_of_isClockwiseSeq {S : Society α β} {n : ℕ} {t : Fin n → α}
    (hn : 1 ≤ n) (ht_range : range t = S.Ω.bar) (ht_cw : S.Ω.IsClockwiseSeq (List.ofFn t))
    (i : Fin n) (m : ℕ) :
    (S.Ω.toFun^[m]) (t i) = t ⟨(i.1 + m) % n, Nat.mod_lt _ (by omega)⟩ := by
  induction m with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.add_zero]
    congr 1
    ext
    exact (Nat.mod_eq_of_lt i.2).symm
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, toFun_t_eq_of_isClockwiseSeq hn ht_range ht_cw]
    congr 1
    ext
    dsimp only
    rw [Nat.mod_add_mod, Nat.add_assoc]

private lemma firstHitIn_three_of_lt {S : Society α β} {n : ℕ} {t : Fin n → α}
    (hn : 1 ≤ n) (ht_inj : Injective t) (ht_range : range t = S.Ω.bar)
    (ht_cw : S.Ω.IsClockwiseSeq (List.ofFn t))
    {a b c : Fin n} (hab : a.1 < b.1) (hbc : b.1 < c.1)
    {X : Set α} (hX : ∀ x, x ∈ X ↔ x = t a ∨ x = t b ∨ x = t c) :
    S.Ω.FirstHitIn X (t a) (t b) ∧
    S.Ω.FirstHitIn X (t b) (t c) ∧
    S.Ω.FirstHitIn X (t c) (t a) := by
  have hiter := iterate_toFun_t_eq_of_isClockwiseSeq hn ht_range ht_cw
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨b.1 - a.1, by omega, ?_, (hX (t b)).mpr (Or.inr (Or.inl rfl)), ?_⟩
    · rw [hiter]
      congr 1; ext; dsimp only
      rw [Nat.add_sub_of_le (le_of_lt hab), Nat.mod_eq_of_lt b.2]
    · intro m hm1 hmk hmem
      rw [hiter, hX] at hmem
      rcases hmem with h | h | h <;>
        have hval := congrArg Fin.val (ht_inj h) <;>
        dsimp only at hval <;>
        rw [Nat.mod_eq_of_lt (by omega)] at hval <;>
        omega
  · refine ⟨c.1 - b.1, by omega, ?_, (hX (t c)).mpr (Or.inr (Or.inr rfl)), ?_⟩
    · rw [hiter]
      congr 1; ext; dsimp only
      rw [Nat.add_sub_of_le (le_of_lt hbc), Nat.mod_eq_of_lt c.2]
    · intro m hm1 hmk hmem
      rw [hiter, hX] at hmem
      rcases hmem with h | h | h <;>
        have hval := congrArg Fin.val (ht_inj h) <;>
        dsimp only at hval <;>
        rw [Nat.mod_eq_of_lt (by omega)] at hval <;>
        omega
  · refine ⟨n - c.1 + a.1, by omega, ?_, (hX (t a)).mpr (Or.inl rfl), ?_⟩
    · rw [hiter]
      congr 1; ext; dsimp only
      have hsum : c.1 + (n - c.1 + a.1) = n + a.1 := by omega
      rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt a.2]
    · intro m hm1 hmk hmem
      rw [hiter, hX] at hmem
      by_cases hlt : c.1 + m < n
      · rcases hmem with h | h | h <;>
          have hval := congrArg Fin.val (ht_inj h) <;>
          dsimp only at hval <;>
          rw [Nat.mod_eq_of_lt hlt] at hval <;>
          omega
      · have hmod : (c.1 + m) % n = c.1 + m - n := by
          have hge : n ≤ c.1 + m := Nat.le_of_not_lt hlt
          have eq_add : c.1 + m = (c.1 + m - n) + n := (Nat.sub_add_cancel hge).symm
          conv_lhs => rw [eq_add]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rcases hmem with h | h | h <;>
          have hval := congrArg Fin.val (ht_inj h) <;>
          dsimp only at hval <;>
          rw [hmod] at hval <;>
          omega

private lemma isClockwise3_of_lt {S : Society α β} {n : ℕ} {t : Fin n → α}
    (hn : 1 ≤ n) (ht_inj : Injective t) (ht_range : range t = S.Ω.bar)
    (ht_cw : S.Ω.IsClockwiseSeq (List.ofFn t))
    {a b c : Fin n} (hab : a.1 < b.1) (hbc : b.1 < c.1) :
    S.Ω.IsClockwise3 (t a) (t b) (t c) ∧ S.Ω.IsClockwise3 (t b) (t c) (t a) := by
  have hne_ab : t a ≠ t b := fun h => by have := congrArg Fin.val (ht_inj h); omega
  have hne_bc : t b ≠ t c := fun h => by have := congrArg Fin.val (ht_inj h); omega
  have hne_ac : t a ≠ t c := fun h => by have := congrArg Fin.val (ht_inj h); omega
  have hbar : ∀ i : Fin n, t i ∈ S.Ω.bar := fun i => ht_range ▸ mem_range_self i
  have hX1 : ∀ x, x ∈ {v | v ∈ [t a, t b, t c]} ↔ x = t a ∨ x = t b ∨ x = t c := by
    intro x; simp
  have hX2 : ∀ x, x ∈ {v | v ∈ [t b, t c, t a]} ↔ x = t a ∨ x = t b ∨ x = t c := by
    intro x; simp [or_comm, or_left_comm]
  obtain ⟨h1_ab, h1_bc, h1_ca⟩ :=
    firstHitIn_three_of_lt hn ht_inj ht_range ht_cw hab hbc hX1
  obtain ⟨h2_ab, h2_bc, h2_ca⟩ :=
    firstHitIn_three_of_lt hn ht_inj ht_range ht_cw hab hbc hX2
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · simp [hne_ab, hne_bc, hne_ac]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> exact hbar _
  · intro i hi
    match i with
    | 0 => exact h1_ab
    | 1 => exact h1_bc
    | 2 => simpa using h1_ca
  · simp [hne_ab.symm, hne_bc, hne_ac.symm]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> exact hbar _
  · intro i hi
    match i with
    | 0 => exact h2_bc
    | 1 => exact h2_ca
    | 2 => simpa using h2_ab

private lemma exists_separation_le_rho_of_isRhoVortex {S : Society α β} {ρ n : ℕ} {t : Fin n → α}
    (hn : 1 ≤ n) (hvortex : IsRhoVortex S ρ) (ht_inj : Injective t)
    (ht_range : range t = S.Ω.bar) (ht_cw : S.Ω.IsClockwiseSeq (List.ofFn t))
    {j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n) :
    let G_H := Hypergraph.ofGraph S.G S.finite_V S.finite_E
    let A_set := {x : α | ∃ i : Fin n, i.1 < j ∧ t i = x}
    let B_set := {x : α | ∃ i : Fin n, j ≤ i.1 ∧ t i = x}
    ∃ Y Z : Hypergraph α β,
      G_H.IsSeparation Y Z ∧ A_set ⊆ Y.vertexSet ∧ B_set ⊆ Z.vertexSet ∧
        separationOrder Y Z ≤ ρ := by
  intro G_H A_set B_set
  have hbar : ∀ i : Fin n, t i ∈ S.Ω.bar := fun i => ht_range ▸ mem_range_self i
  have hA_sub : A_set ⊆ G_H.vertexSet := by
    rintro _ ⟨i, _, rfl⟩
    exact S.bar_subset (hbar i)
  have hB_sub : B_set ⊆ G_H.vertexSet := by
    rintro _ ⟨i, _, rfl⟩
    exact S.bar_subset (hbar i)
  let i₀ : Fin n := ⟨0, by omega⟩
  let ij : Fin n := ⟨j, hjn⟩
  have hA_int : A_set ⊆ S.Ω.interval (t i₀) (t ij) ∪ {t i₀} := by
    rintro _ ⟨i, hi, rfl⟩
    by_cases hi0 : i.1 = 0
    · right
      exact congrArg t (Fin.ext hi0)
    · left
      have h0i : i₀.1 < i.1 := Nat.pos_of_ne_zero hi0
      have hij : i.1 < ij.1 := hi
      refine ⟨⟨hbar i, ?_⟩, (isClockwise3_of_lt hn ht_inj ht_range ht_cw h0i hij).1⟩
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨fun h => by have := congrArg Fin.val (ht_inj h); omega,
        fun h => by have := congrArg Fin.val (ht_inj h); omega⟩
  have hB_int : B_set ⊆ S.Ω.interval (t ij) (t i₀) ∪ {t ij} := by
    rintro _ ⟨i, hi, rfl⟩
    by_cases hij_eq : i.1 = j
    · right
      exact congrArg t (Fin.ext hij_eq)
    · left
      have h0j : i₀.1 < ij.1 := hj1
      have hji : ij.1 < i.1 := by dsimp [ij]; omega
      refine ⟨⟨hbar i, ?_⟩, (isClockwise3_of_lt hn ht_inj ht_range ht_cw h0j hji).2⟩
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨fun h => by have := congrArg Fin.val (ht_inj h); dsimp [ij] at this; omega,
        fun h => by have := congrArg Fin.val (ht_inj h); dsimp [i₀] at this; omega⟩
  have hnot_paths : ¬ HasDisjointPaths G_H.skeleton A_set B_set (ρ + 1) := by
    rintro ⟨P_skel, hdisj_skel⟩
    have hex_P : ∀ k : Fin (ρ + 1),
        ∃ P : Graph α β,
          (∃ a ∈ S.Ω.interval (t i₀) (t ij) ∪ {t i₀},
            ∃ b ∈ S.Ω.interval (t ij) (t i₀) ∪ {t ij},
              IsGraphPathWithEnds S.G P a b) ∧
          V(P) = {x | x ∈ (P_skel k).walk.support} := by
      intro k
      have hfirst_G : (P_skel k).first ∈ V(S.G) := hA_sub (P_skel k).first_mem
      obtain ⟨P, hP_path, hVP⟩ := exists_isGraphPathWithEnds_of_skeleton_isPath
        S.finite_V S.finite_E hfirst_G (P_skel k).walk (P_skel k).isPath
      exact ⟨P, ⟨(P_skel k).first, hA_int (P_skel k).first_mem,
        (P_skel k).last, hB_int (P_skel k).last_mem, hP_path⟩, hVP⟩
    choose P hP_ends hVP using hex_P
    have hne_0j : t i₀ ≠ t ij := fun h => by
      have := congrArg Fin.val (ht_inj h); dsimp [i₀, ij] at this; omega
    apply hvortex (t i₀) (hbar i₀) (t ij) (hbar ij) hne_0j
    refine ⟨P, fun k₁ k₂ hk => ?_, hP_ends⟩
    dsimp only
    rw [hVP k₁, hVP k₂]
    exact hdisj_skel hk
  have hnot_all : ¬ ∀ Y Z : Hypergraph α β,
      G_H.IsSeparation Y Z → A_set ⊆ Y.vertexSet → B_set ⊆ Z.vertexSet →
        ρ + 1 ≤ separationOrder Y Z :=
    fun hall => hnot_paths ((GraphMinor.menger G_H A_set B_set hA_sub hB_sub (ρ + 1)).mp hall)
  push Not at hnot_all
  rcases hnot_all with ⟨Y, Z, hsep, hAY, hBZ, hlt⟩
  exact ⟨Y, Z, hsep, hAY, hBZ, Nat.lt_succ_iff.mp hlt⟩

private lemma submodular_separationOrder (Y₁ Z₁ Y₂ Z₂ : Hypergraph α β) :
    separationOrder (Y₁ ∩ Y₂) (Z₁ ∪ Z₂) + separationOrder (Y₁ ∪ Y₂) (Z₁ ∩ Z₂) ≤
      separationOrder Y₁ Z₁ + separationOrder Y₂ Z₂ := by
  let U₁ : Set α := (Y₁.vertexSet ∩ Y₂.vertexSet) ∩ (Z₁.vertexSet ∪ Z₂.vertexSet)
  let U₂ : Set α := (Y₁.vertexSet ∪ Y₂.vertexSet) ∩ (Z₁.vertexSet ∩ Z₂.vertexSet)
  let S₁ : Set α := Y₁.vertexSet ∩ Z₁.vertexSet
  let S₂ : Set α := Y₂.vertexSet ∩ Z₂.vertexSet
  have hU₁_fin : U₁.Finite := ((Y₁ ∩ Y₂) ∩ (Z₁ ∪ Z₂)).vertexSet_finite
  have hU₂_fin : U₂.Finite := ((Y₁ ∪ Y₂) ∩ (Z₁ ∩ Z₂)).vertexSet_finite
  have hS₁_fin : S₁.Finite := (Y₁ ∩ Z₁).vertexSet_finite
  have hS₂_fin : S₂.Finite := (Y₂ ∩ Z₂).vertexSet_finite
  have h_union : U₁ ∪ U₂ ⊆ S₁ ∪ S₂ := by
    intro v hv
    simp only [U₁, U₂, S₁, S₂, mem_union, mem_inter_iff] at hv ⊢
    tauto
  have h_inter : U₁ ∩ U₂ ⊆ S₁ ∩ S₂ := by
    intro v hv
    simp only [U₁, U₂, S₁, S₂, mem_union, mem_inter_iff] at hv ⊢
    tauto
  have h1 := Set.ncard_union_add_ncard_inter U₁ U₂ hU₁_fin hU₂_fin
  have h2 := Set.ncard_union_add_ncard_inter S₁ S₂ hS₁_fin hS₂_fin
  have hle_u : (U₁ ∪ U₂).ncard ≤ (S₁ ∪ S₂).ncard :=
    Set.ncard_le_ncard h_union (hS₁_fin.union hS₂_fin)
  have hle_i : (U₁ ∩ U₂).ncard ≤ (S₁ ∩ S₂).ncard :=
    Set.ncard_le_ncard h_inter (hS₁_fin.inter_of_left S₂)
  unfold separationOrder
  change U₁.ncard + U₂.ncard ≤ S₁.ncard + S₂.ncard
  omega

private lemma bot_le_hypergraph (G_H : Hypergraph α β) : (⊥ : Hypergraph α β) ≤ G_H :=
  ⟨empty_subset _, empty_subset _, fun _ h => h.elim⟩

private lemma isSeparation_bot_self (G_H : Hypergraph α β) : G_H.IsSeparation ⊥ G_H where
  left_le := bot_le_hypergraph G_H
  right_le := le_rfl
  union_eq := Hypergraph.ext (empty_union _) (empty_union _)
    (funext fun _ => funext fun _ => by simp [GM10.union_inc, GM10.bot_inc])
  edgeSet_inter_eq := empty_inter _

private theorem exists_minimum_separation
    {ValidSep : Hypergraph α β → Hypergraph α β → Prop} {ρ : ℕ}
    (hExists : ∃ Y Z, ValidSep Y Z ∧ separationOrder Y Z ≤ ρ) :
    ∃ (Y Z : Hypergraph α β) (k : ℕ),
      ValidSep Y Z ∧ separationOrder Y Z = k ∧ k ≤ ρ ∧
      (∀ Y' Z', ValidSep Y' Z' → k ≤ separationOrder Y' Z') ∧
      (∀ Y' Z', ValidSep Y' Z' → separationOrder Y' Z' = k →
        Y.vertexSet.ncard + Y.edgeSet.ncard ≤ Y'.vertexSet.ncard + Y'.edgeSet.ncard) := by
  obtain ⟨Y₀, Z₀, hval₀, hord₀⟩ := hExists
  let Orders : Set ℕ := {k : ℕ | ∃ Y Z, ValidSep Y Z ∧ separationOrder Y Z = k}
  have hOrders_ne : Orders.Nonempty := ⟨separationOrder Y₀ Z₀, Y₀, Z₀, hval₀, rfl⟩
  let k := sInf Orders
  obtain ⟨Y₁, Z₁, hval₁, hk₁⟩ := Nat.sInf_mem hOrders_ne
  have hk_le_ρ : k ≤ ρ := (Nat.sInf_le (s := Orders) ⟨Y₀, Z₀, hval₀, rfl⟩).trans hord₀
  have hk_min : ∀ Y' Z', ValidSep Y' Z' → k ≤ separationOrder Y' Z' :=
    fun Y' Z' hval' => Nat.sInf_le ⟨Y', Z', hval', rfl⟩
  let Sizes : Set ℕ :=
    {m : ℕ | ∃ Y Z, ValidSep Y Z ∧ separationOrder Y Z = k ∧
      Y.vertexSet.ncard + Y.edgeSet.ncard = m}
  have hSizes_ne : Sizes.Nonempty :=
    ⟨Y₁.vertexSet.ncard + Y₁.edgeSet.ncard, Y₁, Z₁, hval₁, hk₁, rfl⟩
  obtain ⟨Y, Z, hval, hk, hmin_size⟩ := Nat.sInf_mem hSizes_ne
  refine ⟨Y, Z, k, hval, hk, hk_le_ρ, hk_min, fun Y' Z' hval' hk' => ?_⟩
  rw [hmin_size]
  exact Nat.sInf_le ⟨Y', Z', hval', hk', rfl⟩

private theorem nested_of_minimum_separations
    {G_H Y₁ Y₂ Z₁ Z₂ : Hypergraph α β} {A₁ A₂ B₁ B₂ : Set α}
    (hA : A₁ ⊆ A₂) (hB : B₂ ⊆ B₁) :
    let ValidSep (A B : Set α) (Y Z : Hypergraph α β) :=
      G_H.IsSeparation Y Z ∧ A ⊆ Y.vertexSet ∧ B ⊆ Z.vertexSet
    let k₁ := separationOrder Y₁ Z₁
    let k₂ := separationOrder Y₂ Z₂
    (hval_i : ValidSep A₁ B₁ Y₁ Z₁) → (hval_j : ValidSep A₂ B₂ Y₂ Z₂) →
    (hki_min : ∀ Y Z, ValidSep A₁ B₁ Y Z → k₁ ≤ separationOrder Y Z) →
    (hkj_min : ∀ Y Z, ValidSep A₂ B₂ Y Z → k₂ ≤ separationOrder Y Z) →
    (hsize_min : ∀ Y Z, ValidSep A₁ B₁ Y Z → separationOrder Y Z = k₁ →
      Y₁.vertexSet.ncard + Y₁.edgeSet.ncard ≤ Y.vertexSet.ncard + Y.edgeSet.ncard) →
    Y₁ ≤ Y₂ ∧ Z₂ ≤ Z₁ := by
  intro ValidSep k₁ k₂ hval_i hval_j hki_min hkj_min hsize_min
  have hki_eq : separationOrder Y₁ Z₁ = k₁ := rfl
  have hkj_eq : separationOrder Y₂ Z₂ = k₂ := rfl
  have hsep_inter_union : G_H.IsSeparation (Y₁ ∩ Y₂) (Z₁ ∪ Z₂) :=
    (hval_i.1.symm.union_inter hval_j.1.symm).symm
  have hval_iu : ValidSep A₁ B₁ (Y₁ ∩ Y₂) (Z₁ ∪ Z₂) :=
    ⟨hsep_inter_union, subset_inter hval_i.2.1 ((hA).trans hval_j.2.1),
      hval_i.2.2.trans subset_union_left⟩
  have hsep_union_inter : G_H.IsSeparation (Y₁ ∪ Y₂) (Z₁ ∩ Z₂) :=
    hval_i.1.union_inter hval_j.1
  have hval_ui : ValidSep A₂ B₂ (Y₁ ∪ Y₂) (Z₁ ∩ Z₂) :=
    ⟨hsep_union_inter, hval_j.2.1.trans subset_union_right,
      subset_inter ((hB).trans hval_i.2.2) hval_j.2.2⟩
  have hle_ki : k₁ ≤ separationOrder (Y₁ ∩ Y₂) (Z₁ ∪ Z₂) :=
    hki_min _ _ hval_iu
  have hle_kj : k₂ ≤ separationOrder (Y₁ ∪ Y₂) (Z₁ ∩ Z₂) :=
    hkj_min _ _ hval_ui
  have hsubmod := submodular_separationOrder (Y₁) (Z₁) (Y₂) (Z₂)
  have hord_iu_eq : separationOrder (Y₁ ∩ Y₂) (Z₁ ∪ Z₂) = k₁ := by
    omega
  have hsize_le := hsize_min (Y₁ ∩ Y₂) (Z₁ ∪ Z₂) hval_iu hord_iu_eq
  have hle_Yi : Y₁ ∩ Y₂ ≤ Y₁ :=
    GM10.inter_le_left hval_i.1.left_le hval_j.1.left_le
  have hV_le : (Y₁ ∩ Y₂).vertexSet.ncard ≤ (Y₁).vertexSet.ncard :=
    Set.ncard_le_ncard hle_Yi.vertexSet_subset (Y₁).vertexSet_finite
  have hE_le : (Y₁ ∩ Y₂).edgeSet.ncard ≤ (Y₁).edgeSet.ncard :=
    Set.ncard_le_ncard hle_Yi.edgeSet_subset (Y₁).edgeSet_finite
  have hYi_inter_eq : Y₁ ∩ Y₂ = Y₁ :=
    GM10.eq_of_le_of_ncard_eq hle_Yi (by omega) (by omega)
  have hYi_le_Yj : Y₁ ≤ Y₂ := by
    rw [← hYi_inter_eq]
    exact GM10.inter_le_right hval_i.1.left_le hval_j.1.left_le
  refine ⟨hYi_le_Yj, ?_⟩
  rw [hYi_inter_eq] at hord_iu_eq
  have hsub_inter : (Y₁ ∩ Z₁).vertexSet ⊆
      (Y₁ ∩ (Z₁ ∪ Z₂)).vertexSet :=
    inter_subset_inter_right _ subset_union_left
  have hncard_inter_le :
      (Y₁ ∩ (Z₁ ∪ Z₂)).vertexSet.ncard ≤
        (Y₁ ∩ Z₁).vertexSet.ncard := by
    change separationOrder (Y₁) (Z₁ ∪ Z₂) ≤ separationOrder (Y₁) (Z₁)
    omega
  have hinter_eq : (Y₁ ∩ Z₁).vertexSet =
      (Y₁ ∩ (Z₁ ∪ Z₂)).vertexSet :=
    Set.eq_of_subset_of_ncard_le hsub_inter hncard_inter_le
      (Y₁ ∩ (Z₁ ∪ Z₂)).vertexSet_finite
  rw [GM10.le_iff_of_le hval_j.1.right_le hval_i.1.right_le]
  refine ⟨fun v hvZj => ?_, fun e heZj => ?_⟩
  · have hvG : v ∈ G_H.vertexSet := hval_j.1.right_le.vertexSet_subset hvZj
    have hv_union : v ∈ (Y₁).vertexSet ∪ (Z₁).vertexSet :=
      hval_i.1.vertexSet_union.symm ▸ hvG
    rcases hv_union with hvYi | hvZi
    · have hv_in : v ∈ (Y₁ ∩ (Z₁ ∪ Z₂)).vertexSet := ⟨hvYi, Or.inr hvZj⟩
      rw [← hinter_eq] at hv_in
      exact hv_in.2
    · exact hvZi
  · have heG : e ∈ G_H.edgeSet := hval_j.1.right_le.edgeSet_subset heZj
    have he_union : e ∈ (Y₁).edgeSet ∪ (Z₁).edgeSet :=
      hval_i.1.edgeSet_union.symm ▸ heG
    rcases he_union with heYi | heZi
    · have heYj : e ∈ (Y₂).edgeSet := hYi_le_Yj.edgeSet_subset heYi
      exact (hval_j.1.notMem_edgeSet_left heZj heYj).elim
    · exact heZi

/-- Every `ρ`-vortex `(G, Ω)` with clockwise enumeration `t : Fin n → α` (`1 ≤ n`) admits a linear
decomposition `X : Fin n → Graph α β` with respect to `t` of depth `≤ ρ`
(following the proof of Graph Minors IX, (8.1), pages 60–62). -/
theorem exists_isLinearDecomposition_of_isRhoVortex {S : Society α β} {ρ n : ℕ} {t : Fin n → α}
    (hn : 1 ≤ n) (hvortex : IsRhoVortex S ρ) (ht_inj : Injective t)
    (ht_range : range t = S.Ω.bar) (ht_cw : S.Ω.IsClockwiseSeq (List.ofFn t)) :
    ∃ X : Fin n → Graph α β,
      S.IsLinearDecomposition t X ∧
      ∀ i i' : Fin n, i < i' → (V(X i) ∩ V(X i')).ncard ≤ ρ := by
  classical
  let G_H := Hypergraph.ofGraph S.G S.finite_V S.finite_E
  let A_set (j : ℕ) : Set α := {x : α | ∃ i : Fin n, i.1 < j ∧ t i = x}
  let B_set (j : ℕ) : Set α := {x : α | ∃ i : Fin n, j ≤ i.1 ∧ t i = x}
  let ValidSep (j : ℕ) (Y Z : Hypergraph α β) : Prop :=
    G_H.IsSeparation Y Z ∧ A_set j ⊆ Y.vertexSet ∧ B_set j ⊆ Z.vertexSet
  have hA_mono : ∀ {i j : ℕ}, i ≤ j → A_set i ⊆ A_set j := by
    rintro i j hij _ ⟨a, ha, rfl⟩
    exact ⟨a, lt_of_lt_of_le ha hij, rfl⟩
  have hB_anti : ∀ {i j : ℕ}, i ≤ j → B_set j ⊆ B_set i := by
    rintro i j hij _ ⟨a, ha, rfl⟩
    exact ⟨a, le_trans hij ha, rfl⟩
  have hex_valid_sep : ∀ j : ℕ, ∃ Y₀ Z₀, ValidSep j Y₀ Z₀ ∧ separationOrder Y₀ Z₀ ≤ ρ := by
    intro j
    by_cases hj0 : j = 0
    · subst hj0
      refine ⟨⊥, G_H, ⟨isSeparation_bot_self G_H, ?_, ?_⟩, ?_⟩
      · rintro _ ⟨i, hi, rfl⟩; omega
      · rintro _ ⟨i, _, rfl⟩; exact S.bar_subset (ht_range ▸ mem_range_self i)
      · simp [separationOrder, GM10.inter_vertexSet, GM10.bot_vertexSet]
    · by_cases hjn : j < n
      · obtain ⟨Y₀, Z₀, hsep₀, hA₀, hB₀, hord₀⟩ :=
          exists_separation_le_rho_of_isRhoVortex hn hvortex ht_inj ht_range ht_cw
            (Nat.pos_of_ne_zero hj0) hjn
        exact ⟨Y₀, Z₀, ⟨hsep₀, hA₀, hB₀⟩, hord₀⟩
      · refine ⟨G_H, ⊥, ⟨(isSeparation_bot_self G_H).symm, ?_, ?_⟩, ?_⟩
        · rintro _ ⟨i, _, rfl⟩; exact S.bar_subset (ht_range ▸ mem_range_self i)
        · rintro _ ⟨i, hi, rfl⟩; exact absurd i.2 (not_lt_of_ge (le_trans (by omega) hi))
        · simp [separationOrder, GM10.inter_vertexSet, GM10.bot_vertexSet]
  choose Y_min Z_min k_min hval_min hk_eq hk_le hk_min hsize_min using (fun j
    => exists_minimum_separation (hex_valid_sep j))
  let Y (j : ℕ) : Hypergraph α β :=
    if j = 0 then ⊥ else if j < n then Y_min j else G_H
  let Z (j : ℕ) : Hypergraph α β :=
    if j = 0 then G_H else if j < n then Z_min j else ⊥
  have hY0 : Y 0 = ⊥ := ite_eq_left rfl
  have hZ0 : Z 0 = G_H := ite_eq_left rfl
  have hYn : Y n = G_H := by
    dsimp [Y]; rw [ite_eq_right (by omega), ite_eq_right (lt_irrefl n)]
  have hZn : Z n = ⊥ := by
    dsimp [Z]; rw [ite_eq_right (by omega), ite_eq_right (lt_irrefl n)]
  have hYZ_mid : ∀ {j : ℕ}, 1 ≤ j → j < n → Y j = Y_min j ∧ Z j = Z_min j := by
    intro j hj1 hjn
    have hj0 : j ≠ 0 := by omega
    dsimp [Y, Z]
    rw [ite_eq_right hj0, ite_eq_left hjn, ite_eq_right hj0, ite_eq_left hjn]
    exact ⟨rfl, rfl⟩
  have hValid : ∀ j ≤ n, ValidSep j (Y j) (Z j) ∧ separationOrder (Y j) (Z j) ≤ ρ := by
    intro j hjn
    by_cases hj0 : j = 0
    · subst hj0
      rw [hY0, hZ0]
      refine ⟨⟨isSeparation_bot_self G_H, ?_, ?_⟩, ?_⟩
      · rintro _ ⟨i, hi, rfl⟩; omega
      · rintro _ ⟨i, _, rfl⟩; exact S.bar_subset (ht_range ▸ mem_range_self i)
      · simp [separationOrder, GM10.inter_vertexSet, GM10.bot_vertexSet]
    · by_cases hlt : j < n
      · obtain ⟨hY_eq, hZ_eq⟩ := hYZ_mid (by omega) hlt
        rw [hY_eq, hZ_eq]
        exact ⟨hval_min j, hk_eq j ▸ hk_le j⟩
      · have hjeq : j = n := by omega
        subst hjeq
        rw [hYn, hZn]
        refine ⟨⟨(isSeparation_bot_self G_H).symm, ?_, ?_⟩, ?_⟩
        · rintro _ ⟨i, _, rfl⟩; exact S.bar_subset (ht_range ▸ mem_range_self i)
        · rintro _ ⟨i, hi, rfl⟩; exact absurd i.2 (not_lt_of_ge hi)
        · simp [separationOrder, GM10.inter_vertexSet, GM10.bot_vertexSet]
  have hChain : ∀ {i j : ℕ}, i ≤ j → j ≤ n → Y i ≤ Y j ∧ Z j ≤ Z i := by
    intro i j hij hjn
    by_cases hi0 : i = 0
    · subst hi0
      rw [hY0, hZ0]
      exact ⟨bot_le_hypergraph (Y j), (hValid j hjn).1.1.right_le⟩
    · by_cases hjn_eq : j = n
      · subst hjn_eq
        rw [hYn, hZn]
        exact ⟨(hValid i hij).1.1.left_le, bot_le_hypergraph (Z i)⟩
      · have hi1 : 1 ≤ i := by omega
        have hj1 : 1 ≤ j := by omega
        have hj_lt : j < n := by omega
        have hi_lt : i < n := lt_of_le_of_lt hij hj_lt
        obtain ⟨hYi, hZi⟩ := hYZ_mid hi1 hi_lt
        obtain ⟨hYj, hZj⟩ := hYZ_mid hj1 hj_lt
        rw [hYi, hZi, hYj, hZj]
        apply nested_of_minimum_separations (hA_mono hij) (hB_anti hij) (hval_min i) (hval_min j)
        · simpa only [hk_eq i] using hk_min i
        · simpa only [hk_eq j] using hk_min j
        · simpa only [hk_eq i] using hsize_min i
  let X_H (i : Fin n) : Hypergraph α β := Y (i.1 + 1) ∩ Z i.1
  have hXH_le : ∀ i : Fin n, X_H i ≤ G_H := fun i =>
    GM10.inter_le (hValid (i.1 + 1) (by omega)).1.1.left_le
      (hValid i.1 (le_of_lt i.2)).1.1.right_le
  let X (i : Fin n) : Graph α β := subgraphOfSubhypergraph S.G (X_H i)
  have hX_le : ∀ i : Fin n, X i ≤ S.G := fun i => subgraphOfSubhypergraph_le (hXH_le i)
  refine ⟨X, ⟨ht_inj, ht_range, ht_cw, hX_le, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have hV_eq : (⋃ P ∈ range X, V(P)) = V(S.G) := by
      ext v
      simp only [mem_iUnion, mem_range, exists_prop]
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, hv⟩
        exact (hX_le i).vertexSet_mono hv
      · intro hv
        have hex_k : ∃ k : ℕ, k ≤ n ∧ v ∈ (Y k).vertexSet :=
          ⟨n, le_rfl, by rw [hYn]; exact hv⟩
        let k := Nat.find hex_k
        have hk_spec : k ≤ n ∧ v ∈ (Y k).vertexSet := Nat.find_spec hex_k
        have hk_pos : 1 ≤ k := by
          by_contra h0
          have hk0 : k = 0 := by omega
          have hv0 : v ∈ (Y 0).vertexSet := hk0 ▸ hk_spec.2
          rw [hY0] at hv0
          exact hv0
        have hnot_prev : ¬ (k - 1 ≤ n ∧ v ∈ (Y (k - 1)).vertexSet) :=
          Nat.find_min hex_k (by omega)
        have hv_not_Y : v ∉ (Y (k - 1)).vertexSet := fun h => hnot_prev ⟨by omega, h⟩
        have hv_union : v ∈ (Y (k - 1)).vertexSet ∪ (Z (k - 1)).vertexSet :=
          (hValid (k - 1) (by omega)).1.1.vertexSet_union.symm ▸ hv
        have hv_Z : v ∈ (Z (k - 1)).vertexSet := hv_union.resolve_left hv_not_Y
        have hk_lt : k - 1 < n := by omega
        refine ⟨X ⟨k - 1, hk_lt⟩, ⟨⟨k - 1, hk_lt⟩, rfl⟩, ?_⟩
        change v ∈ (Y (k - 1 + 1)).vertexSet ∧ v ∈ (Z (k - 1)).vertexSet
        rw [Nat.sub_add_cancel hk_pos]
        exact ⟨hk_spec.2, hv_Z⟩
    have hE_eq : (⋃ P ∈ range X, E(P)) = E(S.G) := by
      ext e
      simp only [mem_iUnion, mem_range, exists_prop]
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, he⟩
        exact (hX_le i).edgeSet_mono he
      · intro he
        have hex_k : ∃ k : ℕ, k ≤ n ∧ e ∈ (Y k).edgeSet :=
          ⟨n, le_rfl, by rw [hYn]; exact he⟩
        let k := Nat.find hex_k
        have hk_spec : k ≤ n ∧ e ∈ (Y k).edgeSet := Nat.find_spec hex_k
        have hk_pos : 1 ≤ k := by
          by_contra h0
          have hk0 : k = 0 := by omega
          have he0 : e ∈ (Y 0).edgeSet := hk0 ▸ hk_spec.2
          rw [hY0] at he0
          exact he0
        have hnot_prev : ¬ (k - 1 ≤ n ∧ e ∈ (Y (k - 1)).edgeSet) :=
          Nat.find_min hex_k (by omega)
        have he_not_Y : e ∉ (Y (k - 1)).edgeSet := fun h => hnot_prev ⟨by omega, h⟩
        have he_union : e ∈ (Y (k - 1)).edgeSet ∪ (Z (k - 1)).edgeSet :=
          (hValid (k - 1) (by omega)).1.1.edgeSet_union.symm ▸ he
        have he_Z : e ∈ (Z (k - 1)).edgeSet := he_union.resolve_left he_not_Y
        have hk_lt : k - 1 < n := by omega
        refine ⟨X ⟨k - 1, hk_lt⟩, ⟨⟨k - 1, hk_lt⟩, rfl⟩, ?_⟩
        rw [edgeSet_subgraphOfSubhypergraph (hXH_le ⟨k - 1, hk_lt⟩)]
        change e ∈ (Y (k - 1 + 1)).edgeSet ∧ e ∈ (Z (k - 1)).edgeSet
        rw [Nat.sub_add_cancel hk_pos]
        exact ⟨hk_spec.2, he_Z⟩
    have hU_le : subgraphSUnion S.G (range X) ≤ S.G :=
      restrict_le.trans (S.G.induce_le (by rw [hV_eq]))
    refine (Compatible.of_le_le hU_le le_rfl).ext ?_ ?_
    · simpa [subgraphSUnion] using hV_eq
    · ext e
      simp only [subgraphSUnion, edgeSet_restrict, mem_inter_iff, Graph.edgeSet_induce, hV_eq,
        hE_eq]
      refine ⟨fun h => h.2, fun he => ⟨?_, he⟩⟩
      obtain ⟨x, y, hlink⟩ := exists_isLink_of_mem_edgeSet he
      exact ⟨x, y, hlink, hlink.left_mem, hlink.right_mem⟩
  · intro i i' hii'
    rw [edgeSet_subgraphOfSubhypergraph (hXH_le i),
      edgeSet_subgraphOfSubhypergraph (hXH_le i'), Set.disjoint_left]
    rintro e ⟨heY, _⟩ ⟨_, heZ⟩
    have hZ_le : Z i'.1 ≤ Z (i.1 + 1) := (hChain (by omega) (le_of_lt i'.2)).2
    have heZ' : e ∈ (Z (i.1 + 1)).edgeSet := hZ_le.edgeSet_subset heZ
    exact (hValid (i.1 + 1) (by omega)).1.1.notMem_edgeSet_right heY heZ'
  · intro i
    exact ⟨(hValid (i.1 + 1) (by omega)).1.2.1 ⟨i, Nat.lt_succ_self i.1, rfl⟩,
      (hValid i.1 (le_of_lt i.2)).1.2.2 ⟨i, le_rfl, rfl⟩⟩
  · intro i i' i'' hii' hi'i''
    have hY_le : Y (i.1 + 1) ≤ Y (i'.1 + 1) :=
      (hChain (Nat.add_le_add_right hii' 1) (by omega)).1
    have hZ_le : Z i''.1 ≤ Z i'.1 :=
      (hChain hi'i'' (le_of_lt i''.2)).2
    have hV_sub : V(X i) ∩ V(X i'') ⊆ V(X i') := by
      rintro v ⟨⟨hvY, _⟩, ⟨_, hvZ⟩⟩
      exact ⟨hY_le.vertexSet_subset hvY, hZ_le.vertexSet_subset hvZ⟩
    have hE_sub : E(X i) ∩ E(X i'') ⊆ E(X i') := by
      rw [edgeSet_subgraphOfSubhypergraph (hXH_le i),
        edgeSet_subgraphOfSubhypergraph (hXH_le i''),
        edgeSet_subgraphOfSubhypergraph (hXH_le i')]
      rintro e ⟨⟨heY, _⟩, ⟨_, heZ⟩⟩
      exact ⟨hY_le.edgeSet_subset heY, hZ_le.edgeSet_subset heZ⟩
    have hinter_le : subgraphInter S.G (X i) (X i'') ≤ S.G :=
      restrict_le.trans (S.G.induce_le (inter_subset_left.trans (hX_le i).vertexSet_mono))
    rw [(Compatible.of_le_le hinter_le (hX_le i')).le_iff]
    refine ⟨hV_sub, ?_⟩
    exact (edgeSet_restrict _ _).trans_subset (inter_subset_right.trans hE_sub)
  · intro i i' hii'
    have hZ_le : Z i'.1 ≤ Z (i.1 + 1) := (hChain (by omega) (le_of_lt i'.2)).2
    have hsub : V(X i) ∩ V(X i') ⊆ (Y (i.1 + 1) ∩ Z (i.1 + 1)).vertexSet := by
      rintro v ⟨⟨hvY, _⟩, ⟨_, hvZ⟩⟩
      exact ⟨hvY, hZ_le.vertexSet_subset hvZ⟩
    exact (Set.ncard_le_ncard hsub (Y (i.1 + 1) ∩ Z (i.1 + 1)).vertexSet_finite).trans
      (hValid (i.1 + 1) (by omega)).2

/-- `V(A_{i-1} ∩ A_i)` in the proof of Graph Minors XVI, (3.2) (page 50), with `A_0` null. -/
def vortexPrevInter {n : ℕ} (A : Fin n → Graph α β) (i : Fin n) : Set α :=
  if h : 0 < i.1 then V(A ⟨i.1 - 1, by omega⟩) ∩ V(A i) else ∅

/-- `V(A_i ∩ A_{i+1})` in the proof of Graph Minors XVI, (3.2) (page 50), with `A_{n+1}` null. -/
def vortexNextInter {n : ℕ} (A : Fin n → Graph α β) (i : Fin n) : Set α :=
  if h : i.1 + 1 < n then V(A i) ∩ V(A ⟨i.1 + 1, h⟩) else ∅

/-- The separator `V(A_{i-1} ∩ A_i) ∪ V(A_i ∩ A_{i+1}) ∪ {t_i}` in the proof of Graph Minors XVI,
(3.2) (page 50). -/
def vortexSepSet {n : ℕ} (t : Fin n → α) (A : Fin n → Graph α β) (i : Fin n) : Set α :=
  vortexPrevInter A i ∪ vortexNextInter A i ∪ {t i}

/-- The subgraph `B_i` in the proof of Graph Minors XVI, (3.2) (page 50). -/
def vortexRightSubgraph (G : Graph α β) {n : ℕ} (t : Fin n → α) (A : Fin n → Graph α β)
    (i : Fin n) : Graph α β :=
  (G.induce ((V(G) \ V(A i)) ∪ vortexSepSet t A i)).restrict (E(G) \ E(A i))

private lemma vortexSepSet_subset_A {S : Society α β} {n : ℕ} {t : Fin n → α}
    {A : Fin n → Graph α β} (hLD : S.IsLinearDecomposition t A) (i : Fin n) :
    vortexSepSet t A i ⊆ V(A i) := by
  refine union_subset (union_subset ?_ ?_) (singleton_subset_iff.mpr (hLD.mem_vertexSet i))
  · unfold vortexPrevInter
    split_ifs with h
    · exact inter_subset_right
    · exact empty_subset _
  · unfold vortexNextInter
    split_ifs with h
    · exact inter_subset_left
    · exact empty_subset _

private lemma inter_subset_vortexSepSet {S : Society α β} {n : ℕ} {t : Fin n → α}
    {A : Fin n → Graph α β} (hLD : S.IsLinearDecomposition t A) {i j : Fin n} (hij : i ≠ j) :
    V(A i) ∩ V(A j) ⊆ vortexSepSet t A i := by
  intro v ⟨hvi, hvj⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · left; right
    unfold vortexNextInter
    have hnext : i.1 + 1 < n := by omega
    rw [dite_eq_left hnext]
    have hle1 : i ≤ ⟨i.1 + 1, hnext⟩ := Fin.mk_le_mk.mpr (by omega)
    have hle2 : (⟨i.1 + 1, hnext⟩ : Fin n) ≤ j := Fin.mk_le_mk.mpr (by omega)
    have hv_mid : v ∈ V(A ⟨i.1 + 1, hnext⟩) :=
      (hLD.inter_le i ⟨i.1 + 1, hnext⟩ j hle1 hle2).vertexSet_mono ⟨hvi, hvj⟩
    exact ⟨hvi, hv_mid⟩
  · left; left
    unfold vortexPrevInter
    have hprev : 0 < i.1 := by omega
    rw [dite_eq_left hprev]
    have hle1 : j ≤ ⟨i.1 - 1, by omega⟩ := Fin.mk_le_mk.mpr (by omega)
    have hle2 : (⟨i.1 - 1, by omega⟩ : Fin n) ≤ i := Fin.mk_le_mk.mpr (by omega)
    have hv_mid : v ∈ V(A ⟨i.1 - 1, by omega⟩) :=
      (hLD.inter_le j ⟨i.1 - 1, by omega⟩ i hle1 hle2).vertexSet_mono ⟨hvj, hvi⟩
    exact ⟨hv_mid, hvi⟩

private lemma isGraphSeparation_vortexRightSubgraph {S : Society α β} {n : ℕ} {t : Fin n → α}
    {A : Fin n → Graph α β} (hLD : S.IsLinearDecomposition t A) (i : Fin n) :
    IsGraphSeparation S.G (A i) (vortexRightSubgraph S.G t A i) ∧
    V(A i) ∩ V(vortexRightSubgraph S.G t A i) = vortexSepSet t A i ∧
    E(vortexRightSubgraph S.G t A i) = E(S.G) \ E(A i) := by
  let B_i := vortexRightSubgraph S.G t A i
  have hsep_sub_A : vortexSepSet t A i ⊆ V(A i) := vortexSepSet_subset_A hLD i
  have hAi_sub_G : V(A i) ⊆ V(S.G) := (hLD.le_G i).vertexSet_mono
  have hVB_sub_G : (V(S.G) \ V(A i)) ∪ vortexSepSet t A i ⊆ V(S.G) :=
    union_subset sdiff_subset (hsep_sub_A.trans hAi_sub_G)
  have hBi_le : B_i ≤ S.G := restrict_le.trans (S.G.induce_le hVB_sub_G)
  have hV_inter : V(A i) ∩ V(B_i) = vortexSepSet t A i := by
    ext v
    simp only [B_i, vortexRightSubgraph, vertexSet_restrict, vertexSet_induce, mem_inter_iff,
      mem_union, mem_sdiff]
    exact ⟨fun ⟨hvA, h⟩ => h.elim (fun ⟨_, hnot⟩ => (hnot hvA).elim) id,
      fun hvS => ⟨hsep_sub_A hvS, Or.inr hvS⟩⟩
  have hV_union : V(A i) ∪ V(B_i) = V(S.G) := by
    ext v
    simp only [B_i, vortexRightSubgraph, vertexSet_restrict, vertexSet_induce, mem_union, mem_sdiff]
    constructor
    · rintro (hvA | (⟨hvG, _⟩ | hvS))
      · exact hAi_sub_G hvA
      · exact hvG
      · exact hAi_sub_G (hsep_sub_A hvS)
    · intro hvG
      by_cases hvA : v ∈ V(A i)
      · exact Or.inl hvA
      · exact Or.inr (Or.inl ⟨hvG, hvA⟩)
  have hE_Bi : E(B_i) = E(S.G) \ E(A i) := by
    ext e
    simp only [B_i, vortexRightSubgraph, edgeSet_restrict, mem_inter_iff, Graph.edgeSet_induce]
    refine ⟨fun h => h.2, fun ⟨heG, he_not_Ai⟩ => ⟨?_, heG, he_not_Ai⟩⟩
    have he_union : e ∈ E(subgraphSUnion S.G (range A)) := hLD.union_eq.symm ▸ heG
    simp only [subgraphSUnion, edgeSet_restrict, mem_inter_iff, mem_iUnion, mem_range,
      exists_prop] at he_union
    obtain ⟨_, ⟨j, rfl⟩, heAj⟩ := he_union.2
    have hij : i ≠ j := fun h => he_not_Ai (h ▸ heAj)
    obtain ⟨x, y, hlink⟩ := exists_isLink_of_mem_edgeSet heG
    have hlink_j : (A j).IsLink e x y := ((hLD.le_G j).isLink_iff heAj).mpr hlink
    have hx_Bi : x ∈ (V(S.G) \ V(A i)) ∪ vortexSepSet t A i := by
      by_cases hxA : x ∈ V(A i)
      · exact Or.inr (inter_subset_vortexSepSet hLD hij ⟨hxA, hlink_j.left_mem⟩)
      · exact Or.inl ⟨hlink.left_mem, hxA⟩
    have hy_Bi : y ∈ (V(S.G) \ V(A i)) ∪ vortexSepSet t A i := by
      by_cases hyA : y ∈ V(A i)
      · exact Or.inr (inter_subset_vortexSepSet hLD hij ⟨hyA, hlink_j.right_mem⟩)
      · exact Or.inl ⟨hlink.right_mem, hyA⟩
    exact ⟨x, y, hlink, hx_Bi, hy_Bi⟩
  have hE_union : E(A i) ∪ E(B_i) = E(S.G) := by
    rw [hE_Bi]
    ext e
    exact ⟨fun h => h.elim (fun he => (hLD.le_G i).edgeSet_mono he) (fun he => he.1),
      fun he => by by_cases h : e ∈ E(A i) <;> [exact Or.inl h; exact Or.inr ⟨he, h⟩]⟩
  have hE_disj : Disjoint E(A i) E(B_i) := by
    rw [hE_Bi]
    exact disjoint_sdiff_self_right
  exact ⟨⟨hLD.le_G i, hBi_le, hV_union, hE_union, hE_disj⟩, hV_inter, hE_Bi⟩

/-- Claim (1) in the proof of Graph Minors XVI, (3.2) (page 50):
"(1) $A_i \subseteq B_j$ for $1 \le i, j \le n$ with $i \ne j$." -/
theorem lemma_3_2_claim_1 {S : Society α β} {n : ℕ} {t : Fin n → α}
    {A : Fin n → Graph α β} (hLD : S.IsLinearDecomposition t A)
    {i j : Fin n} (hij : i ≠ j) :
    A i ≤ vortexRightSubgraph S.G t A j := by
  obtain ⟨hsep_j, _, hEB_j⟩ := isGraphSeparation_vortexRightSubgraph hLD j
  rw [(Compatible.of_le_le (hLD.le_G i) hsep_j.2.1).le_iff]
  refine ⟨fun v hvAi => ?_, fun e heAi => ?_⟩
  · by_cases hvAj : v ∈ V(A j)
    · exact Or.inr (inter_subset_vortexSepSet hLD hij.symm ⟨hvAj, hvAi⟩)
    · exact Or.inl ⟨(hLD.le_G i).vertexSet_mono hvAi, hvAj⟩
  · rw [hEB_j]
    refine ⟨(hLD.le_G i).edgeSet_mono heAi, ?_⟩
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact Set.disjoint_left.mp (hLD.edge_disjoint i j hlt) heAi
    · exact Set.disjoint_right.mp (hLD.edge_disjoint j i hgt) heAi

/-- Claim (2) in the proof of Graph Minors XVI, (3.2) (page 50):
"(2) $t_i \in V(B_j)$ for $1 \le i, j \le n$." -/
theorem lemma_3_2_claim_2 {S : Society α β} {n : ℕ} {t : Fin n → α}
    {A : Fin n → Graph α β} (hLD : S.IsLinearDecomposition t A)
    (i j : Fin n) :
    t i ∈ V(vortexRightSubgraph S.G t A j) := by
  by_cases hij : i = j
  · subst hij
    exact Or.inr (Or.inr (mem_singleton (t i)))
  · exact (lemma_3_2_claim_1 hLD hij).vertexSet_mono (hLD.mem_vertexSet i)

/-- Claim (3) in the proof of Graph Minors XVI, (3.2) (pages 50–51):
"(3) $X_i \cap X_k \subseteq X_j$ for $1 \le i \le j \le k \le n$." -/
theorem lemma_3_2_claim_3 {S : Society α β} {n : ℕ} {t : Fin n → α}
    {A : Fin n → Graph α β} (hLD : S.IsLinearDecomposition t A)
    {i j k : Fin n} (hij : i ≤ j) (hjk : j ≤ k) :
    (V(A i) ∩ V(vortexRightSubgraph S.G t A i)) ∩
      (V(A k) ∩ V(vortexRightSubgraph S.G t A k)) ⊆
      V(A j) ∩ V(vortexRightSubgraph S.G t A j) := by
  rintro v ⟨⟨hvAi, hvBi⟩, ⟨hvAk, _⟩⟩
  by_cases hji : j = i
  · subst hji
    exact ⟨hvAi, hvBi⟩
  · have hij_ne : i ≠ j := Ne.symm hji
    have hvAj : v ∈ V(A j) := (hLD.inter_le i j k hij hjk).vertexSet_mono ⟨hvAi, hvAk⟩
    have hvBj : v ∈ V(vortexRightSubgraph S.G t A j) :=
      (lemma_3_2_claim_1 hLD hij_ne).vertexSet_mono hvAi
    exact ⟨hvAj, hvBj⟩

/-- **Graph Minors XVI, (3.2)** (page 50):
"Let $(G, \Omega)$ be a $\rho$-vortex, and let the vertices in $\bar{\Omega}$ be $t_1, \ldots, t_n$
in order, where $n \ge 1$. Then there are separations $(A_1, B_1), \ldots, (A_n, B_n)$ of $G$, such
that:
1. $t_1, \ldots, t_n \in V(B_i)$ for $1 \le i \le n$,
2. $t_i \in V(A_i)$ for $1 \le i \le n$,
3. $\mathscr{L} = \{(A_1, B_1), \ldots, (A_n, B_n)\}$ is a location in $G$,
4. $(A_i, B_i)$ has order $\le 2\rho + 1$ for $1 \le i \le n$, and
5. every torso of the design of $\mathscr{L}$ is a $(2\rho + 1)$-ring with perimeter
$t_1, \ldots, t_n$." -/
theorem theorem_3_2_with_edge_cover :
    ∀ {α : Type u} {β : Type v} (S : Society α β) (ρ n : ℕ) (t : Fin n → α),
    1 ≤ n → IsRhoVortex S ρ →
    Injective t → range t = S.Ω.bar → S.Ω.IsClockwiseSeq (List.ofFn t) →
    ∃ A B : Fin n → Graph α β,
      (∀ i : Fin n, IsGraphSeparation S.G (A i) (B i)) ∧
      (∀ i j : Fin n, t j ∈ V(B i)) ∧
      (∀ i : Fin n, t i ∈ V(A i)) ∧
      IsGraphLocation S.G (range fun i : Fin n => (A i, B i)) ∧
      (∀ i : Fin n, (V(A i) ∩ V(B i)).ncard ≤ 2 * ρ + 1) ∧
      (∀ x ∈ V(S.G), ∃ i, x ∈ V(A i)) ∧
      (∀ e ∈ E(S.G), ∃ i, e ∈ E(A i)) ∧
      (∀ H' : Graph α β,
        IsTorsoOfDesign (graphLocationDesign S.G (range fun i : Fin n => (A i, B i))) H' →
        IsRRing H' (2 * ρ + 1) (List.ofFn t)) := by
  intro α β S ρ n t hn hvortex ht_inj ht_range ht_cw
  obtain ⟨A, hLD, hdepth⟩ :=
    exists_isLinearDecomposition_of_isRhoVortex hn hvortex ht_inj ht_range ht_cw
  let B : Fin n → Graph α β := vortexRightSubgraph S.G t A
  have hsep_B : ∀ i : Fin n,
      IsGraphSeparation S.G (A i) (B i) ∧
      V(A i) ∩ V(B i) = vortexSepSet t A i ∧
      E(B i) = E(S.G) \ E(A i) :=
    isGraphSeparation_vortexRightSubgraph hLD
  have hord_le : ∀ i : Fin n, (V(A i) ∩ V(B i)).ncard ≤ 2 * ρ + 1 := by
    intro i
    rw [(hsep_B i).2.1]
    unfold vortexSepSet
    have hprev_fin : (vortexPrevInter A i).Finite := by
      unfold vortexPrevInter
      split_ifs with h
      · exact S.finite_V.subset (inter_subset_right.trans (hLD.le_G i).vertexSet_mono)
      · exact finite_empty
    have hnext_fin : (vortexNextInter A i).Finite := by
      unfold vortexNextInter
      split_ifs with h
      · exact S.finite_V.subset (inter_subset_left.trans (hLD.le_G i).vertexSet_mono)
      · exact finite_empty
    have hprev_le : (vortexPrevInter A i).ncard ≤ ρ := by
      unfold vortexPrevInter
      split_ifs with h
      · exact hdepth ⟨i.1 - 1, by omega⟩ i (Fin.mk_lt_mk.mpr (by omega))
      · simp
    have hnext_le : (vortexNextInter A i).ncard ≤ ρ := by
      unfold vortexNextInter
      split_ifs with h
      · exact hdepth i ⟨i.1 + 1, h⟩ (Fin.mk_lt_mk.mpr (by omega))
      · simp
    have h1 := Set.ncard_union_le (vortexPrevInter A i ∪ vortexNextInter A i) {t i}
    have h2 := Set.ncard_union_le (vortexPrevInter A i) (vortexNextInter A i)
    have h3 : ({t i} : Set α).ncard = 1 := Set.ncard_singleton (t i)
    omega
  have hloc : IsGraphLocation S.G (range fun i : Fin n => (A i, B i)) := by
    refine ⟨finite_range _, ?_, ?_⟩
    · rintro _ ⟨i, rfl⟩
      exact (hsep_B i).1
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
      have hij : i ≠ j := fun h => hne (congrArg (fun k => (A k, B k)) h)
      exact lemma_3_2_claim_1 hLD hij
  have hVertexCover : ∀ x ∈ V(S.G), ∃ i, x ∈ V(A i) := by
    intro x hx
    have hxUnion : x ∈ V(subgraphSUnion S.G (range A)) := hLD.union_eq.symm ▸ hx
    obtain ⟨_, ⟨i, rfl⟩, hxi⟩ := mem_iUnion₂.mp hxUnion
    exact ⟨i, hxi⟩
  have hCover : ∀ e ∈ E(S.G), ∃ i, e ∈ E(A i) := by
    intro e he
    have heUnion : e ∈ E(subgraphSUnion S.G (range A)) := hLD.union_eq.symm ▸ he
    rw [edgeSet_subgraphSUnion (by rintro _ ⟨i, rfl⟩; exact hLD.le_G i)] at heUnion
    obtain ⟨_, ⟨i, rfl⟩, hei⟩ := mem_iUnion₂.mp heUnion
    exact ⟨i, hei⟩
  refine ⟨A, B, fun i => (hsep_B i).1, fun i j => lemma_3_2_claim_2 hLD j i,
    hLD.mem_vertexSet, hloc, hord_le, hVertexCover, hCover, ?_⟩
  intro H' htorso
  let ℒ := range fun i : Fin n => (A i, B i)
  have hcore_V : V(graphLocationCore S.G ℒ) = ⋃ i : Fin n, (V(A i) ∩ V(B i)) := by
    ext v
    simp only [graphLocationCore, ℒ, vertexSet_restrict, vertexSet_induce, Set.mem_ofPred_eq,
      mem_range, forall_exists_index, forall_apply_eq_imp_iff, mem_iUnion, mem_inter_iff]
    constructor
    · rintro ⟨hvG, hall⟩
      have hv_union : v ∈ V(subgraphSUnion S.G (range A)) := hLD.union_eq.symm ▸ hvG
      simp only [subgraphSUnion, vertexSet_restrict, vertexSet_induce, mem_iUnion, mem_range,
        exists_prop] at hv_union
      obtain ⟨_, ⟨i, rfl⟩, hvAi⟩ := hv_union
      exact ⟨i, hvAi, hall i⟩
    · rintro ⟨i, hvAi, hvBi⟩
      refine ⟨(hLD.le_G i).vertexSet_mono hvAi, fun j => ?_⟩
      by_cases hij : i = j
      · exact hij ▸ hvBi
      · exact (lemma_3_2_claim_1 hLD hij).vertexSet_mono hvAi
  have hcore_E : E(graphLocationCore S.G ℒ) = ∅ := by
    ext e
    simp only [graphLocationCore, ℒ, edgeSet_restrict, mem_inter_iff, Graph.edgeSet_induce,
      Set.mem_ofPred_eq, mem_range, forall_exists_index, forall_apply_eq_imp_iff,
      mem_empty_iff_false, iff_false]
    rintro ⟨_, heG, hall⟩
    have he_union : e ∈ E(subgraphSUnion S.G (range A)) := hLD.union_eq.symm ▸ heG
    simp only [subgraphSUnion, edgeSet_restrict, mem_inter_iff, mem_iUnion, mem_range,
      exists_prop] at he_union
    obtain ⟨_, ⟨i, rfl⟩, heAi⟩ := he_union.2
    have heBi : e ∈ E(B i) := hall i
    rw [(hsep_B i).2.2] at heBi
    exact heBi.2 heAi
  have hVH' : V(H') = ⋃ i : Fin n, (V(A i) ∩ V(B i)) := htorso.1.symm.trans hcore_V
  let castFin (i : Fin (List.ofFn t).length) : Fin n := i.cast (List.length_ofFn)
  let X_ring (i : Fin (List.ofFn t).length) : Set α :=
    V(A (castFin i)) ∩ V(B (castFin i))
  refine ⟨ht_cw.1, ?_, X_ring, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [List.mem_ofFn] at hx
    rcases hx with ⟨i, rfl⟩
    rw [hVH', mem_iUnion]
    exact ⟨i, hLD.mem_vertexSet i, lemma_3_2_claim_2 hLD i i⟩
  · intro i
    rw [hVH']
    exact subset_iUnion (fun k : Fin n => V(A k) ∩ V(B k)) (castFin i)
  · rw [hVH']
    ext v
    simp only [mem_iUnion, X_ring, castFin]
    exact ⟨fun ⟨i, hv⟩ => ⟨i.cast (List.length_ofFn), hv⟩,
      fun ⟨k, hv⟩ => ⟨k.cast (List.length_ofFn).symm, hv⟩⟩
  · intro e heH'
    have he_diff : e ∈ E(H') \ E(graphLocationCore S.G ℒ) := by
      rw [hcore_E]
      exact ⟨heH', notMem_empty e⟩
    obtain ⟨X, hX_mem, hends⟩ := htorso.2.2 e he_diff
    simp only [graphLocationDesign, mem_image, mem_range, exists_exists_eq_and] at hX_mem
    rcases hX_mem with ⟨k, rfl⟩
    refine ⟨k.cast (List.length_ofFn).symm, fun v hv => ?_⟩
    simpa [X_ring, castFin] using hends v hv
  · intro i
    simp only [List.getElem_ofFn, X_ring, castFin]
    exact ⟨hLD.mem_vertexSet (castFin i), lemma_3_2_claim_2 hLD (castFin i) (castFin i)⟩
  · intro i j k hij hjk
    exact lemma_3_2_claim_3 hLD (Fin.mk_le_mk.mpr (Fin.mk_le_mk.mp hij))
      (Fin.mk_le_mk.mpr (Fin.mk_le_mk.mp hjk))
  · intro i
    exact hord_le (castFin i)

/-- Graph Minors XVI, (3.2), page 50, by the paper's linear
 decomposition and the separator sets of consecutive pieces. -/
theorem theorem_3_2_proof : GM16Theorem32Statement.{u, v} := by
  intro α β S ρ n t hn hvortex ht_inj ht_range ht_cw
  obtain ⟨A, B, hsep, hbd, hmem, hloc, hord, _, _, htorso⟩ :=
    theorem_3_2_with_edge_cover S ρ n t hn hvortex ht_inj ht_range ht_cw
  exact ⟨A, B, hsep, hbd, hmem, hloc, hord, htorso⟩

end GraphMinor.GM16
