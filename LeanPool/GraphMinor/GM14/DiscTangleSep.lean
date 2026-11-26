/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Section3
import LeanPool.GraphMinor.GM14.Section10Translation1
import LeanPool.GraphMinor.GM14.Section7a
import LeanPool.GraphMinor.GM11.Section64b
import LeanPool.GraphMinor.GM11.Section91
import LeanPool.GraphMinor.GM11.CitedResults

/-!
# Tangle Separations and Distance Bounds for Non-Normal Discs and Closed Curves

This file proves two general lemmas connecting intersections with `U(H)` (without any
`H`-normality or `O`-arc restriction) to respectful tangles and their metrics on a connected
closed non-spherical surface `S`:

- `disc_sep_mem_tangle`: for a 2-cell drawing `Γ` with `Γ.E.Nonempty` and a respectful tangle `T`
  of order `θ > 15`, any closed disc `Δ ⊆ S` with `(subBd Δ ∩ Γ.U).Finite` and
  `(subBd Δ ∩ Γ.U).ncard ≤ 3` induces a separation `(A, B) ∈ T` of `Γ.toHypergraph` with
  `A.vertexSet = Γ.V ∩ Δ` and `separationOrder A B ≤ (subBd Δ ∩ Γ.U).ncard`.
- `not_exists_curve_of_dist_ge_twelve`: if `H` has tangle metric `d` of order `θ > 15` with
  `H.E.Nonempty` and `u, v ∈ H.V` satisfy `¬ d {u} {v} < 12`, then there is no continuous closed
  curve `φ : C(Circle, S)` with `(range φ ∩ H.U).encard ≤ 3`, `u ∈ curveIns φ`, and
  `v ∈ curveIns φ`.

These supply the boundary-intersection and curve-enclosure steps for Graph Minors XIV,
`(1.1)(iii)(iii)` and `(1.1)(ii)` (pages 24–25).
-/

namespace GraphMinor.GM14

open Set Function Topology Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM10
open GraphMinor.GM11 GraphMinor.GM14.Whitney

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-! ## 1. Edge Ends, Boundary Counts, and Small Edge-Set Separations -/

omit [T2Space S] in
private theorem closure_inter_V_nonempty_and_ncard_le_two {Γ : Drawing S} {e : Set S}
    (he : e ∈ Γ.E) :
    (closure e ∩ Γ.V).Nonempty ∧ (closure e ∩ Γ.V).ncard ≤ 2 := by
  rcases Γ.edge_cond e he with ⟨u, v, huv, hcap, -⟩ | ⟨u, hcap, -⟩
  · rw [hcap]
    exact ⟨⟨u, Or.inl rfl⟩, by rw [ncard_pair huv]⟩
  · rw [hcap]
    exact ⟨⟨u, rfl⟩, by rw [ncard_singleton]; omega⟩

omit [T2Space S] in
private theorem closure_inter_V_inter_ncard_le_one {Γ : Drawing S} {e Δ : Set S}
    (he : e ∈ Γ.E) (hnot : ¬ (closure e ∩ Γ.V ⊆ Δ)) :
    ((closure e ∩ Γ.V) ∩ Δ).ncard ≤ 1 := by
  rcases Γ.edge_cond e he with ⟨u, v, _, hcap, -⟩ | ⟨u, hcap, -⟩
  · rw [hcap] at hnot ⊢
    by_cases hu : u ∈ Δ
    · have hv : v ∉ Δ := fun hv => hnot (by rintro z (rfl | rfl) <;> assumption)
      have hsub : ({u, v} : Set S) ∩ Δ ⊆ {u} := by
        rintro z ⟨rfl | rfl, hzΔ⟩
        · rfl
        · exact absurd hzΔ hv
      exact (ncard_le_ncard hsub (finite_singleton u)).trans (by rw [ncard_singleton])
    · have hsub : ({u, v} : Set S) ∩ Δ ⊆ {v} := by
        rintro z ⟨rfl | rfl, hzΔ⟩
        · exact absurd hzΔ hu
        · rfl
      exact (ncard_le_ncard hsub (finite_singleton v)).trans (by rw [ncard_singleton])
  · rw [hcap] at hnot ⊢
    have hu : u ∉ Δ := fun hu => hnot (singleton_subset_iff.mpr hu)
    have hemp : ({u} : Set S) ∩ Δ = ∅ := by
      ext z
      simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
      rintro rfl
      exact hu
    rw [hemp, ncard_empty]
    omega

omit [T2Space S] in
private theorem ends_subset_closure_inter_V {Γ : Drawing S} {e : Set S} :
    Γ.toHypergraph.ends e ⊆ closure e ∩ Γ.V := by
  intro v hv
  have h := (PaintingOrDrawing.toHypergraph_inc (Γ := PaintingOrDrawing.drawing Γ)).mp hv
  exact ⟨h.2.2, h.2.1⟩

omit [T2Space S] in
private theorem ends_ncard_le_two {Γ : Drawing S} {e : Set S} (he : e ∈ Γ.E) :
    (Γ.toHypergraph.ends e).ncard ≤ 2 :=
  (ncard_le_ncard ends_subset_closure_inter_V (Γ.finite_V.subset inter_subset_right)).trans
    (closure_inter_V_nonempty_and_ncard_le_two he).2

omit [T2Space S] in
/-- For a subset `X ⊆ S` such that `(X ∩ Γ.U).Finite`, the number of vertices of `Γ` in `X` plus
the number of edges of `Γ` meeting `X` is at most `(X ∩ Γ.U).ncard`. -/
private theorem bd_verts_add_edges_ncard_le {Γ : Drawing S} {X : Set S}
    (hfin : (X ∩ Γ.U).Finite) :
    (X ∩ Γ.V).ncard + {e ∈ Γ.E | (e ∩ X).Nonempty}.ncard ≤ (X ∩ Γ.U).ncard := by
  classical
  set V_bd := X ∩ Γ.V
  set E_bd := {e ∈ Γ.E | (e ∩ X).Nonempty}
  have hE_fin : E_bd.Finite := Γ.finite_edges.subset fun _ h => h.1
  by_cases hE_ne : E_bd.Nonempty
  · obtain ⟨e₀, he₀⟩ := hE_ne
    obtain ⟨p₀, hp₀e, _⟩ := he₀.2
    let f : Set S → S := fun e => if h : (e ∩ X).Nonempty then h.choose else p₀
    have hf_spec : ∀ {e}, e ∈ E_bd → f e ∈ e ∧ f e ∈ X := by
      intro e he
      simp only [f, he.2, dite_true]
      exact he.2.choose_spec
    have hinj : InjOn f E_bd := by
      intro e₁ he₁ e₂ he₂ heq
      exact Γ.edge_eq_of_mem he₁.1 he₂.1 (hf_spec he₁).1 (heq ▸ (hf_spec he₂).1)
    have himg_sub : f '' E_bd ⊆ (X ∩ Γ.U) \ V_bd := by
      rintro z ⟨e, he, rfl⟩
      obtain ⟨hfe, hfX⟩ := hf_spec he
      exact ⟨⟨hfX, (he.1.2.1 hfe).1⟩, fun hzV => (he.1.2.1 hfe).2 hzV.2⟩
    have hV_sub : V_bd ⊆ X ∩ Γ.U := inter_subset_inter_right X Γ.V_subset_U
    have hdisj : Disjoint V_bd (f '' E_bd) :=
      disjoint_left.mpr fun z hzV hzI => (himg_sub hzI).2 hzV
    have hunion_sub : V_bd ∪ f '' E_bd ⊆ X ∩ Γ.U := union_subset hV_sub
      (himg_sub.trans sdiff_subset)
    have hV_fin : V_bd.Finite := hfin.subset hV_sub
    have hI_fin : (f '' E_bd).Finite := hE_fin.image f
    have hle := ncard_le_ncard hunion_sub hfin
    rw [ncard_union_eq hdisj hV_fin hI_fin, hinj.ncard_image] at hle
    exact hle
  · rw [not_nonempty_iff_eq_empty.mp hE_ne, ncard_empty, add_zero]
    exact ncard_le_ncard (inter_subset_inter_right X Γ.V_subset_U) hfin

omit [T2Space S] in
/-- In a tangle `T` of `Γ.toHypergraph` where every vertex of `Γ` is incident with an edge of `Γ`,
no separation `(L, M) ∈ T` can satisfy `separationOrder L M + 2 * M.edgeSet.ncard < θ`. -/
private theorem not_mem_tangle_of_edgeSet_ncard_small {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle Γ.toHypergraph θ T)
    (hno_iso : ∀ v ∈ Γ.V, ∃ e ∈ Γ.E, v ∈ closure e) :
    ∀ (n : ℕ) {L M : Hypergraph S (Set S)},
      M.edgeSet.ncard = n → (L, M) ∈ T →
      separationOrder L M + 2 * n < θ → False := by
  intro n
  induction n with
  | zero =>
    intro L M hMn hLM _
    have hsep := hT.isSeparation hLM
    have hME : M.edgeSet = ∅ := (ncard_eq_zero M.edgeSet_finite).mp hMn
    have hLE : L.edgeSet = Γ.E := by
      have hU := hsep.edgeSet_union
      rw [hME, union_empty] at hU
      exact hU
    have hLV : L.vertexSet = Γ.V := by
      apply subset_antisymm hsep.left_le.vertexSet_subset
      intro v hv
      obtain ⟨e, he, hve⟩ := hno_iso v hv
      have heL : e ∈ L.edgeSet := hLE.symm ▸ he
      have hincG : Γ.toHypergraph.Inc e v :=
        (PaintingOrDrawing.toHypergraph_inc (Γ := PaintingOrDrawing.drawing Γ)).mpr ⟨he, hv, hve⟩
      exact L.vertex_mem_of_inc ((inc_iff_of_le hsep.left_le heL).mpr hincG)
    exact hT.axiom3 hLM hLV
  | succ n ih =>
    intro L M hMn hLM hbound
    have hsep := hT.isSeparation hLM
    have hM_ne : M.edgeSet.Nonempty := (ncard_pos M.edgeSet_finite).mp (by omega)
    obtain ⟨e, heM⟩ := hM_ne
    have heE : e ∈ Γ.E := hsep.right_le.edgeSet_subset heM
    have hends_le : (Γ.toHypergraph.ends e).ncard ≤ 2 := ends_ncard_le_two heE
    have he_size : edgeSize Γ.toHypergraph e < θ := by
      unfold edgeSize
      omega
    have hKe : (edgeHypergraph Γ.toHypergraph e, Γ.toHypergraph.deleteEdges {e}) ∈ T :=
      (GM10.theorem_2_7_proof (by omega) hT.isSeparation hT.order_lt hT.axiom1 hT.axiom2).mp
        hT e heE he_size
    let Ke := edgeHypergraph Γ.toHypergraph e
    let De := Γ.toHypergraph.deleteEdges {e}
    have hinter_sub : ((L ∪ Ke) ∩ (M ∩ De)).vertexSet ⊆
        (L ∩ M).vertexSet ∪ Γ.toHypergraph.ends e := by
      intro z ⟨hzLK, hzM, _⟩
      rcases hzLK with hzL | hzKe
      · exact Or.inl ⟨hzL, hzM⟩
      · exact Or.inr hzKe
    have hfin_u : ((L ∩ M).vertexSet ∪ Γ.toHypergraph.ends e).Finite :=
      (L ∩ M).vertexSet_finite.union (Γ.finite_V.subset fun _ h => ends_subset_closure_inter_V h
        |>.2)
    have hord_le : separationOrder (L ∪ Ke) (M ∩ De) ≤ separationOrder L M + 2 := by
      calc ((L ∪ Ke) ∩ (M ∩ De)).vertexSet.ncard
        _ ≤ ((L ∩ M).vertexSet ∪ Γ.toHypergraph.ends e).ncard :=
            ncard_le_ncard hinter_sub hfin_u
        _ ≤ (L ∩ M).vertexSet.ncard + (Γ.toHypergraph.ends e).ncard := ncard_union_le _ _
        _ ≤ separationOrder L M + 2 := Nat.add_le_add_left hends_le _
    have hord_lt : separationOrder (L ∪ Ke) (M ∩ De) < θ := by omega
    have hunion : (L ∪ Ke, M ∩ De) ∈ T := GM10.theorem_2_2_proof hT hLM hKe hord_lt
    have hMDe_eq : (M ∩ De).edgeSet = M.edgeSet \ {e} := by
      change M.edgeSet ∩ (Γ.E \ {e}) = M.edgeSet \ {e}
      ext g
      simp only [mem_inter_iff, mem_sdiff, mem_singleton_iff]
      exact ⟨fun ⟨hgM, _, hne⟩ => ⟨hgM, hne⟩,
        fun ⟨hgM, hne⟩ => ⟨hgM, hsep.right_le.edgeSet_subset hgM, hne⟩⟩
    have hMDe_card : (M ∩ De).edgeSet.ncard = n := by
      rw [hMDe_eq, ncard_sdiff_singleton_of_mem heM, hMn]
      rfl
    exact ih hMDe_card hunion (by omega)

omit [TopologicalSpace S] [T2Space S] in
private theorem ncard_biUnion_finset_le {ι : Type*} (F : Finset ι)
    (s : ι → Set S) :
    (⋃ i ∈ F, s i).ncard ≤ ∑ i ∈ F, (s i).ncard := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
    simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left, Finset.sum_insert ha]
    exact (ncard_union_le (s a) (⋃ i ∈ F, s i)).trans (Nat.add_le_add_left ih _)

/-! ## 2. Disc Separation Construction and Membership in `T` -/

private def discSepA (Γ : Drawing S) (Δ : Set S) (E₁ : Set (Set S))
    (hE₁ : E₁ ⊆ Γ.E) (hends : ∀ e ∈ E₁, closure e ∩ Γ.V ⊆ Δ) : Hypergraph S (Set S) where
  vertexSet := Γ.V ∩ Δ
  edgeSet := E₁
  Inc e v := Γ.toHypergraph.Inc e v ∧ e ∈ E₁
  vertex_mem_of_inc e v h := by
    have hi := (PaintingOrDrawing.toHypergraph_inc (Γ := PaintingOrDrawing.drawing Γ)).mp h.1
    exact ⟨hi.2.1, hends e h.2 ⟨hi.2.2, hi.2.1⟩⟩
  edge_mem_of_inc _ _ h := h.2
  vertexSet_finite := Γ.finite_V.subset inter_subset_left
  edgeSet_finite := Γ.finite_edges.subset hE₁

private def discSepB (Γ : Drawing S) (Δ : Set S) (E₁ : Set (Set S)) : Hypergraph S (Set S) where
  vertexSet := (Γ.V \ Δ) ∪ (subBd Δ ∩ Γ.V) ∪ Whitney.verts Γ.toGraph (Γ.E \ E₁)
  edgeSet := Γ.E \ E₁
  Inc e v := Γ.toHypergraph.Inc e v ∧ e ∈ Γ.E \ E₁
  vertex_mem_of_inc e v h := by
    have hi := (PaintingOrDrawing.toHypergraph_inc (Γ := PaintingOrDrawing.drawing Γ)).mp h.1
    exact Or.inr ⟨e, h.2, inc_of_mem_closure hi.1 hi.2.2 hi.2.1⟩
  edge_mem_of_inc _ _ h := h.2
  vertexSet_finite := by
    refine ((Γ.finite_V.subset sdiff_subset).union (Γ.finite_V.subset inter_subset_right)).union ?_
    exact Γ.finite_V.subset fun _ ⟨_, _, _, hl⟩ => hl.left_mem
  edgeSet_finite := Γ.finite_edges.subset sdiff_subset

omit [T2Space S] in
private theorem isSeparation_discSep {Γ : Drawing S} {Δ : Set S} {E₁ : Set (Set S)}
    (hE₁ : E₁ ⊆ Γ.E) (hends : ∀ e ∈ E₁, closure e ∩ Γ.V ⊆ Δ) :
    Γ.toHypergraph.IsSeparation (discSepA Γ Δ E₁ hE₁ hends) (discSepB Γ Δ E₁) := by
  have hleA : discSepA Γ Δ E₁ hE₁ hends ≤ Γ.toHypergraph := by
    refine ⟨inter_subset_left, hE₁, fun e he => ?_⟩
    ext v
    exact ⟨fun h => ⟨h, he⟩, fun h => h.1⟩
  have hleB : discSepB Γ Δ E₁ ≤ Γ.toHypergraph := by
    refine ⟨?_, sdiff_subset, fun e he => ?_⟩
    · refine union_subset (union_subset sdiff_subset inter_subset_right) ?_
      exact fun _ ⟨_, _, _, hl⟩ => hl.left_mem
    · ext v
      exact ⟨fun h => ⟨h, he⟩, fun h => h.1⟩
  rw [isSeparation_iff_of_le hleA hleB]
  refine ⟨?_, ?_, ?_⟩
  · ext v
    constructor
    · intro hv
      rcases hv with hvA | hvB
      · exact hleA.vertexSet_subset hvA
      · exact hleB.vertexSet_subset hvB
    · intro hv
      by_cases hvΔ : v ∈ Δ
      · exact Or.inl ⟨hv, hvΔ⟩
      · exact Or.inr (Or.inl (Or.inl ⟨hv, hvΔ⟩))
  · change E₁ ∪ (Γ.E \ E₁) = Γ.E
    ext e
    exact ⟨fun h => h.elim (fun h1 => hE₁ h1) And.left,
      fun h => (Classical.em (e ∈ E₁)).imp_right fun hn => ⟨h, hn⟩⟩
  · exact Disjoint.inter_eq disjoint_sdiff_self_right

omit [T2Space S] in
private theorem inter_vertexSet_discSep_subset {Γ : Drawing S} {Δ : Set S}
    (hΔ_cl : IsClosed Δ) {E₁ : Set (Set S)}
    (hE₁ : E₁ ⊆ Γ.E) (hends : ∀ e ∈ E₁, closure e ∩ Γ.V ⊆ Δ)
    (hin_sub : {e ∈ Γ.E | e ⊆ Δ} ⊆ E₁) :
    (discSepA Γ Δ E₁ hE₁ hends ∩ discSepB Γ Δ E₁).vertexSet ⊆
      (subBd Δ ∩ Γ.V) ∪ ⋃ e ∈ {e ∈ Γ.E | (e ∩ subBd Δ).Nonempty} \ E₁, ((closure e ∩ Γ.V) ∩ Δ) := by
  rintro v ⟨⟨hvV, hvΔ⟩, hvB⟩
  rcases hvB with (⟨_, hvnΔ⟩ | hv_bd) | ⟨e, ⟨heE, he_not⟩, hinc⟩
  · exact absurd hvΔ hvnΔ
  · exact Or.inl hv_bd
  · have hve : v ∈ closure e := mem_closure_of_inc hinc
    by_cases he_bd : (e ∩ subBd Δ).Nonempty
    · exact Or.inr (mem_iUnion₂.mpr ⟨e, ⟨⟨heE, he_bd⟩, he_not⟩, ⟨hve, hvV⟩, hvΔ⟩)
    · have hdis_bd : Disjoint e (frontier Δ) := by
        rw [← subBd_eq_frontier]
        exact not_nonempty_iff_eq_empty.mp he_bd |> disjoint_iff_inter_eq_empty.mpr
      have hdis_Δ : Disjoint e Δ := by
        refine disjoint_left.mpr fun x hxe hxΔ => he_not (hin_sub ⟨heE, ?_⟩)
        exact subset_of_disjoint_frontier heE.2.2.1.isConnected.isPreconnected
          hΔ_cl hdis_bd hxe hxΔ
      have hv_not_int : v ∉ interior Δ := by
        intro hv_int
        obtain ⟨y, hy_int, hye⟩ := mem_closure_iff.mp hve (interior Δ) isOpen_interior hv_int
        exact disjoint_left.mp hdis_Δ hye (interior_subset hy_int)
      have hv_fr : v ∈ subBd Δ := by
        rw [subBd_eq_frontier, frontier, hΔ_cl.closure_eq]
        exact ⟨hvΔ, hv_not_int⟩
      exact Or.inl ⟨hv_fr, hvV⟩

public section

/-- For any 2-cell drawing `Γ` with `Γ.E.Nonempty` on a connected closed non-spherical surface `S`,
respectful tangle `T` of order `θ > 15`, and closed disc `Δ ⊆ S` with `(subBd Δ ∩ Γ.U).Finite` and
`(subBd Δ ∩ Γ.U).ncard ≤ 3`, there is a separation `(A, B) ∈ T` of `Γ.toHypergraph` with
`A.vertexSet = Γ.V ∩ Δ`, `separationOrder A B ≤ (subBd Δ ∩ Γ.U).ncard`, and every separator vertex
either in `subBd Δ ∩ Γ.V` or an end of an edge of `Γ` meeting `subBd Δ`. -/
theorem disc_sep_mem_tangle [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S)
    {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 15 < θ) (hE : Γ.E.Nonempty) (hResp : IsRespectfulDrawingTangle Γ θ T)
    {Δ : Set S} (hΔ : IsClosedDisc Δ)
    (hfin : (subBd Δ ∩ Γ.U).Finite) (hcard : (subBd Δ ∩ Γ.U).ncard ≤ 3) :
    ∃ A B : Hypergraph S (Set S),
      (A, B) ∈ T ∧
      A.vertexSet = Γ.V ∩ Δ ∧
      separationOrder A B ≤ (subBd Δ ∩ Γ.U).ncard ∧
      (∀ w ∈ (A ∩ B).vertexSet,
        w ∈ subBd Δ ∩ Γ.V ∨ ∃ e ∈ Γ.E, (e ∩ subBd Δ).Nonempty ∧ w ∈ closure e ∩ Γ.V) := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have h2cell : (PaintingOrDrawing.drawing Γ).IsTwoCell := hResp.1
  have hT : IsTangle Γ.toHypergraph θ T := hResp.2.1
  have hresp : (PaintingOrDrawing.drawing Γ).IsRespectful θ T := hResp.2.2
  obtain ⟨K, hK⟩ := GM11.exists_radialDrawing (Γ := PaintingOrDrawing.drawing Γ) hS h2cell
  obtain ⟨ins, hd⟩ := GM11.exists_derivedSlope hS hresp hK.2.1
  have hrf : RegionFacts (PaintingOrDrawing.drawing Γ) K :=
    GM11.regionFacts_of_radial ⟨hK.1, hK.2.1⟩ hS hK.2.2 hE
  have hno_iso : ∀ v ∈ Γ.V, ∃ e ∈ Γ.E, v ∈ closure e := fun v hv => by
    obtain ⟨e, he, hve⟩ := GM11.exists_edge_of_regionFacts hS hrf hv
    exact ⟨e, he, hve⟩
  set V_bd := subBd Δ ∩ Γ.V
  set E_bd := {e ∈ Γ.E | (e ∩ subBd Δ).Nonempty}
  have hE_bd_fin : E_bd.Finite := Γ.finite_edges.subset fun _ h => h.1
  have hV_bd_fin : V_bd.Finite := Γ.finite_V.subset inter_subset_right
  have hsum_le : V_bd.ncard + E_bd.ncard ≤ (subBd Δ ∩ Γ.U).ncard :=
    bd_verts_add_edges_ncard_le hfin
  -- Step 1: Purely interior edge set `E₀ = {e ∈ Γ.E | e ⊆ Δ}` gives `(A₀, B₀) ∈ T` of order `≤ 6`.
  let E₀ : Set (Set S) := {e ∈ Γ.E | e ⊆ Δ}
  have hE₀_sub : E₀ ⊆ Γ.E := fun _ h => h.1
  have hE₀_ends : ∀ e ∈ E₀, closure e ∩ Γ.V ⊆ Δ := fun e he x hx =>
    hΔ.isClosed.closure_subset_iff.mpr he.2 hx.1
  let A₀ := discSepA Γ Δ E₀ hE₀_sub hE₀_ends
  let B₀ := discSepB Γ Δ E₀
  have hsep₀ : Γ.toHypergraph.IsSeparation A₀ B₀ := isSeparation_discSep hE₀_sub hE₀_ends
  have hord₀_le : separationOrder A₀ B₀ ≤ 6 := by
    have hsub₀ := inter_vertexSet_discSep_subset hΔ.isClosed hE₀_sub hE₀_ends Subset.rfl
    have hfin_bi : (⋃ e ∈ E_bd \ E₀, ((closure e ∩ Γ.V) ∩ Δ)).Finite :=
      (hE_bd_fin.subset sdiff_subset).biUnion fun _ _ =>
        Γ.finite_V.subset (inter_subset_right.trans' inter_subset_left)
    have hbi_le : (⋃ e ∈ E_bd \ E₀, ((closure e ∩ Γ.V) ∩ Δ)).ncard ≤ 2 * (E_bd \ E₀).ncard := by
      classical
      obtain ⟨F, hF⟩ := (hE_bd_fin.subset sdiff_subset).exists_finset_coe
      rw [← hF]
      have hbi_eq : (⋃ e ∈ (F : Set (Set S)), ((closure e ∩ Γ.V) ∩ Δ)) =
          ⋃ e ∈ F, ((closure e ∩ Γ.V) ∩ Δ) := by simp
      rw [hbi_eq, ncard_coe_finset]
      refine (ncard_biUnion_finset_le F fun e => (closure e ∩ Γ.V) ∩ Δ).trans ?_
      calc ∑ e ∈ F, ((closure e ∩ Γ.V) ∩ Δ).ncard
        _ ≤ ∑ _e ∈ F, 2 := Finset.sum_le_sum fun e heF => by
            have heE : e ∈ Γ.E := ((hF ▸ heF : e ∈ E_bd \ E₀)).1.1
            exact (ncard_le_ncard inter_subset_left
              (Γ.finite_V.subset inter_subset_right)).trans
              (closure_inter_V_nonempty_and_ncard_le_two heE).2
        _ = 2 * F.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hle_ediff : (E_bd \ E₀).ncard ≤ E_bd.ncard := ncard_le_ncard sdiff_subset hE_bd_fin
    calc (A₀ ∩ B₀).vertexSet.ncard
      _ ≤ (V_bd ∪ ⋃ e ∈ E_bd \ E₀, ((closure e ∩ Γ.V) ∩ Δ)).ncard :=
          ncard_le_ncard hsub₀ (hV_bd_fin.union hfin_bi)
      _ ≤ V_bd.ncard + (⋃ e ∈ E_bd \ E₀, ((closure e ∩ Γ.V) ∩ Δ)).ncard := ncard_union_le _ _
      _ ≤ V_bd.ncard + 2 * (E_bd \ E₀).ncard := Nat.add_le_add_left hbi_le _
      _ ≤ V_bd.ncard + 2 * E_bd.ncard := Nat.add_le_add_left (Nat.mul_le_mul_left 2 hle_ediff) _
      _ ≤ 6 := by omega
  have hA₀_null : ∀ F : Set S, F ⊆ PaintingOrDrawing.underlying A₀ → IsOArc F →
      IsNullHomotopicOArc F := by
    intro F hFA hF
    have hsub : ∀ e ∈ A₀.edgeSet, e ⊆ Δ := fun _ he => he.2
    have hFΔ : F ⊆ Δ :=
      GM11.oArc_subset_of_edges hF hΔ.isClosed A₀.vertexSet_finite hsub hFA
    exact isNullHomotopicOArcIn_of_subset_disc hF (subset_univ _) hΔ hFΔ
  obtain ⟨F₀, hF₀, hF₀_sub, hF₀_not_null⟩ :=
    GM11.exists_oArc_of_null hS hns hE hK (by omega) hd hsep₀ (by omega) hA₀_null
  have hnot_B₀ : (B₀, A₀) ∉ T := by
    intro hB₀A₀
    exact hF₀_not_null (GM11.no_oArc_of_mem (Γ := PaintingOrDrawing.drawing Γ) hS hns hE h2cell
      hT.isPretangle hresp hK hd hsep₀.symm (by rw [separationOrder_comm]; omega) hB₀A₀ hF₀
      (hF₀_sub.trans sdiff_subset))
  have hA₀B₀ : (A₀, B₀) ∈ T := (hT.axiom1 hsep₀ (by omega)).resolve_right hnot_B₀
  -- Step 2: Refined edge set `E₁` adds boundary edges whose ends both lie in `Δ`, giving order `≤
  -- 3`.
  let E₁ : Set (Set S) := {e ∈ Γ.E | e ⊆ Δ ∨ (e ∈ E_bd ∧ closure e ∩ Γ.V ⊆ Δ)}
  have hE₁_sub : E₁ ⊆ Γ.E := fun _ h => h.1
  have hE₁_ends : ∀ e ∈ E₁, closure e ∩ Γ.V ⊆ Δ := by
    rintro e ⟨_, heΔ | ⟨_, hends⟩⟩
    · exact fun x hx => hΔ.isClosed.closure_subset_iff.mpr heΔ hx.1
    · exact hends
  have hE₀_E₁ : E₀ ⊆ E₁ := fun _ ⟨he, heΔ⟩ => ⟨he, Or.inl heΔ⟩
  let A₁ := discSepA Γ Δ E₁ hE₁_sub hE₁_ends
  let B₁ := discSepB Γ Δ E₁
  have hsep₁ : Γ.toHypergraph.IsSeparation A₁ B₁ := isSeparation_discSep hE₁_sub hE₁_ends
  have hsub₁ := inter_vertexSet_discSep_subset hΔ.isClosed hE₁_sub hE₁_ends hE₀_E₁
  have hord₁_le : separationOrder A₁ B₁ ≤ (subBd Δ ∩ Γ.U).ncard := by
    have hfin_bi : (⋃ e ∈ E_bd \ E₁, ((closure e ∩ Γ.V) ∩ Δ)).Finite :=
      (hE_bd_fin.subset sdiff_subset).biUnion fun _ _ =>
        Γ.finite_V.subset (inter_subset_right.trans' inter_subset_left)
    have hbi_le : (⋃ e ∈ E_bd \ E₁, ((closure e ∩ Γ.V) ∩ Δ)).ncard ≤ (E_bd \ E₁).ncard := by
      classical
      obtain ⟨F, hF⟩ := (hE_bd_fin.subset sdiff_subset).exists_finset_coe
      rw [← hF]
      have hbi_eq : (⋃ e ∈ (F : Set (Set S)), ((closure e ∩ Γ.V) ∩ Δ)) =
          ⋃ e ∈ F, ((closure e ∩ Γ.V) ∩ Δ) := by simp
      rw [hbi_eq, ncard_coe_finset]
      refine (ncard_biUnion_finset_le F fun e => (closure e ∩ Γ.V) ∩ Δ).trans ?_
      calc ∑ e ∈ F, ((closure e ∩ Γ.V) ∩ Δ).ncard
        _ ≤ ∑ _e ∈ F, 1 := Finset.sum_le_sum fun e heF => by
            obtain ⟨he_bd, he_not⟩ := (hF ▸ heF : e ∈ E_bd \ E₁)
            exact closure_inter_V_inter_ncard_le_one he_bd.1
              fun hends => he_not ⟨he_bd.1, Or.inr ⟨he_bd, hends⟩⟩
        _ = F.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    have hle_ediff : (E_bd \ E₁).ncard ≤ E_bd.ncard := ncard_le_ncard sdiff_subset hE_bd_fin
    calc (A₁ ∩ B₁).vertexSet.ncard
      _ ≤ (V_bd ∪ ⋃ e ∈ E_bd \ E₁, ((closure e ∩ Γ.V) ∩ Δ)).ncard :=
          ncard_le_ncard hsub₁ (hV_bd_fin.union hfin_bi)
      _ ≤ V_bd.ncard + (⋃ e ∈ E_bd \ E₁, ((closure e ∩ Γ.V) ∩ Δ)).ncard := ncard_union_le _ _
      _ ≤ V_bd.ncard + (E_bd \ E₁).ncard := Nat.add_le_add_left hbi_le _
      _ ≤ V_bd.ncard + E_bd.ncard := Nat.add_le_add_left hle_ediff _
      _ ≤ (subBd Δ ∩ Γ.U).ncard := hsum_le
  -- Step 3: Show `(B₁, A₁) ∉ T`, hence `(A₁, B₁) ∈ T`.
  have hnot_B₁ : (B₁, A₁) ∉ T := by
    intro hB₁A₁
    have hinter_u : ((A₀ ∪ B₁) ∩ (B₀ ∩ A₁)).vertexSet ⊆
        (A₀ ∩ B₀).vertexSet ∪ (B₁ ∩ A₁).vertexSet := by
      intro z ⟨hz_l, hzB₀, hzA₁⟩
      rcases hz_l with hzA₀ | hzB₁
      · exact Or.inl ⟨hzA₀, hzB₀⟩
      · exact Or.inr ⟨hzB₁, hzA₁⟩
    have hord_u_le : separationOrder (A₀ ∪ B₁) (B₀ ∩ A₁) ≤ 9 := by
      have hfin_u := (A₀ ∩ B₀).vertexSet_finite.union (B₁ ∩ A₁).vertexSet_finite
      have hord_B₁A₁ : (B₁ ∩ A₁).vertexSet.ncard ≤ 3 := by
        have : separationOrder B₁ A₁ ≤ 3 := by
          rw [separationOrder_comm]
          exact hord₁_le.trans hcard
        exact this
      calc ((A₀ ∪ B₁) ∩ (B₀ ∩ A₁)).vertexSet.ncard
        _ ≤ ((A₀ ∩ B₀).vertexSet ∪ (B₁ ∩ A₁).vertexSet).ncard := ncard_le_ncard hinter_u hfin_u
        _ ≤ (A₀ ∩ B₀).vertexSet.ncard + (B₁ ∩ A₁).vertexSet.ncard := ncard_union_le _ _
        _ ≤ 6 + 3 := Nat.add_le_add hord₀_le hord_B₁A₁
        _ = 9 := rfl
    have hunion : (A₀ ∪ B₁, B₀ ∩ A₁) ∈ T :=
      GM10.theorem_2_2_proof hT hA₀B₀ hB₁A₁ (by omega)
    have hR_sub : (B₀ ∩ A₁).edgeSet ⊆ E_bd := by
      rintro e ⟨⟨_, he_not₀⟩, ⟨heE, he₁⟩⟩
      rcases he₁ with heΔ | ⟨he_bd, _⟩
      · exact absurd ⟨heE, heΔ⟩ he_not₀
      · exact he_bd
    have hR_card : (B₀ ∩ A₁).edgeSet.ncard ≤ 3 :=
      (ncard_le_ncard hR_sub hE_bd_fin).trans (by omega)
    exact not_mem_tangle_of_edgeSet_ncard_small hT hno_iso (B₀ ∩ A₁).edgeSet.ncard rfl hunion
      (by omega)
  have hA₁B₁ : (A₁, B₁) ∈ T := (hT.axiom1 hsep₁ (by omega)).resolve_right hnot_B₁
  refine ⟨A₁, B₁, hA₁B₁, rfl, hord₁_le, fun w hw => ?_⟩
  rcases hsub₁ hw with hw_bd | hw_bi
  · exact Or.inl hw_bd
  · obtain ⟨e, ⟨⟨heE, he_bd⟩, _⟩, hwe, _⟩ := mem_iUnion₂.mp hw_bi
    exact Or.inr ⟨e, heE, he_bd, hwe⟩

/-! ## 3. Curve Hit-Count vs. Tangle Metric Bound (`d {u} {v} < 12`) -/

/-- `AssocVertex H p w` relates a point `p ∈ H.U` to an associated vertex `w ∈ H.V`: either
`p = w ∈ H.V`, or `p` lies in an edge `e ∈ H.E` and `w` is an end of `e`. -/
private def AssocVertex (H : Drawing S) (p w : S) : Prop :=
  (p ∈ H.V ∧ w = p) ∨ ∃ e ∈ H.E, p ∈ e ∧ w ∈ closure e ∩ H.V

omit [T2Space S] in
private theorem AssocVertex.mem_V {H : Drawing S} {p w : S} (h : AssocVertex H p w) :
    w ∈ H.V := by
  rcases h with ⟨hp, rfl⟩ | ⟨_, _, _, hw⟩
  · exact hp
  · exact hw.2

omit [T2Space S] in
private theorem exists_assocVertex {H : Drawing S} {p : S} (hp : p ∈ H.U) :
    ∃ w ∈ H.V, AssocVertex H p w := by
  by_cases hpV : p ∈ H.V
  · exact ⟨p, hpV, Or.inl ⟨hpV, rfl⟩⟩
  · obtain ⟨e, he, hpe⟩ := H.exists_edge_of_mem hp hpV
    obtain ⟨⟨w, hw⟩, -⟩ := closure_inter_V_nonempty_and_ncard_le_two he
    exact ⟨w, hw.2, Or.inr ⟨e, he, hpe, hw⟩⟩

omit [T2Space S] in
private theorem mem_closure_region_of_assocVertex (hS : IsClosedSurface S)
    {H : Drawing S} {p w : S} {r : Set S}
    (ha : AssocVertex H p w) (hr : r ∈ H.R) (hpr : p ∈ closure r) :
    w ∈ closure r := by
  rcases ha with ⟨_, rfl⟩ | ⟨e, he, hpe, hwe, _⟩
  · exact hpr
  · have her : e ⊆ closure r := GM11.edge_subset_closure_of_incident hS he hr ⟨p, hpe, hpr⟩
    exact isClosed_closure.closure_subset_iff.mpr her hwe

omit [T2Space S] in
private theorem finite_R_of_radial {H K : Drawing S} (hE : H.E.Nonempty)
    (hrad : (PaintingOrDrawing.drawing H).IsRadialDrawing K) :
    H.R.Finite := by
  classical
  obtain ⟨e₀, he₀⟩ := hE
  obtain ⟨v₀, _⟩ := he₀.1
  let hub : Set S → S := fun r =>
    if hr : r ∈ H.R then (hrad.2.1.2.2.1 r hr).exists.choose else v₀
  have hhub_spec : ∀ {r}, r ∈ H.R → hub r ∈ r ∧ hub r ∈ K.V := by
    intro r hr
    simp only [hub, hr, dite_true]
    exact (hrad.2.1.2.2.1 r hr).exists.choose_spec
  refine Finite.of_finite_image (f := hub) (K.finite_V.subset ?_) ?_
  · rintro _ ⟨r, hr, rfl⟩
    exact (hhub_spec hr).2
  · intro r₁ hr₁ r₂ hr₂ heq
    exact region_eq_of_mem hr₁ hr₂ (hhub_spec hr₁).1 (heq ▸ (hhub_spec hr₂).1)

/-- For any nonempty proper subset `X₁` of `X = range φ ∩ H.U`, some region `r ∈ H.R` meets both
`X₁` and `X \ X₁` in its closure. -/
private theorem exists_shared_region_of_partition (hS : IsClosedSurface S) {H K : Drawing S}
    (hE : H.E.Nonempty) (hrad : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    {φ : C(Circle, S)} (hfin : (range φ ∩ H.U).Finite)
    {X₁ : Set S} (hX₁_sub : X₁ ⊆ range φ ∩ H.U)
    (hX₁_ne : X₁.Nonempty) (hX₂_ne : ((range φ ∩ H.U) \ X₁).Nonempty) :
    ∃ q₁ ∈ X₁, ∃ q₂ ∈ (range φ ∩ H.U) \ X₁, ∃ r ∈ H.R,
      q₁ ∈ closure r ∧ q₂ ∈ closure r := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  set X := range φ ∩ H.U
  set X₂ := X \ X₁
  have hR_fin : H.R.Finite := finite_R_of_radial hE hrad
  by_contra hno
  push Not at hno
  let R₁ := {r ∈ H.R | Disjoint (closure r) X₂}
  let R₂ := {r ∈ H.R | ¬ Disjoint (closure r) X₂}
  have hR₂_disj : ∀ r ∈ R₂, Disjoint (closure r) X₁ := by
    intro r ⟨hr, hnot₂⟩
    rw [Set.not_disjoint_iff] at hnot₂
    obtain ⟨q₂, hq₂_cl, hq₂_X₂⟩ := hnot₂
    exact disjoint_left.mpr fun q₁ hq₁_cl hq₁_X₁ =>
      hno q₁ hq₁_X₁ q₂ hq₂_X₂ r hr hq₁_cl hq₂_cl
  let K₁ : Set S := X₁ ∪ ⋃ r ∈ R₁, closure r
  let K₂ : Set S := X₂ ∪ ⋃ r ∈ R₂, closure r
  have hRf₁ : R₁.Finite := hR_fin.subset fun _ h => h.1
  have hRf₂ : R₂.Finite := hR_fin.subset fun _ h => h.1
  have hK₁_cl : IsClosed K₁ :=
    (hfin.subset hX₁_sub).isClosed.union (hRf₁.isClosed_biUnion fun _ _ => isClosed_closure)
  have hK₂_cl : IsClosed K₂ :=
    (hfin.subset sdiff_subset).isClosed.union (hRf₂.isClosed_biUnion fun _ _ => isClosed_closure)
  have hcov : range φ ⊆ K₁ ∪ K₂ := by
    intro z hz
    by_cases hzU : z ∈ H.U
    · by_cases hz₁ : z ∈ X₁
      · exact Or.inl (Or.inl hz₁)
      · exact Or.inr (Or.inl ⟨⟨hz, hzU⟩, hz₁⟩)
    · obtain ⟨r, hr, hzr⟩ := exists_region_of_notMem hzU
      by_cases hd₂ : Disjoint (closure r) X₂
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨r, ⟨hr, hd₂⟩, subset_closure hzr⟩))
      · exact Or.inr (Or.inr (mem_iUnion₂.mpr ⟨r, ⟨hr, hd₂⟩, subset_closure hzr⟩))
  obtain ⟨q₁, hq₁⟩ := hX₁_ne
  obtain ⟨q₂, hq₂⟩ := hX₂_ne
  have hconn := (isConnected_range φ.continuous).isPreconnected
  obtain ⟨z, hz_ran, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp hconn K₁ K₂ hK₁_cl hK₂_cl hcov
    ⟨q₁, (hX₁_sub hq₁).1, Or.inl hq₁⟩ ⟨q₂, hq₂.1.1, Or.inl hq₂⟩
  by_cases hzU : z ∈ H.U
  · by_cases hzX₁ : z ∈ X₁
    · rcases hz₂ with hzX₂ | hzr₂
      · exact hzX₂.2 hzX₁
      · obtain ⟨r₂, hr₂, hzr₂⟩ := mem_iUnion₂.mp hzr₂
        exact disjoint_left.mp (hR₂_disj r₂ hr₂) hzr₂ hzX₁
    · have hzX₂ : z ∈ X₂ := ⟨⟨hz_ran, hzU⟩, hzX₁⟩
      rcases hz₁ with hzX₁' | hzr₁
      · exact hzX₁ hzX₁'
      · obtain ⟨r₁, ⟨_, hd₁⟩, hzr₁⟩ := mem_iUnion₂.mp hzr₁
        exact disjoint_left.mp hd₁ hzr₁ hzX₂
  · obtain ⟨r₀, hr₀, hzr₀⟩ := exists_region_of_notMem hzU
    have hzr₁ : z ∈ ⋃ r ∈ R₁, closure r :=
      hz₁.resolve_left fun h => hzU (hX₁_sub h).2
    have hzr₂ : z ∈ ⋃ r ∈ R₂, closure r :=
      hz₂.resolve_left fun h => hzU h.1.2
    obtain ⟨r₁, hr₁, hcl₁⟩ := mem_iUnion₂.mp hzr₁
    obtain ⟨r₂, hr₂, hcl₂⟩ := mem_iUnion₂.mp hzr₂
    obtain ⟨y₁, hy₁₀, hy₁₁⟩ := mem_closure_iff.mp hcl₁ r₀ (region_isOpen hr₀) hzr₀
    obtain ⟨y₂, hy₂₀, hy₂₂⟩ := mem_closure_iff.mp hcl₂ r₀ (region_isOpen hr₀) hzr₀
    have heq₁ : r₀ = r₁ := region_eq_of_mem hr₀ hr₁.1 hy₁₀ hy₁₁
    have heq₂ : r₀ = r₂ := region_eq_of_mem hr₀ hr₂.1 hy₂₀ hy₂₂
    exact hr₂.2 (heq₂ ▸ heq₁ ▸ hr₁.2)

private theorem dist_le_two_of_same_or_shared_region [ConnectedSpace S]
    (hS : IsClosedSurface S) {H K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}
    {d : Set S → Set S → ℕ}
    (hE : H.E.Nonempty) (hResp : IsRespectfulDrawingTangle H θ T)
    (hrad : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hslope : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hd_eq : ∀ x ∈ H.A, ∀ y ∈ H.A, d x y = tangleMetric H K ins θ x y)
    {p₁ p₂ w₁ w₂ : S} (ha₁ : AssocVertex H p₁ w₁) (ha₂ : AssocVertex H p₂ w₂)
    (hrel : p₁ = p₂ ∨ ∃ r ∈ H.R, p₁ ∈ closure r ∧ p₂ ∈ closure r) :
    d {w₁} {w₂} ≤ 2 := by
  have hsl : IsSlope K (2 * θ) ins :=
    GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing H) hS hResp.2.1.isPretangle hrad.2.1.1
      hslope
  have hw₁V := ha₁.mem_V
  have hw₂V := ha₂.mem_V
  have hw₁A : ({w₁} : Set S) ∈ H.A := Or.inl (Or.inl ⟨w₁, hw₁V, rfl⟩)
  have hw₂A : ({w₂} : Set S) ∈ H.A := Or.inl (Or.inl ⟨w₂, hw₂V, rfl⟩)
  have h_via_region : ∀ {r : Set S}, r ∈ H.R → w₁ ∈ closure r → w₂ ∈ closure r →
      d {w₁} {w₂} ≤ 2 := by
    intro r hr hwr₁ hwr₂
    rw [hd_eq {w₁} hw₁A {w₂} hw₂A]
    have h1 := GM11.tangleMetric_le_one (ins := ins) (θ := θ) hS hrad hE hw₁V hr hwr₁
    have h2 : tangleMetric H K ins θ r {w₂} ≤ 1 := by
      rw [GM11.tangleMetric_comm]
      exact GM11.tangleMetric_le_one (ins := ins) (θ := θ) hS hrad hE hw₂V hr hwr₂
    exact (GM11.tangleMetric_triangle hS hrad.2.1 hsl {w₁} r {w₂}).trans (Nat.add_le_add h1 h2)
  rcases hrel with rfl | ⟨r, hr, hp₁r, hp₂r⟩
  · rcases ha₁ with ⟨hp₁V, hw₁_eq⟩ | ⟨e₁, he₁, hp₁e₁, hw₁e₁, _⟩
    · rcases ha₂ with ⟨_, hw₂_eq⟩ | ⟨e₂, he₂, hp₁e₂, _, _⟩
      · have hw_eq : w₂ = w₁ := hw₂_eq.trans hw₁_eq.symm
        rw [hd_eq {w₁} hw₁A {w₂} hw₂A, hw_eq]
        simp [tangleMetric]
      · exact absurd hp₁V (he₂.2.1 hp₁e₂).2
    · rcases ha₂ with ⟨hp₁V, _⟩ | ⟨e₂, he₂, hp₁e₂, hw₂e₂, _⟩
      · exact absurd hp₁V (he₁.2.1 hp₁e₁).2
      · have heq : e₁ = e₂ := H.edge_eq_of_mem he₁ he₂ hp₁e₁ hp₁e₂
        subst heq
        obtain ⟨r, hr, her⟩ := GM11.exists_region_incident hS he₁
        have hcl : closure e₁ ⊆ closure r := isClosed_closure.closure_subset_iff.mpr her
        exact h_via_region hr (hcl hw₁e₁) (hcl hw₂e₂)
  · exact h_via_region hr
      (mem_closure_region_of_assocVertex hS ha₁ hr hp₁r)
      (mem_closure_region_of_assocVertex hS ha₂ hr hp₂r)

private theorem dist_le_four_of_assocVertex_on_curve [ConnectedSpace S]
    (hS : IsClosedSurface S) {H K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}
    {d : Set S → Set S → ℕ}
    (hE : H.E.Nonempty) (hResp : IsRespectfulDrawingTangle H θ T)
    (hrad : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hslope : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hd_eq : ∀ x ∈ H.A, ∀ y ∈ H.A, d x y = tangleMetric H K ins θ x y)
    {φ : C(Circle, S)} (hfin : (range φ ∩ H.U).Finite) (hcard : (range φ ∩ H.U).ncard ≤ 3)
    {p₁ p₂ w₁ w₂ : S} (hp₁ : p₁ ∈ range φ ∩ H.U) (hp₂ : p₂ ∈ range φ ∩ H.U)
    (ha₁ : AssocVertex H p₁ w₁) (ha₂ : AssocVertex H p₂ w₂) :
    d {w₁} {w₂} ≤ 4 := by
  have hsl : IsSlope K (2 * θ) ins :=
    GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing H) hS hResp.2.1.isPretangle hrad.2.1.1
      hslope
  set X := range φ ∩ H.U
  let X₁ : Set S := {q ∈ X | q = p₁ ∨ ∃ r ∈ H.R, p₁ ∈ closure r ∧ q ∈ closure r}
  by_cases hp₂_X₁ : p₂ ∈ X₁
  · exact (dist_le_two_of_same_or_shared_region hS hE hResp hrad hslope hd_eq ha₁ ha₂
      (hp₂_X₁.2.imp Eq.symm id)).trans (by omega)
  · have hX₁_sub : X₁ ⊆ X := fun _ h => h.1
    have hp₁_X₁ : p₁ ∈ X₁ := ⟨hp₁, Or.inl rfl⟩
    obtain ⟨q₁, hq₁, q₂, hq₂, r₂, hr₂, hq₁r₂, hq₂r₂⟩ :=
      exists_shared_region_of_partition hS hE hrad hfin hX₁_sub ⟨p₁, hp₁_X₁⟩ ⟨p₂, hp₂, hp₂_X₁⟩
    have hq₁_ne : q₁ ≠ p₁ := by
      rintro rfl
      exact hq₂.2 ⟨hq₂.1, Or.inr ⟨r₂, hr₂, hq₁r₂, hq₂r₂⟩⟩
    have hq₂_eq : q₂ = p₂ := by
      by_contra hne₂
      have hp₁_ne_p₂ : p₁ ≠ p₂ := fun h => hp₂_X₁ (h ▸ hp₁_X₁)
      have hp₁_ne_q₂ : p₁ ≠ q₂ := fun h => hq₂.2 (h ▸ hp₁_X₁)
      have hq₁_ne_q₂ : q₁ ≠ q₂ := fun h => hq₂.2 (h ▸ hq₁)
      have hq₁_ne_p₂ : q₁ ≠ p₂ := fun h => hp₂_X₁ (h ▸ hq₁)
      have hsub4 : ({p₁, q₁, q₂, p₂} : Set S) ⊆ X := by
        rintro z (rfl | rfl | rfl | rfl)
        · exact hp₁
        · exact hq₁.1
        · exact hq₂.1
        · exact hp₂
      have h4 : ({p₁, q₁, q₂, p₂} : Set S).ncard = 4 := by
        rw [ncard_insert_of_notMem (by simp [hq₁_ne.symm, hp₁_ne_q₂, hp₁_ne_p₂]),
          ncard_insert_of_notMem (by simp [hq₁_ne_q₂, hq₁_ne_p₂]),
          ncard_pair hne₂]
      have hle := ncard_le_ncard hsub4 hfin
      omega
    subst hq₂_eq
    obtain ⟨w_q, hw_qV, ha_q⟩ := exists_assocVertex hq₁.1.2
    have hd₁ : d {w₁} {w_q} ≤ 2 :=
      dist_le_two_of_same_or_shared_region hS hE hResp hrad hslope hd_eq ha₁ ha_q
        (hq₁.2.imp Eq.symm id)
    have hd₂ : d {w_q} {w₂} ≤ 2 :=
      dist_le_two_of_same_or_shared_region hS hE hResp hrad hslope hd_eq ha_q ha₂
        (Or.inr ⟨r₂, hr₂, hq₁r₂, hq₂r₂⟩)
    have hw₁A : ({w₁} : Set S) ∈ H.A := Or.inl (Or.inl ⟨w₁, ha₁.mem_V, rfl⟩)
    have hwqA : ({w_q} : Set S) ∈ H.A := Or.inl (Or.inl ⟨w_q, hw_qV, rfl⟩)
    have hw₂A : ({w₂} : Set S) ∈ H.A := Or.inl (Or.inl ⟨w₂, ha₂.mem_V, rfl⟩)
    have htri : d {w₁} {w₂} ≤ d {w₁} {w_q} + d {w_q} {w₂} := by
      rw [hd_eq {w₁} hw₁A {w₂} hw₂A, hd_eq {w₁} hw₁A {w_q} hwqA, hd_eq {w_q} hwqA {w₂} hw₂A]
      exact GM11.tangleMetric_triangle hS hrad.2.1 hsl {w₁} {w_q} {w₂}
    omega

private theorem exists_assocVertex_dist_le_three_of_mem_curveIns [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S)
    {H K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}
    {d : Set S → Set S → ℕ}
    (hθ : 15 < θ) (hE : H.E.Nonempty) (hResp : IsRespectfulDrawingTangle H θ T)
    (hrad : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hslope : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hd_eq : ∀ x ∈ H.A, ∀ y ∈ H.A, d x y = tangleMetric H K ins θ x y)
    {φ : C(Circle, S)} (hfin : (range φ ∩ H.U).Finite) (hcard : (range φ ∩ H.U).ncard ≤ 3)
    {u : S} (hu : u ∈ H.V) (hu_ins : u ∈ curveIns φ) :
    ∃ p ∈ range φ ∩ H.U, ∃ w ∈ H.V, AssocVertex H p w ∧ d {u} {w} ≤ 3 := by
  have huA : ({u} : Set S) ∈ H.A := Or.inl (Or.inl ⟨u, hu, rfl⟩)
  rcases hu_ins with hu_ran | hu_disc
  · refine ⟨u, ⟨hu_ran, H.V_subset_U hu⟩, u, hu, Or.inl ⟨hu, rfl⟩, ?_⟩
    rw [hd_eq {u} huA {u} huA]
    simp [tangleMetric]
  · obtain ⟨Δ, ⟨hΔ, hbd_sub⟩, huΔ⟩ := mem_iUnion₂.mp hu_disc
    have hbd_U_sub : subBd Δ ∩ H.U ⊆ range φ ∩ H.U := inter_subset_inter_left H.U hbd_sub
    have hfin_Δ : (subBd Δ ∩ H.U).Finite := hfin.subset hbd_U_sub
    have hcard_Δ : (subBd Δ ∩ H.U).ncard ≤ 3 := (ncard_le_ncard hbd_U_sub hfin).trans hcard
    obtain ⟨A₁, B₁, hA₁B₁, hAV, hord_le, hsep_verts⟩ :=
      disc_sep_mem_tangle hS hns hθ hE hResp hΔ hfin_Δ hcard_Δ
    have hassoc_sep : ∀ w ∈ (A₁ ∩ B₁).vertexSet,
        ∃ p ∈ range φ ∩ H.U, AssocVertex H p w := by
      intro w hw
      rcases hsep_verts w hw with ⟨hw_bd, hwV⟩ | ⟨e, heE, ⟨p, hpe, hp_bd⟩, hw_cl⟩
      · exact ⟨w, ⟨hbd_sub hw_bd, H.V_subset_U hwV⟩, Or.inl ⟨hwV, rfl⟩⟩
      · exact ⟨p, ⟨hbd_sub hp_bd, (heE.2.1 hpe).1⟩, Or.inr ⟨e, heE, hpe, hw_cl⟩⟩
    by_cases hu_sep : u ∈ (A₁ ∩ B₁).vertexSet
    · obtain ⟨p, hp, ha⟩ := hassoc_sep u hu_sep
      refine ⟨p, hp, u, hu, ha, ?_⟩
      rw [hd_eq {u} huA {u} huA]
      simp [tangleMetric]
    · have hsep₁ := hResp.2.1.isSeparation hA₁B₁
      have huA₁ : u ∈ A₁.vertexSet := hAV.symm ▸ ⟨hu, huΔ⟩
      have hu_not_B₁ : u ∉ B₁.vertexSet := fun huB₁ => hu_sep ⟨huA₁, huB₁⟩
      have hrf : RegionFacts (PaintingOrDrawing.drawing H) K :=
        GM11.regionFacts_of_radial ⟨hrad.1, hrad.2.1⟩ hS hrad.2.2 hE
      obtain ⟨f, hfE, huf⟩ := GM11.exists_edge_of_regionFacts hS hrf hu
      have hincH : H.toHypergraph.Inc f u :=
        (PaintingOrDrawing.toHypergraph_inc (Γ := PaintingOrDrawing.drawing H)).mpr ⟨hfE, hu, huf⟩
      have hfA₁ : f ∈ A₁.edgeSet := by
        rcases (hsep₁.edgeSet_union.symm ▸ hfE : f ∈ A₁.edgeSet ∪ B₁.edgeSet) with hfA | hfB
        · exact hfA
        · exact absurd (B₁.vertex_mem_of_inc ((inc_iff_of_le hsep₁.right_le hfB).mpr hincH))
            hu_not_B₁
      obtain ⟨D, hD, hDs, hDlen, hDV, hfD⟩ :=
        theorem_7_2_proof hS ‹ConnectedSpace S› hE hResp hrad hslope hA₁B₁ hfA₁
      obtain ⟨w, hwD⟩ := (circuit_length_eq_two_mul_ncard hrad.2.1 hD hDs).2
      have hw_sep : w ∈ (A₁ ∩ B₁).vertexSet := hDV hwD
      obtain ⟨p, hp, ha⟩ := hassoc_sep w hw_sep
      have hu_insD : u ∈ ins D :=
        (hslope D hD hDs hDlen).1.isClosed.closure_subset_iff.mpr hfD huf
      have hwA : ({w} : Set S) ∈ H.A := Or.inl (Or.inl ⟨w, hwD.2, rfl⟩)
      have hduw : d {u} {w} ≤ 3 := by
        rw [hd_eq {u} huA {w} hwA, GM11.tangleMetric_comm]
        calc tangleMetric H K ins θ {w} {u}
          _ ≤ (D.V ∩ H.V).ncard :=
              (tangleMetric_vertex_le_of_circuit hS hrad hslope hD hDs hDlen hwD huA
                ⟨u, rfl, hu_insD⟩).2
          _ ≤ (A₁ ∩ B₁).vertexSet.ncard := ncard_le_ncard hDV (A₁ ∩ B₁).vertexSet_finite
          _ ≤ (subBd Δ ∩ H.U).ncard := hord_le
          _ ≤ 3 := hcard_Δ
      exact ⟨p, hp, w, hwD.2, ha, hduw⟩

/-- If `H` is a drawing in a connected closed non-spherical surface `S` with `H.E.Nonempty` and a
respectful tangle `T` of order `θ > 15` with metric `d`, and `u, v ∈ H.V` satisfy `¬ d {u} {v} <
12`,
then there is no continuous closed curve `φ : C(Circle, S)` with `(range φ ∩ H.U).encard ≤ 3`,
`u ∈ curveIns φ`, and `v ∈ curveIns φ`. -/
theorem not_exists_curve_of_dist_ge_twelve [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S)
    {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hθ : 15 < θ) (hE : H.E.Nonempty) (hd : HasTangleMetric H θ T d)
    {u v : S} (hu : u ∈ H.V) (hv : v ∈ H.V) (hdist : ¬ d {u} {v} < 12) :
    ¬ ∃ φ : C(Circle, S),
      (range φ ∩ H.U).encard ≤ 3 ∧ u ∈ curveIns φ ∧ v ∈ curveIns φ := by
  rintro ⟨φ, hencard, hu_ins, hv_ins⟩
  have hfin : (range φ ∩ H.U).Finite :=
    Set.finite_of_encard_le_coe (k := 3) hencard
  have hcard : (range φ ∩ H.U).ncard ≤ 3 :=
    Nat.cast_le (α := ℕ∞).mp (by rw [hfin.cast_ncard_eq]; exact hencard)
  obtain ⟨hResp, K, ins, hrad, hslope, hd_eq⟩ := id hd
  have hsl : IsSlope K (2 * θ) ins :=
    GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing H) hS hResp.2.1.isPretangle hrad.2.1.1
      hslope
  obtain ⟨p_u, hp_u, w_u, hw_u, ha_u, hdu⟩ :=
    exists_assocVertex_dist_le_three_of_mem_curveIns hS hns hθ hE hResp hrad hslope hd_eq
      hfin hcard hu hu_ins
  obtain ⟨p_v, hp_v, w_v, hw_v, ha_v, hdv⟩ :=
    exists_assocVertex_dist_le_three_of_mem_curveIns hS hns hθ hE hResp hrad hslope hd_eq
      hfin hcard hv hv_ins
  have hdw : d {w_u} {w_v} ≤ 4 :=
    dist_le_four_of_assocVertex_on_curve hS hE hResp hrad hslope hd_eq
      hfin hcard hp_u hp_v ha_u ha_v
  have huA : ({u} : Set S) ∈ H.A := Or.inl (Or.inl ⟨u, hu, rfl⟩)
  have hvA : ({v} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
  have hwuA : ({w_u} : Set S) ∈ H.A := Or.inl (Or.inl ⟨w_u, hw_u, rfl⟩)
  have hwvA : ({w_v} : Set S) ∈ H.A := Or.inl (Or.inl ⟨w_v, hw_v, rfl⟩)
  have hdv_symm : d {w_v} {v} = d {v} {w_v} := by
    rw [hd_eq {w_v} hwvA {v} hvA, hd_eq {v} hvA {w_v} hwvA, GM11.tangleMetric_comm]
  have htri₁ : d {u} {v} ≤ d {u} {w_u} + d {w_u} {v} := by
    rw [hd_eq {u} huA {v} hvA, hd_eq {u} huA {w_u} hwuA, hd_eq {w_u} hwuA {v} hvA]
    exact GM11.tangleMetric_triangle hS hrad.2.1 hsl {u} {w_u} {v}
  have htri₂ : d {w_u} {v} ≤ d {w_u} {w_v} + d {w_v} {v} := by
    rw [hd_eq {w_u} hwuA {v} hvA, hd_eq {w_u} hwuA {w_v} hwvA, hd_eq {w_v} hwvA {v} hvA]
    exact GM11.tangleMetric_triangle hS hrad.2.1 hsl {w_u} {w_v} {v}
  exact hdist (by omega)

end

end GraphMinor.GM14
