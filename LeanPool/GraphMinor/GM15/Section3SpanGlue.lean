/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Defs
public import LeanPool.GraphMinor.GM15.Cited
public import LeanPool.GraphMinor.GM15.Section3
public import LeanPool.GraphMinor.GM15.Section4
import LeanPool.GraphMinor.GM11.DrawingOps
import LeanPool.GraphMinor.GM11.ArcDrawings
import LeanPool.GraphMinor.GM11.PaintingCells
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.GM14.Section6c
import LeanPool.GraphMinor.GM16.PathIsoCard
import LeanPool.GraphMinor.GM16.LineDrawingPath
import LeanPool.GraphMinor.GM16.PathDrawingOnLine
import LeanPool.GraphMinor.GM16.FiniteDrawingUnion
import LeanPool.GraphMinor.GM16.GraphDrawingSpanEmbedding
import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.Surface.CutLift
import LeanPool.GraphMinor.Surface.DiscArcs

/-!
# Shared Drawing and Span-Embedding Gluing for Graph Minors XV, Section 3

This file provides the common infrastructure used in the proofs of (3.3), (3.4), and (3.5) of
*Graph Minors XV. Giant steps*:
- Lifting a drawing `H : Drawing S_hat`, its `SpanEmbedding H G`, and its tangle across a
  continuous embedding `g : S_hat → S'` on a compact set `K ⊆ S_hat` containing `H.U`.
- Drawing a finite family of pairwise vertex-disjoint `η₁(H₁)`-paths `P : Fin m → Graph α β`
  along pairwise disjoint lines `L : Fin m → Set S'` meeting `H₁.U` only at their endpoints,
  and gluing them with `(H₁, η₁)` to obtain `(H', η')`.
- Proving the normality, vertex-intersection, and subdrawing decomposition formulas for
  pinched splits `(P₁^XII, P₂^XII)` used when applying Graph Minors XII, (5.1), (5.2), and (6.1).
- Proving `IsTangle` and `IsControllingTangle` for `GM12.inducedAcross` and
  `GM12.inducedBySubgraph`.
-/

@[expose] public section

namespace GraphMinor.GM15

open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 GM16

universe u v w

/-! ## 1. Lifting a Drawing and SpanEmbedding Along a Compact Embedding -/

section LiftDrawing

variable {S' S_hat : Type w} [TopologicalSpace S'] [T2Space S']
  [TopologicalSpace S_hat] [T2Space S_hat]

/-- Lift a drawing `H : Drawing S_hat` with `H.U ⊆ K` along a continuous injection `g : S_hat → S'`
with continuous left inverse `f : S' → S_hat` on the compact set `K`. -/
noncomputable def liftDrawingOn {K : Set S_hat} (hK : IsCompact K)
    {g : S_hat → S'} {f : S' → S_hat}
    (hg : ContinuousOn g K) (hf : ContinuousOn f (g '' K)) (hl : LeftInvOn f g K)
    (H : Drawing S_hat) (hHU : H.U ⊆ K) : Drawing S' where
  U := g '' H.U
  V := g '' H.V
  V_subset_U := image_mono H.V_subset_U
  isClosed_U := (hK.of_isClosed_subset H.isClosed_U hHU).image_of_continuousOn
    (hg.mono hHU) |>.isClosed
  finite_V := H.finite_V.image g
  finite_edges := by
    have hinj : InjOn g K := hl.injOn
    have hUV : g '' H.U \ g '' H.V = g '' (H.U \ H.V) := by
      ext x
      constructor
      · rintro ⟨⟨y, hyU, rfl⟩, hyV⟩
        exact ⟨y, ⟨hyU, fun h => hyV ⟨y, h, rfl⟩⟩, rfl⟩
      · rintro ⟨y, ⟨hyU, hyV⟩, rfl⟩
        refine ⟨⟨y, hyU, rfl⟩, ?_⟩
        rintro ⟨z, hzV, hzy⟩
        exact hyV (hinj (H.V_subset_U.trans hHU hzV) (hHU hyU) hzy ▸ hzV)
    have hUV_sub : H.U \ H.V ⊆ K := sdiff_subset.trans hHU
    rw [hUV, GM11.arcComponentsIn_image (hg.mono hUV_sub)
      (hf.mono (image_mono hUV_sub)) (hl.mono hUV_sub)]
    exact H.finite_edges.image (image g)
  edge_cond := by
    have hinj : InjOn g K := hl.injOn
    have hUV : g '' H.U \ g '' H.V = g '' (H.U \ H.V) := by
      ext x
      constructor
      · rintro ⟨⟨y, hyU, rfl⟩, hyV⟩
        exact ⟨y, ⟨hyU, fun h => hyV ⟨y, h, rfl⟩⟩, rfl⟩
      · rintro ⟨y, ⟨hyU, hyV⟩, rfl⟩
        refine ⟨⟨y, hyU, rfl⟩, ?_⟩
        rintro ⟨z, hzV, hzy⟩
        exact hyV (hinj (H.V_subset_U.trans hHU hzV) (hHU hyU) hzy ▸ hzV)
    have hUV_sub : H.U \ H.V ⊆ K := sdiff_subset.trans hHU
    intro e' he'
    rw [hUV, GM11.arcComponentsIn_image (hg.mono hUV_sub)
      (hf.mono (image_mono hUV_sub)) (hl.mono hUV_sub)] at he'
    rcases he' with ⟨e, he, rfl⟩
    have he_U : e ⊆ H.U := fun x hx => (he.2.1 hx).1
    have hcl_sub : closure e ⊆ K := (H.isClosed_U.closure_subset_iff.mpr he_U).trans hHU
    have hcl_comp : IsCompact (closure e) := hK.of_isClosed_subset isClosed_closure hcl_sub
    have hcl_img : g '' closure e = closure (g '' e) :=
      image_closure_of_isCompact hcl_comp (hg.mono hcl_sub)
    have hcap : closure (g '' e) ∩ g '' H.V = g '' (closure e ∩ H.V) := by
      rw [← hcl_img, ← hinj.image_inter hcl_sub (H.V_subset_U.trans hHU)]
    obtain ⟨e_homeo, he_homeo⟩ := exists_homeomorph_image
      (hg.mono hcl_sub) (hf.mono (image_mono hcl_sub)) (hl.mono hcl_sub)
    rcases H.edge_cond e he with ⟨u, v, huv, hcap_e, ⟨φ, hφ0, hφ1⟩⟩ | ⟨u, hcap_e, ⟨φ⟩⟩
    · left
      have huK : u ∈ K := hcl_sub (by
        have : u ∈ closure e ∩ H.V := hcap_e ▸ mem_insert u {v}
        exact this.1)
      have hvK : v ∈ K := hcl_sub (by
        have : v ∈ closure e ∩ H.V := hcap_e ▸ mem_insert_of_mem u rfl
        exact this.1)
      refine ⟨g u, g v, fun h => huv (hinj huK hvK h), ?_, ?_⟩
      · rw [hcap, hcap_e, image_pair]
      · rw [← hcl_img]
        exact ⟨φ.trans e_homeo,
          (he_homeo (φ 0)).trans (congrArg g hφ0),
          (he_homeo (φ 1)).trans (congrArg g hφ1)⟩
    · right
      refine ⟨g u, ?_, ?_⟩
      · rw [hcap, hcap_e, image_singleton]
      · rw [← hcl_img]
        exact ⟨φ.trans e_homeo⟩

omit [T2Space S_hat] in
@[simp]
theorem liftDrawingOn_U {K : Set S_hat} (hK : IsCompact K)
    {g : S_hat → S'} {f : S' → S_hat}
    (hg : ContinuousOn g K) (hf : ContinuousOn f (g '' K)) (hl : LeftInvOn f g K)
    (H : Drawing S_hat) (hHU : H.U ⊆ K) :
    (liftDrawingOn hK hg hf hl H hHU).U = g '' H.U := rfl

omit [T2Space S_hat] in
@[simp]
theorem liftDrawingOn_V {K : Set S_hat} (hK : IsCompact K)
    {g : S_hat → S'} {f : S' → S_hat}
    (hg : ContinuousOn g K) (hf : ContinuousOn f (g '' K)) (hl : LeftInvOn f g K)
    (H : Drawing S_hat) (hHU : H.U ⊆ K) :
    (liftDrawingOn hK hg hf hl H hHU).V = g '' H.V := rfl

omit [T2Space S_hat] in
theorem liftDrawingOn_E {K : Set S_hat} (hK : IsCompact K)
    {g : S_hat → S'} {f : S' → S_hat}
    (hg : ContinuousOn g K) (hf : ContinuousOn f (g '' K)) (hl : LeftInvOn f g K)
    (H : Drawing S_hat) (hHU : H.U ⊆ K) :
    (liftDrawingOn hK hg hf hl H hHU).E = image g '' H.E := by
  have hinj : InjOn g K := hl.injOn
  have hUV : g '' H.U \ g '' H.V = g '' (H.U \ H.V) := by
    ext x
    constructor
    · rintro ⟨⟨y, hyU, rfl⟩, hyV⟩
      exact ⟨y, ⟨hyU, fun h => hyV ⟨y, h, rfl⟩⟩, rfl⟩
    · rintro ⟨y, ⟨hyU, hyV⟩, rfl⟩
      refine ⟨⟨y, hyU, rfl⟩, ?_⟩
      rintro ⟨z, hzV, hzy⟩
      exact hyV (hinj (H.V_subset_U.trans hHU hzV) (hHU hyU) hzy ▸ hzV)
  have hUV_sub : H.U \ H.V ⊆ K := sdiff_subset.trans hHU
  change arcComponentsIn (g '' H.U \ g '' H.V) = image g '' H.E
  rw [hUV]
  exact GM11.arcComponentsIn_image (hg.mono hUV_sub)
    (hf.mono (image_mono hUV_sub)) (hl.mono hUV_sub)

omit [T2Space S_hat] in
theorem liftDrawingOn_closure_edge {K : Set S_hat} (hK : IsCompact K)
    {g : S_hat → S'} {f : S' → S_hat}
    (hg : ContinuousOn g K) (_hf : ContinuousOn f (g '' K)) (_hl : LeftInvOn f g K)
    {H : Drawing S_hat} (hHU : H.U ⊆ K) {e : Set S_hat} (he : e ∈ H.E) :
    closure (g '' e) = g '' closure e := by
  have he_U : e ⊆ H.U := fun x hx => (he.2.1 hx).1
  have hcl_sub : closure e ⊆ K := (H.isClosed_U.closure_subset_iff.mpr he_U).trans hHU
  have hcl_comp : IsCompact (closure e) := hK.of_isClosed_subset isClosed_closure hcl_sub
  exact (image_closure_of_isCompact hcl_comp (hg.mono hcl_sub)).symm

/-- Lift a `SpanEmbedding H G` along `(g, f)` to a `SpanEmbedding (liftDrawingOn ...) G`. -/
noncomputable def liftSpanEmbeddingOn {α : Type u} {β : Type v} {G : Graph α β}
    {K : Set S_hat} (hK : IsCompact K)
    {g : S_hat → S'} {f : S' → S_hat}
    (hg : ContinuousOn g K) (hf : ContinuousOn f (g '' K)) (hl : LeftInvOn f g K)
    {H : Drawing S_hat} (hHU : H.U ⊆ K) (η : SpanEmbedding H G) :
    SpanEmbedding (liftDrawingOn hK hg hf hl H hHU) G where
  imageGraph := η.imageGraph
  vMap x := η.vMap (f x)
  eMap e' := η.eMap (f '' e')
  imageGraph_le := η.imageGraph_le
  bijOn_v := by
    have hV_sub : H.V ⊆ K := H.V_subset_U.trans hHU
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      dsimp only
      rw [hl (hV_sub hv)]
      exact η.bijOn_v.mapsTo hv
    · rintro _ ⟨v₁, hv₁, rfl⟩ _ ⟨v₂, hv₂, rfl⟩ heq
      dsimp only at heq
      rw [hl (hV_sub hv₁), hl (hV_sub hv₂)] at heq
      exact congrArg g (η.bijOn_v.injOn hv₁ hv₂ heq)
    · intro a ha
      obtain ⟨v, hv, rfl⟩ := η.bijOn_v.surjOn ha
      refine ⟨g v, ⟨v, hv, rfl⟩, ?_⟩
      dsimp only
      rw [hl (hV_sub hv)]
  bijOn_e := by
    rw [liftDrawingOn_E hK hg hf hl H hHU]
    have hfg : ∀ {e : Set S_hat}, e ∈ H.E → f '' (g '' e) = e := by
      intro e he
      have he_sub : e ⊆ K := fun x hx => hHU (he.2.1 hx).1
      exact hl.image_image' he_sub
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨e, he, rfl⟩
      dsimp only
      rw [hfg he]
      exact η.bijOn_e.mapsTo he
    · rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩ heq
      dsimp only at heq
      rw [hfg he₁, hfg he₂] at heq
      exact congrArg (image g) (η.bijOn_e.injOn he₁ he₂ heq)
    · intro b hb
      obtain ⟨e, he, rfl⟩ := η.bijOn_e.surjOn hb
      refine ⟨g '' e, ⟨e, he, rfl⟩, ?_⟩
      dsimp only
      rw [hfg he]
  inc_iff := by
    rw [liftDrawingOn_E hK hg hf hl H hHU]
    rintro _ ⟨e, he, rfl⟩ _ ⟨v, hv, rfl⟩
    have he_U : e ⊆ H.U := fun x hx => (he.2.1 hx).1
    have he_sub : e ⊆ K := he_U.trans hHU
    have hcl_sub : closure e ⊆ K := (H.isClosed_U.closure_subset_iff.mpr he_U).trans hHU
    have hv_sub : v ∈ K := H.V_subset_U.trans hHU hv
    change η.imageGraph.Inc (η.eMap (f '' (g '' e))) (η.vMap (f (g v))) ↔ g v ∈ closure (g '' e)
    rw [hl.image_image' he_sub, hl hv_sub, η.inc_iff e he v hv,
      liftDrawingOn_closure_edge hK hg hf hl hHU he]
    exact ⟨fun h => ⟨v, h, rfl⟩, fun ⟨w, hw, hgw⟩ => hl.injOn (hcl_sub hw) hv_sub hgw ▸ hw⟩

end LiftDrawing

/-! ## 2. Gluing a Base Drawing and SpanEmbedding with Path Drawings on Disjoint Lines -/

section GluePaths

variable {α : Type u} {β : Type v} {S' : Type w} [TopologicalSpace S'] [T2Space S']

omit [T2Space S'] in
private lemma isCompact_of_isLineWithEnds' {L : Set S'} {u v : S'}
    (hL : IsLineWithEnds L u v) : IsCompact L := by
  obtain ⟨ψ, _, _⟩ := hL
  have hEq : L = range (fun s : unitInterval => (ψ s).1) := by
    ext x
    exact ⟨fun hx => ⟨ψ.symm ⟨x, hx⟩, by simp⟩, fun ⟨s, hs⟩ => hs ▸ (ψ s).2⟩
  rw [hEq]
  exact isCompact_range (continuous_subtype_val.comp ψ.continuous)

private theorem paths_on_gluing_arcs_have_drawings
    {α : Type u}
    {β : Type v}
    {S' : Type w}
    [TopologicalSpace S']
    [T2Space S']
    {G : Graph α β}
    (H₁ : Drawing S')
    (η₁ : SpanEmbedding H₁ G)
    {m : ℕ}
    (u' : Fin m → S')
    (v' : Fin m → S')
    (P : Fin m → Graph α β)
    (L : Fin m → Set S')
    (hP : ∀ (i : Fin m), IsHPathWithEnds G η₁.imageGraph (P i) (η₁.vMap (u' i)) (η₁.vMap (v' i)))
    (hL : ∀ (i : Fin m), IsLineWithEnds (L i) (u' i) (v' i))
    (huv_ne : ∀ (i : Fin m), u' i ≠ v' i) :
    ∀ (i : Fin m), ∃ (D_i : Drawing S') (η_i : SpanEmbedding D_i G),
      D_i.U = L i ∧ D_i.IsPathBetween (u' i) (v' i) ∧ u' i ∈ D_i.V ∧ v' i
      ∈ D_i.V ∧ η_i.imageGraph = P i ∧ η_i.vMap (u' i) = η₁.vMap (u' i) ∧ η_i.vMap (v' i) =
      η₁.vMap (v' i) := by
  intro i
  have hα : Nonempty α := ⟨η₁.vMap (u' i)⟩
  have hβ : Nonempty β := ⟨η₁.eMap ∅⟩
  obtain ⟨Γ_i, hU_i, hLeft_i, hRight_i⟩ :=
    GM16.exists_path_drawing_on_line (hP i).2.1 (hP i).2.2.1 (hL i) (huv_ne i)
  obtain ⟨η_i, hIm_i, hv_i, _⟩ :=
    GM16.exists_spanEmbedding_of_graphDrawing (hP i).2.1.1 Γ_i
  have hu_mem_P : η₁.vMap (u' i) ∈ V(P i) := IsGraphPathWithEnds.left_mem (hP i).2.1
  have hv_mem_P : η₁.vMap (v' i) ∈ V(P i) := IsGraphPathWithEnds.right_mem (hP i).2.1
  let u_P : V(P i) := ⟨η₁.vMap (u' i), hu_mem_P⟩
  let v_P : V(P i) := ⟨η₁.vMap (v' i), hv_mem_P⟩
  have h_u_eq : (Γ_i.iso.vertexEquiv u_P).val = u' i := hLeft_i u_P rfl
  have h_v_eq : (Γ_i.iso.vertexEquiv v_P).val = v' i := hRight_i v_P rfl
  have hu'_V : u' i ∈ Γ_i.drawing.V := h_u_eq ▸ (Γ_i.iso.vertexEquiv u_P).property
  have hv'_V : v' i ∈ Γ_i.drawing.V := h_v_eq ▸ (Γ_i.iso.vertexEquiv v_P).property
  have h_symm_u : Γ_i.iso.vertexEquiv.symm ⟨u' i, hu'_V⟩ = u_P := by
    apply Γ_i.iso.vertexEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext h_u_eq.symm
  have h_symm_v : Γ_i.iso.vertexEquiv.symm ⟨v' i, hv'_V⟩ = v_P := by
    apply Γ_i.iso.vertexEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext h_v_eq.symm
  have hvMap_u : η_i.vMap (u' i) = η₁.vMap (u' i) :=
    (hv_i ⟨u' i, hu'_V⟩).trans (congrArg Subtype.val h_symm_u)
  have hvMap_v : η_i.vMap (v' i) = η₁.vMap (v' i) :=
    (hv_i ⟨v' i, hv'_V⟩).trans (congrArg Subtype.val h_symm_v)
  have hPath_i : Γ_i.drawing.IsPathBetween (u' i) (v' i) :=
    GM16.drawing_isPathBetween_of_isLine_U (hU_i.symm ▸ hL i) (huv_ne i) hu'_V hv'_V
  exact ⟨Γ_i.drawing, η_i, hU_i, hPath_i, hu'_V, hv'_V, hIm_i, hvMap_u, hvMap_v⟩

private theorem initial_drawing_and_gluing_paths_only_meet_at_vertices
    {S' : Type w}
    [TopologicalSpace S']
    (H₁ : Drawing S')
    {m : ℕ}
    (u' : Fin m → S')
    (v' : Fin m → S')
    (L : Fin m → Set S')
    (hu' : ∀ (i : Fin m), u' i ∈ H₁.V)
    (hv' : ∀ (i : Fin m), v' i ∈ H₁.V)
    (hL_disj : Pairwise fun i j => Disjoint (L i) (L j))
    (hL_inter : ∀ (i : Fin m), L i ∩ H₁.U = {u' i, v' i})
    (P' : Fin m → Drawing S')
    (hP'_U : ∀ (i : Fin m), (P' i).U = L i) :
    ∀ o₁ ∈ univ, ∀ o₂ ∈ univ, o₁ ≠ o₂ → ((Option.elim' H₁ P') o₁).U ∩ ((Option.elim' H₁ P') o₂).U
      ⊆ H₁.V := by
  let D_fam := Option.elim' H₁ P'
  rintro (_ | i) _ (_ | j) _ hne x ⟨hx₁, hx₂⟩
  · exact (hne rfl).elim
  · change x ∈ H₁.U at hx₁
    change x ∈ (P' j).U at hx₂
    rw [hP'_U j] at hx₂
    have hx_pair : x ∈ ({u' j, v' j} : Set S') := hL_inter j ▸ ⟨hx₂, hx₁⟩
    rcases hx_pair with rfl | rfl
    · exact hu' j
    · exact hv' j
  · change x ∈ (P' i).U at hx₁
    change x ∈ H₁.U at hx₂
    rw [hP'_U i] at hx₁
    have hx_pair : x ∈ ({u' i, v' i} : Set S') := hL_inter i ▸ ⟨hx₁, hx₂⟩
    rcases hx_pair with rfl | rfl
    · exact hu' i
    · exact hv' i
  · have hij : i ≠ j := fun h => hne (congrArg some h)
    change x ∈ (P' i).U at hx₁
    change x ∈ (P' j).U at hx₂
    rw [hP'_U i] at hx₁
    rw [hP'_U j] at hx₂
    exact (Set.disjoint_left.mp (hL_disj hij) hx₁ hx₂).elim

private theorem glued_drawing_vertex_map_bijective
    {α : Type u}
    {β : Type v}
    {S' : Type w}
    [TopologicalSpace S']
    {G : Graph α β}
    (H₁ : Drawing S')
    (η₁ : SpanEmbedding H₁ G)
    {m : ℕ}
    (u' : Fin m → S')
    (v' : Fin m → S')
    (P : Fin m → Graph α β)
    (hu' : ∀ (i : Fin m), u' i ∈ H₁.V)
    (hv' : ∀ (i : Fin m), v' i ∈ H₁.V)
    (hP : ∀ (i : Fin m), IsHPathWithEnds G η₁.imageGraph (P i) (η₁.vMap (u' i)) (η₁.vMap (v' i)))
    (hP_disj : Pairwise fun i j => Disjoint V(P i) V(P j))
    (P' : Fin m → Drawing S')
    (η_P : (i : Fin m) → SpanEmbedding (P' i) G)
    (hu'_P'V : ∀ (i : Fin m), u' i ∈ (P' i).V)
    (hv'_P'V : ∀ (i : Fin m), v' i ∈ (P' i).V)
    (hη_P_im : ∀ (i : Fin m), (η_P i).imageGraph = P i)
    (hη_P_u : ∀ (i : Fin m), (η_P i).vMap (u' i) = η₁.vMap (u' i))
    (hη_P_v : ∀ (i : Fin m), (η_P i).vMap (v' i) = η₁.vMap (v' i))
    (H' : Drawing S')
    (hH'_V : H'.V = H₁.V ∪ ⋃ i, (P' i).V)
    (hSub_H₁ : H₁.IsSubdrawing H')
    (hSub_P' : ∀ (i : Fin m), (P' i).IsSubdrawing H')
    (vm : S' → α)
    (hvm_H₁ : ∀ x ∈ H₁.V, vm x = η₁.vMap x)
    (hvm_P' : ∀ (i : Fin m), ∀ x ∈ (P' i).V, vm x = (η_P i).vMap x)
    (hV_ImG : V((subgraphUnion G η₁.imageGraph (subgraphSUnion G (range P)))) = V(η₁.imageGraph) ∪
      ⋃ i, V(P i)) :
    BijOn vm H'.V V((subgraphUnion G η₁.imageGraph (subgraphSUnion G (range P)))) := by
  let ImG := subgraphUnion G η₁.imageGraph (subgraphSUnion G (range P))
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [hH'_V] at hx
    rw [hV_ImG]
    rcases hx with hx₁ | hxP
    · rw [hvm_H₁ x hx₁]
      exact Or.inl (η₁.bijOn_v.mapsTo hx₁)
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxP
      rw [hvm_P' i x hxi]
      exact Or.inr (mem_iUnion.mpr ⟨i, hη_P_im i ▸ (η_P i).bijOn_v.mapsTo hxi⟩)
  · intro x hx y hy hxy
    rw [hH'_V] at hx hy
    rcases hx with hx₁ | hxP <;> rcases hy with hy₁ | hyP
    · rw [hvm_H₁ x hx₁, hvm_H₁ y hy₁] at hxy
      exact η₁.bijOn_v.injOn hx₁ hy₁ hxy
    · obtain ⟨j, hyj⟩ := mem_iUnion.mp hyP
      have hvy_im : vm y ∈ V(P j) ∩ V(η₁.imageGraph) := by
        refine ⟨?_, ?_⟩
        · rw [hvm_P' j y hyj, ← hη_P_im j]
          exact (η_P j).bijOn_v.mapsTo hyj
        · rw [← hxy, hvm_H₁ x hx₁]
          exact η₁.bijOn_v.mapsTo hx₁
      rw [(hP j).2.2.2.2.2.1] at hvy_im
      rcases hvy_im with h_u | h_v
      · have hy_u : y = u' j :=
          (η_P j).bijOn_v.injOn hyj (hu'_P'V j) (by rw [← hvm_P' j y hyj, h_u, hη_P_u j])
        subst hy_u
        rw [hvm_H₁ x hx₁, hvm_H₁ (u' j) (hu' j)] at hxy
        exact η₁.bijOn_v.injOn hx₁ (hu' j) hxy
      · rw [mem_singleton_iff] at h_v
        have hy_v : y = v' j :=
          (η_P j).bijOn_v.injOn hyj (hv'_P'V j) (by rw [← hvm_P' j y hyj, h_v, hη_P_v j])
        subst hy_v
        rw [hvm_H₁ x hx₁, hvm_H₁ (v' j) (hv' j)] at hxy
        exact η₁.bijOn_v.injOn hx₁ (hv' j) hxy
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxP
      have hvx_im : vm x ∈ V(P i) ∩ V(η₁.imageGraph) := by
        refine ⟨?_, ?_⟩
        · rw [hvm_P' i x hxi, ← hη_P_im i]
          exact (η_P i).bijOn_v.mapsTo hxi
        · rw [hxy, hvm_H₁ y hy₁]
          exact η₁.bijOn_v.mapsTo hy₁
      rw [(hP i).2.2.2.2.2.1] at hvx_im
      rcases hvx_im with h_u | h_v
      · have hx_u : x = u' i :=
          (η_P i).bijOn_v.injOn hxi (hu'_P'V i) (by rw [← hvm_P' i x hxi, h_u, hη_P_u i])
        subst hx_u
        rw [hvm_H₁ (u' i) (hu' i), hvm_H₁ y hy₁] at hxy
        exact η₁.bijOn_v.injOn (hu' i) hy₁ hxy
      · rw [mem_singleton_iff] at h_v
        have hx_v : x = v' i :=
          (η_P i).bijOn_v.injOn hxi (hv'_P'V i) (by rw [← hvm_P' i x hxi, h_v, hη_P_v i])
        subst hx_v
        rw [hvm_H₁ (v' i) (hv' i), hvm_H₁ y hy₁] at hxy
        exact η₁.bijOn_v.injOn (hv' i) hy₁ hxy
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxP
      obtain ⟨j, hyj⟩ := mem_iUnion.mp hyP
      by_cases hij : i = j
      · subst hij
        rw [hvm_P' i x hxi, hvm_P' i y hyj] at hxy
        exact (η_P i).bijOn_v.injOn hxi hyj hxy
      · exfalso
        have hx_Pi : vm x ∈ V(P i) := by
          rw [hvm_P' i x hxi, ← hη_P_im i]
          exact (η_P i).bijOn_v.mapsTo hxi
        have hy_Pj : vm y ∈ V(P j) := by
          rw [hvm_P' j y hyj, ← hη_P_im j]
          exact (η_P j).bijOn_v.mapsTo hyj
        exact Set.disjoint_left.mp (hP_disj hij) hx_Pi (hxy ▸ hy_Pj)
  · intro a ha
    rw [hV_ImG] at ha
    rcases ha with ha₁ | haP
    · obtain ⟨x, hx₁, rfl⟩ := η₁.bijOn_v.surjOn ha₁
      exact ⟨x, hSub_H₁.1 hx₁, hvm_H₁ x hx₁⟩
    · obtain ⟨i, hai⟩ := mem_iUnion.mp haP
      obtain ⟨x, hxi, rfl⟩ := (η_P i).bijOn_v.surjOn (hη_P_im i ▸ hai)
      exact ⟨x, (hSub_P' i).1 hxi, hvm_P' i x hxi⟩

private theorem glued_drawing_edge_map_bijective
    {α : Type u}
    {β : Type v}
    {S' : Type w}
    [TopologicalSpace S']
    {G : Graph α β}
    (H₁ : Drawing S')
    (η₁ : SpanEmbedding H₁ G)
    {m : ℕ}
    (u' : Fin m → S')
    (v' : Fin m → S')
    (P : Fin m → Graph α β)
    (hP : ∀ (i : Fin m), IsHPathWithEnds G η₁.imageGraph (P i) (η₁.vMap (u' i)) (η₁.vMap (v' i)))
    (P' : Fin m → Drawing S')
    (η_P : (i : Fin m) → SpanEmbedding (P' i) G)
    (hη_P_im : ∀ (i : Fin m), (η_P i).imageGraph = P i)
    (H' : Drawing S')
    (hH'_E : H'.E = H₁.E ∪ ⋃ i, (P' i).E)
    (hSub_H₁ : H₁.IsSubdrawing H')
    (hSub_P' : ∀ (i : Fin m), (P' i).IsSubdrawing H')
    (em : Set S' → β)
    (hem_H₁ : ∀ e ∈ H₁.E, em e = η₁.eMap e)
    (hem_P' : ∀ (i : Fin m), ∀ e ∈ (P' i).E, em e = (η_P i).eMap e)
    (hE_ImG : E((subgraphUnion G η₁.imageGraph (subgraphSUnion G (range P)))) = E(η₁.imageGraph) ∪
      ⋃ i, E(P i))
    (hPE_disj : Pairwise fun i j => Disjoint E(P i) E(P j)) :
    BijOn em H'.E E((subgraphUnion G η₁.imageGraph (subgraphSUnion G (range P)))) := by
  let ImG := subgraphUnion G η₁.imageGraph (subgraphSUnion G (range P))
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rw [hH'_E] at he
    rw [hE_ImG]
    rcases he with he₁ | heP
    · rw [hem_H₁ e he₁]
      exact Or.inl (η₁.bijOn_e.mapsTo he₁)
    · obtain ⟨i, hei⟩ := mem_iUnion.mp heP
      rw [hem_P' i e hei]
      exact Or.inr (mem_iUnion.mpr ⟨i, hη_P_im i ▸ (η_P i).bijOn_e.mapsTo hei⟩)
  · intro e₁ he₁ e₂ he₂ heq
    rw [hH'_E] at he₁ he₂
    rcases he₁ with he₁ | he₁P <;> rcases he₂ with he₂ | he₂P
    · rw [hem_H₁ e₁ he₁, hem_H₁ e₂ he₂] at heq
      exact η₁.bijOn_e.injOn he₁ he₂ heq
    · obtain ⟨j, he₂j⟩ := mem_iUnion.mp he₂P
      exfalso
      have h₁ : em e₁ ∈ E(η₁.imageGraph) := hem_H₁ e₁ he₁ ▸ η₁.bijOn_e.mapsTo he₁
      have h₂ : em e₂ ∈ E(P j) := hem_P' j e₂ he₂j ▸ hη_P_im j ▸ (η_P j).bijOn_e.mapsTo he₂j
      exact Set.disjoint_left.mp (hP j).2.2.2.2.2.2 (heq ▸ h₂) h₁
    · obtain ⟨i, he₁i⟩ := mem_iUnion.mp he₁P
      exfalso
      have h₁ : em e₁ ∈ E(P i) := hem_P' i e₁ he₁i ▸ hη_P_im i ▸ (η_P i).bijOn_e.mapsTo he₁i
      have h₂ : em e₂ ∈ E(η₁.imageGraph) := hem_H₁ e₂ he₂ ▸ η₁.bijOn_e.mapsTo he₂
      exact Set.disjoint_left.mp (hP i).2.2.2.2.2.2 h₁ (heq ▸ h₂)
    · obtain ⟨i, he₁i⟩ := mem_iUnion.mp he₁P
      obtain ⟨j, he₂j⟩ := mem_iUnion.mp he₂P
      by_cases hij : i = j
      · subst hij
        rw [hem_P' i e₁ he₁i, hem_P' i e₂ he₂j] at heq
        exact (η_P i).bijOn_e.injOn he₁i he₂j heq
      · exfalso
        have h₁ : em e₁ ∈ E(P i) := hem_P' i e₁ he₁i ▸ hη_P_im i ▸ (η_P i).bijOn_e.mapsTo he₁i
        have h₂ : em e₂ ∈ E(P j) := hem_P' j e₂ he₂j ▸ hη_P_im j ▸ (η_P j).bijOn_e.mapsTo he₂j
        exact Set.disjoint_left.mp (hPE_disj hij) h₁ (heq ▸ h₂)
  · intro b hb
    rw [hE_ImG] at hb
    rcases hb with hb₁ | hbP
    · obtain ⟨e, he₁, rfl⟩ := η₁.bijOn_e.surjOn hb₁
      exact ⟨e, hSub_H₁.2 he₁, hem_H₁ e he₁⟩
    · obtain ⟨i, hbi⟩ := mem_iUnion.mp hbP
      obtain ⟨e, hei, rfl⟩ := (η_P i).bijOn_e.surjOn (hη_P_im i ▸ hbi)
      exact ⟨e, (hSub_P' i).2 hei, hem_P' i e hei⟩

private theorem glued_drawing_incidence_iff_closure
    {α : Type u}
    {β : Type v}
    {S' : Type w}
    [TopologicalSpace S']
    [T2Space S']
    {G : Graph α β}
    (H₁ : Drawing S')
    (η₁ : SpanEmbedding H₁ G)
    {m : ℕ}
    (u' : Fin m → S')
    (v' : Fin m → S')
    (P : Fin m → Graph α β)
    (L : Fin m → Set S')
    (hu' : ∀ (i : Fin m), u' i ∈ H₁.V)
    (hv' : ∀ (i : Fin m), v' i ∈ H₁.V)
    (hP : ∀ (i : Fin m), IsHPathWithEnds G η₁.imageGraph (P i) (η₁.vMap (u' i)) (η₁.vMap (v' i)))
    (hP_disj : Pairwise fun i j => Disjoint V(P i) V(P j))
    (hL : ∀ (i : Fin m), IsLineWithEnds (L i) (u' i) (v' i))
    (hL_disj : Pairwise fun i j => Disjoint (L i) (L j))
    (hL_inter : ∀ (i : Fin m), L i ∩ H₁.U = {u' i, v' i})
    (P' : Fin m → Drawing S')
    (η_P : (i : Fin m) → SpanEmbedding (P' i) G)
    (hP'_U : ∀ (i : Fin m), (P' i).U = L i)
    (hu'_P'V : ∀ (i : Fin m), u' i ∈ (P' i).V)
    (hv'_P'V : ∀ (i : Fin m), v' i ∈ (P' i).V)
    (hη_P_im : ∀ (i : Fin m), (η_P i).imageGraph = P i)
    (hη_P_u : ∀ (i : Fin m), (η_P i).vMap (u' i) = η₁.vMap (u' i))
    (hη_P_v : ∀ (i : Fin m), (η_P i).vMap (v' i) = η₁.vMap (v' i))
    (H' : Drawing S')
    (hH'_V : H'.V = H₁.V ∪ ⋃ i, (P' i).V)
    (hH'_E : H'.E = H₁.E ∪ ⋃ i, (P' i).E)
    (hP'V_inter_H₁U : ∀ (i : Fin m), (P' i).V ∩ H₁.U = {u' i, v' i})
    (vm : S' → α)
    (em : Set S' → β)
    (hvm_H₁ : ∀ x ∈ H₁.V, vm x = η₁.vMap x)
    (hvm_P' : ∀ (i : Fin m), ∀ x ∈ (P' i).V, vm x = (η_P i).vMap x)
    (hem_H₁ : ∀ e ∈ H₁.E, em e = η₁.eMap e)
    (hem_P' : ∀ (i : Fin m), ∀ e ∈ (P' i).E, em e = (η_P i).eMap e)
    (hP_le : ∀ M ∈ range P, M ≤ G)
    (hSUnion_le : subgraphSUnion G (range P) ≤ G) :
    ∀ e ∈ H'.E, ∀ v ∈ H'.V, (subgraphUnion G η₁.imageGraph (subgraphSUnion G (range P))).Inc (em
      e) (vm v) ↔ v ∈ closure e := by
  let ImG := subgraphUnion G η₁.imageGraph (subgraphSUnion G (range P))
  intro e he v hv
  rw [hH'_E] at he
  rcases he with he₁ | heP
  · have hem_in : em e ∈ E(η₁.imageGraph) := hem_H₁ e he₁ ▸ η₁.bijOn_e.mapsTo he₁
    have hem_not_SUnion : em e ∉ E(subgraphSUnion G (range P)) := by
      rw [edgeSet_subgraphSUnion hP_le]
      intro hmem_u
      obtain ⟨M, ⟨i, rfl⟩, hmem⟩ := mem_iUnion₂.mp hmem_u
      exact Set.disjoint_left.mp (hP i).2.2.2.2.2.2 hmem hem_in
    have hInc_eq : ImG.Inc (em e) (vm v) ↔ η₁.imageGraph.Inc (η₁.eMap e) (vm v) := by
      rw [hem_H₁ e he₁]
      constructor
      · rintro ⟨w, hlink⟩
        rw [subgraphUnion_isLink η₁.imageGraph_le hSUnion_le] at hlink
        rcases hlink with hlink₁ | hlink₂
        · exact ⟨w, hlink₁⟩
        · exact (hem_not_SUnion (hem_H₁ e he₁ ▸ hlink₂.edge_mem)).elim
      · rintro ⟨w, hlink₁⟩
        exact ⟨w, (subgraphUnion_isLink η₁.imageGraph_le hSUnion_le).mpr (Or.inl hlink₁)⟩
    rw [hInc_eq]
    by_cases hv₁ : v ∈ H₁.V
    · rw [hvm_H₁ v hv₁, η₁.inc_iff e he₁ v hv₁]
    · have hv_P : ∃ i : Fin m, v ∈ (P' i).V := by
        rw [hH'_V] at hv
        exact mem_iUnion.mp (hv.resolve_left hv₁)
      obtain ⟨i, hvi⟩ := hv_P
      have hv_not_H₁U : v ∉ H₁.U := by
        intro hvU
        have hv_pair : v ∈ ({u' i, v' i} : Set S') := hP'V_inter_H₁U i ▸ ⟨hvi, hvU⟩
        rcases hv_pair with rfl | rfl
        · exact hv₁ (hu' i)
        · exact hv₁ (hv' i)
      have hv_not_cl : v ∉ closure e := by
        intro hv_cl
        have he_sub : e ⊆ H₁.U := fun x hx => (he₁.2.1 hx).1
        exact hv_not_H₁U (H₁.isClosed_U.closure_subset_iff.mpr he_sub hv_cl)
      have hvm_not_V₁ : vm v ∉ V(η₁.imageGraph) := by
        intro hvm_in
        have hvm_Pi : vm v ∈ V(P i) :=
          hvm_P' i v hvi ▸ hη_P_im i ▸ (η_P i).bijOn_v.mapsTo hvi
        have hvm_inter : vm v ∈ V(P i) ∩ V(η₁.imageGraph) := ⟨hvm_Pi, hvm_in⟩
        rw [(hP i).2.2.2.2.2.1] at hvm_inter
        rcases hvm_inter with h_u | h_v
        · have hv_u : v = u' i :=
            (η_P i).bijOn_v.injOn hvi (hu'_P'V i) (by rw [← hvm_P' i v hvi, h_u, hη_P_u i])
          exact hv₁ (hv_u ▸ hu' i)
        · rw [mem_singleton_iff] at h_v
          have hv_v : v = v' i :=
            (η_P i).bijOn_v.injOn hvi (hv'_P'V i) (by rw [← hvm_P' i v hvi, h_v, hη_P_v i])
          exact hv₁ (hv_v ▸ hv' i)
      exact ⟨fun ⟨w, hlink⟩ => (hvm_not_V₁ hlink.left_mem).elim, fun h => (hv_not_cl h).elim⟩
  · obtain ⟨i, hei⟩ := mem_iUnion.mp heP
    have hem_in : em e ∈ E(P i) := hem_P' i e hei ▸ hη_P_im i ▸ (η_P i).bijOn_e.mapsTo hei
    have hem_not_H₁ : em e ∉ E(η₁.imageGraph) :=
      Set.disjoint_left.mp (hP i).2.2.2.2.2.2 hem_in
    have hInc_eq : ImG.Inc (em e) (vm v) ↔ (P i).Inc ((η_P i).eMap e) (vm v) := by
      rw [hem_P' i e hei]
      constructor
      · rintro ⟨w, hlink⟩
        rw [subgraphUnion_isLink η₁.imageGraph_le hSUnion_le] at hlink
        rcases hlink with hlink₁ | hlink₂
        · exact (hem_not_H₁ (hem_P' i e hei ▸ hlink₁.edge_mem)).elim
        · have hlink_G : G.IsLink ((η_P i).eMap e) (vm v) w :=
            (hSUnion_le.isLink_iff hlink₂.edge_mem).mp hlink₂
          have he_Pi : (η_P i).eMap e ∈ E(P i) := hem_P' i e hei ▸ hem_in
          exact ⟨w, ((hP i).2.1.1.isLink_iff he_Pi).mpr hlink_G⟩
      · rintro ⟨w, hlink_i⟩
        have hlink_Su : (subgraphSUnion G (range P)).IsLink ((η_P i).eMap e) (vm v) w :=
          (le_subgraphSUnion hP_le ⟨i, rfl⟩).isLink_mono hlink_i
        exact ⟨w, (subgraphUnion_isLink η₁.imageGraph_le hSUnion_le).mpr (Or.inr hlink_Su)⟩
    rw [hInc_eq]
    by_cases hvi : v ∈ (P' i).V
    · rw [hvm_P' i v hvi, ← hη_P_im i, (η_P i).inc_iff e hei v hvi]
    · have hv_not_Li : v ∉ L i := by
        intro hvL
        rw [hH'_V] at hv
        rcases hv with hv₁ | hvP
        · have hv_pair : v ∈ ({u' i, v' i} : Set S') :=
            hL_inter i ▸ ⟨hvL, H₁.V_subset_U hv₁⟩
          rcases hv_pair with rfl | rfl
          · exact hvi (hu'_P'V i)
          · exact hvi (hv'_P'V i)
        · obtain ⟨j, hvj⟩ := mem_iUnion.mp hvP
          by_cases hij : i = j
          · exact hvi (hij ▸ hvj)
          · exact Set.disjoint_left.mp (hL_disj hij) hvL (hP'_U j ▸ (P' j).V_subset_U hvj)
      have hv_not_cl : v ∉ closure e := by
        intro hv_cl
        have he_sub : e ⊆ L i := hP'_U i ▸ fun x hx => (hei.2.1 hx).1
        have hLi_closed : IsClosed (L i) := (isCompact_of_isLineWithEnds' (hL i)).isClosed
        exact hv_not_Li (hLi_closed.closure_subset_iff.mpr he_sub hv_cl)
      have hvm_not_Pi : vm v ∉ V(P i) := by
        intro hvm_in
        rw [hH'_V] at hv
        rcases hv with hv₁ | hvP
        · have hvm_inter : vm v ∈ V(P i) ∩ V(η₁.imageGraph) :=
            ⟨hvm_in, hvm_H₁ v hv₁ ▸ η₁.bijOn_v.mapsTo hv₁⟩
          rw [(hP i).2.2.2.2.2.1] at hvm_inter
          rcases hvm_inter with h_u | h_v
          · have hv_u : v = u' i :=
              η₁.bijOn_v.injOn hv₁ (hu' i) (by rw [← hvm_H₁ v hv₁, h_u])
            exact hvi (hv_u ▸ hu'_P'V i)
          · rw [mem_singleton_iff] at h_v
            have hv_v : v = v' i :=
              η₁.bijOn_v.injOn hv₁ (hv' i) (by rw [← hvm_H₁ v hv₁, h_v])
            exact hvi (hv_v ▸ hv'_P'V i)
        · obtain ⟨j, hvj⟩ := mem_iUnion.mp hvP
          by_cases hij : i = j
          · exact hvi (hij ▸ hvj)
          · have hvm_Pj : vm v ∈ V(P j) :=
              hvm_P' j v hvj ▸ hη_P_im j ▸ (η_P j).bijOn_v.mapsTo hvj
            exact Set.disjoint_left.mp (hP_disj hij) hvm_in hvm_Pj
      exact ⟨fun ⟨w, hlink⟩ => (hvm_not_Pi hlink.left_mem).elim, fun h => (hv_not_cl h).elim⟩

/-- Given a base drawing `H₁ : Drawing S'` with `η₁ : SpanEmbedding H₁ G`, and `m` pairwise
vertex-disjoint `η₁(H₁)`-paths `P : Fin m → Graph α β` with ends `η₁.vMap (u' i), η₁.vMap (v' i)`
along `m` pairwise disjoint lines `L : Fin m → Set S'` with `L i ∩ H₁.U = {u' i, v' i}`,
there exist path drawings `P' : Fin m → Drawing S'`, a glued drawing `H' : Drawing S'`, and a
glued `SpanEmbedding H' G` (`η'`). -/
theorem exists_glued_span_of_lines {G : Graph α β}
    (H₁ : Drawing S') (η₁ : SpanEmbedding H₁ G)
    {m : ℕ} (u' v' : Fin m → S') (P : Fin m → Graph α β) (L : Fin m → Set S')
    (hu' : ∀ i, u' i ∈ H₁.V) (hv' : ∀ i, v' i ∈ H₁.V)
    (hP : ∀ i, IsHPathWithEnds G η₁.imageGraph (P i) (η₁.vMap (u' i)) (η₁.vMap (v' i)))
    (hP_disj : Pairwise (fun i j => Disjoint V(P i) V(P j)))
    (hL : ∀ i, IsLineWithEnds (L i) (u' i) (v' i))
    (hL_disj : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hL_inter : ∀ i, L i ∩ H₁.U = {u' i, v' i}) :
    ∃ (P' : Fin m → Drawing S') (H' : Drawing S') (η' : SpanEmbedding H' G),
      H'.U = H₁.U ∪ ⋃ i : Fin m, L i ∧
      H'.V = H₁.V ∪ ⋃ i : Fin m, (P' i).V ∧
      H'.E = H₁.E ∪ ⋃ i : Fin m, (P' i).E ∧
      H₁.IsSubdrawing H' ∧
      (∀ i, (P' i).U = L i ∧ (P' i).IsPathBetween (u' i) (v' i) ∧ (P' i).IsSubdrawing H' ∧
        u' i ∈ (P' i).V ∧ v' i ∈ (P' i).V) ∧
      Pairwise (fun i j => Disjoint (P' i).U (P' j).U) ∧
      η'.imageGraph = subgraphUnion G η₁.imageGraph (subgraphSUnion G (range P)) ∧
      (∀ x ∈ H₁.V, η'.vMap x = η₁.vMap x) ∧
      (∀ e ∈ H₁.E, η'.eMap e = η₁.eMap e) ∧
      (∀ i, ∀ e ∈ (P' i).E, η'.eMap e ∈ E(P i)) ∧
      (∀ i, ∀ b ∈ E(P i), ∃ e ∈ (P' i).E, η'.eMap e = b) := by
  classical
  have huv_ne : ∀ i, u' i ≠ v' i := fun i h => (hP i).2.2.1 (congrArg η₁.vMap h)
  have hex_P : ∀ i : Fin m, ∃ (D_i : Drawing S') (η_i : SpanEmbedding D_i G),
      D_i.U = L i ∧
      D_i.IsPathBetween (u' i) (v' i) ∧
      u' i ∈ D_i.V ∧ v' i ∈ D_i.V ∧
      η_i.imageGraph = P i ∧
      η_i.vMap (u' i) = η₁.vMap (u' i) ∧
      η_i.vMap (v' i) = η₁.vMap (v' i) := by
    exact paths_on_gluing_arcs_have_drawings (α := α) (β := β) (S' := S') (G := G) H₁ η₁ (m := m)
      u' v' P L hP hL huv_ne
  choose P' η_P hP'_U hP'_path hu'_P'V hv'_P'V hη_P_im hη_P_u hη_P_v using hex_P
  let D_fam : Option (Fin m) → Drawing S' := Option.elim' H₁ P'
  have hZMeet : ∀ o ∈ (univ : Set (Option (Fin m))), (D_fam o).U ∩ H₁.V ⊆ (D_fam o).V := by
    rintro (_ | i) _ x ⟨hxU, hxV⟩
    · exact hxV
    · change x ∈ (P' i).U at hxU
      rw [hP'_U i] at hxU
      have hx_pair : x ∈ ({u' i, v' i} : Set S') := hL_inter i ▸ ⟨hxU, H₁.V_subset_U hxV⟩
      rcases hx_pair with rfl | rfl
      · exact hu'_P'V i
      · exact hv'_P'V i
  have hMeet : ∀ o₁ ∈ (univ : Set (Option (Fin m))), ∀ o₂ ∈ (univ : Set (Option (Fin m))),
      o₁ ≠ o₂ → (D_fam o₁).U ∩ (D_fam o₂).U ⊆ H₁.V := by
    exact initial_drawing_and_gluing_paths_only_meet_at_vertices (S' := S') H₁ (m := m) u' v' L
      hu' hv' hL_disj hL_inter P' hP'_U
  obtain ⟨H', hH'_U₀, hH'_V₀, hH'_E₀⟩ :=
    GM16.exists_drawing_of_finite_drawings (Set.toFinite univ) H₁.finite_V D_fam hZMeet hMeet
  have hH'_U : H'.U = H₁.U ∪ ⋃ i : Fin m, L i := by
    rw [hH'_U₀]
    ext x
    constructor
    · rintro (hxV | hxU)
      · exact Or.inl (H₁.V_subset_U hxV)
      · obtain ⟨o, -, hxo⟩ := mem_iUnion₂.mp hxU
        rcases o with _ | i
        · exact Or.inl hxo
        · exact Or.inr (mem_iUnion.mpr ⟨i, hP'_U i ▸ hxo⟩)
    · rintro (hxU | hxL)
      · exact Or.inr (mem_iUnion₂.mpr ⟨none, mem_univ _, hxU⟩)
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxL
        exact Or.inr (mem_iUnion₂.mpr ⟨some i, mem_univ _, (hP'_U i).symm ▸ hxi⟩)
  have hH'_V : H'.V = H₁.V ∪ ⋃ i : Fin m, (P' i).V := by
    rw [hH'_V₀]
    ext x
    constructor
    · rintro (hxV | hxU)
      · exact Or.inl hxV
      · obtain ⟨o, -, hxo⟩ := mem_iUnion₂.mp hxU
        rcases o with _ | i
        · exact Or.inl hxo
        · exact Or.inr (mem_iUnion.mpr ⟨i, hxo⟩)
    · rintro (hxV | hxP)
      · exact Or.inl hxV
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxP
        exact Or.inr (mem_iUnion₂.mpr ⟨some i, mem_univ _, hxi⟩)
  have hH'_E : H'.E = H₁.E ∪ ⋃ i : Fin m, (P' i).E := by
    rw [hH'_E₀]
    ext e
    constructor
    · intro heU
      obtain ⟨o, -, heo⟩ := mem_iUnion₂.mp heU
      rcases o with _ | i
      · exact Or.inl heo
      · exact Or.inr (mem_iUnion.mpr ⟨i, heo⟩)
    · rintro (he₁ | heP)
      · exact mem_iUnion₂.mpr ⟨none, mem_univ _, he₁⟩
      · obtain ⟨i, hei⟩ := mem_iUnion.mp heP
        exact mem_iUnion₂.mpr ⟨some i, mem_univ _, hei⟩
  have hSub_H₁ : H₁.IsSubdrawing H' :=
    ⟨by rw [hH'_V]; exact subset_union_left, by rw [hH'_E]; exact subset_union_left⟩
  have hSub_P' : ∀ i, (P' i).IsSubdrawing H' := fun i =>
    ⟨by rw [hH'_V]; exact (subset_iUnion (fun j => (P' j).V) i).trans subset_union_right,
     by rw [hH'_E]; exact (subset_iUnion (fun j => (P' j).E) i).trans subset_union_right⟩
  have hP'_disj : Pairwise (fun i j => Disjoint (P' i).U (P' j).U) := by
    intro i j hij
    rw [hP'_U i, hP'_U j]
    exact hL_disj hij
  have hP'V_inter_H₁U : ∀ i, (P' i).V ∩ H₁.U = {u' i, v' i} := by
    intro i
    refine Subset.antisymm ?_ ?_
    · intro x ⟨hxV, hxU⟩
      have hxL : x ∈ L i := hP'_U i ▸ (P' i).V_subset_U hxV
      exact hL_inter i ▸ ⟨hxL, hxU⟩
    · rintro x (rfl | rfl)
      · exact ⟨hu'_P'V i, H₁.V_subset_U (hu' i)⟩
      · exact ⟨hv'_P'V i, H₁.V_subset_U (hv' i)⟩
  have hP'E_disj_H₁U : ∀ i, ∀ e ∈ (P' i).E, Disjoint e H₁.U := by
    intro i e he
    refine Set.disjoint_left.mpr fun x hxe hxU => ?_
    have hx_diff : x ∈ (P' i).U \ (P' i).V := he.2.1 hxe
    have hx_pair : x ∈ ({u' i, v' i} : Set S') := hL_inter i ▸ ⟨hP'_U i ▸ hx_diff.1, hxU⟩
    rcases hx_pair with rfl | rfl
    · exact hx_diff.2 (hu'_P'V i)
    · exact hx_diff.2 (hv'_P'V i)
  have hP'E_disj_H₁E : ∀ i, Disjoint (P' i).E H₁.E := by
    intro i
    refine Set.disjoint_left.mpr fun e heP he₁ => ?_
    obtain ⟨x, hxe⟩ := heP.1
    exact Set.disjoint_left.mp (hP'E_disj_H₁U i e heP) hxe (he₁.2.1 hxe).1
  have hP'E_disj : Pairwise (fun i j => Disjoint (P' i).E (P' j).E) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun e hei hej => ?_
    obtain ⟨x, hxe⟩ := hei.1
    exact Set.disjoint_left.mp (hP'_disj hij) (hei.2.1 hxe).1 (hej.2.1 hxe).1
  let vm : S' → α := fun x =>
    if x ∈ H₁.V then η₁.vMap x
    else if h : ∃ i : Fin m, x ∈ (P' i).V then (η_P (Classical.choose h)).vMap x
    else η₁.vMap x
  let em : Set S' → β := fun e =>
    if e ∈ H₁.E then η₁.eMap e
    else if h : ∃ i : Fin m, e ∈ (P' i).E then (η_P (Classical.choose h)).eMap e
    else η₁.eMap e
  have hvm_H₁ : ∀ x ∈ H₁.V, vm x = η₁.vMap x := fun x hx => ite_eq_left hx
  have hvm_P' : ∀ i, ∀ x ∈ (P' i).V, vm x = (η_P i).vMap x := by
    intro i x hx
    by_cases hx₁ : x ∈ H₁.V
    · rw [hvm_H₁ x hx₁]
      have hx_pair : x ∈ ({u' i, v' i} : Set S') :=
        hP'V_inter_H₁U i ▸ ⟨hx, H₁.V_subset_U hx₁⟩
      rcases hx_pair with rfl | rfl
      · exact (hη_P_u i).symm
      · exact (hη_P_v i).symm
    · have hex : ∃ j : Fin m, x ∈ (P' j).V := ⟨i, hx⟩
      have h_eq : vm x = (η_P (Classical.choose hex)).vMap x := by
        dsimp [vm]
        rw [ite_eq_right hx₁, dite_eq_left hex]
      rw [h_eq]
      have h_choose : Classical.choose hex = i := by
        by_contra hne
        exact Set.disjoint_left.mp (hP'_disj hne)
          ((P' (Classical.choose hex)).V_subset_U (Classical.choose_spec hex))
          ((P' i).V_subset_U hx)
      rw [h_choose]
  have hem_H₁ : ∀ e ∈ H₁.E, em e = η₁.eMap e := fun e he => ite_eq_left he
  have hem_P' : ∀ i, ∀ e ∈ (P' i).E, em e = (η_P i).eMap e := by
    intro i e he
    have he₁ : e ∉ H₁.E := Set.disjoint_left.mp (hP'E_disj_H₁E i) he
    have hex : ∃ j : Fin m, e ∈ (P' j).E := ⟨i, he⟩
    have h_eq : em e = (η_P (Classical.choose hex)).eMap e := by
      dsimp [em]
      rw [ite_eq_right he₁, dite_eq_left hex]
    rw [h_eq]
    have h_choose : Classical.choose hex = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hP'E_disj hne) (Classical.choose_spec hex) he
    rw [h_choose]
  let ImG := subgraphUnion G η₁.imageGraph (subgraphSUnion G (range P))
  have hP_le : ∀ M ∈ range P, M ≤ G := by
    rintro _ ⟨i, rfl⟩
    exact (hP i).2.1.1
  have hSUnion_le : subgraphSUnion G (range P) ≤ G := subgraphSUnion_le hP_le
  have hImG_le : ImG ≤ G := subgraphUnion_le η₁.imageGraph_le hSUnion_le
  have hV_ImG : V(ImG) = V(η₁.imageGraph) ∪ ⋃ i : Fin m, V(P i) := by
    change V(η₁.imageGraph) ∪ V(subgraphSUnion G (range P)) = _
    rw [vertexSet_subgraphSUnion]
    ext a
    simp
  have hE_ImG : E(ImG) = E(η₁.imageGraph) ∪ ⋃ i : Fin m, E(P i) := by
    change E(subgraphUnion G η₁.imageGraph (subgraphSUnion G (range P))) = _
    rw [edgeSet_subgraphUnion η₁.imageGraph_le hSUnion_le, edgeSet_subgraphSUnion hP_le]
    ext b
    simp
  have hBij_v : BijOn vm H'.V V(ImG) := by
    exact glued_drawing_vertex_map_bijective (α := α) (β := β) (S' := S') (G := G) H₁ η₁ (m := m)
      u' v' P hu' hv' hP hP_disj P' η_P hu'_P'V hv'_P'V hη_P_im hη_P_u hη_P_v H' hH'_V hSub_H₁
      hSub_P' vm hvm_H₁ hvm_P' hV_ImG
  have hPE_disj : Pairwise (fun i j => Disjoint E(P i) E(P j)) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun b hbi hbj => ?_
    obtain ⟨x, y, hlink⟩ := (P i).exists_isLink_of_mem_edgeSet hbi
    have hx_i : x ∈ V(P i) := hlink.left_mem
    have hlink_G : G.IsLink b x y := ((hP i).2.1.1.isLink_iff hbi).mp hlink
    have hlink_j : (P j).IsLink b x y := ((hP j).2.1.1.isLink_iff hbj).mpr hlink_G
    exact Set.disjoint_left.mp (hP_disj hij) hx_i hlink_j.left_mem
  have hBij_e : BijOn em H'.E E(ImG) := by
    exact glued_drawing_edge_map_bijective (α := α) (β := β) (S' := S') (G := G) H₁ η₁ (m := m) u'
      v' P hP P' η_P hη_P_im H' hH'_E hSub_H₁ hSub_P' em hem_H₁ hem_P' hE_ImG hPE_disj
  have hInc_iff : ∀ e ∈ H'.E, ∀ v ∈ H'.V, ImG.Inc (em e) (vm v) ↔ v ∈ closure e := by
    exact glued_drawing_incidence_iff_closure (α := α) (β := β) (S' := S') (G := G) H₁ η₁ (m := m)
      u' v' P L hu' hv' hP hP_disj hL hL_disj hL_inter P' η_P hP'_U hu'_P'V hv'_P'V hη_P_im hη_P_u
      hη_P_v H' hH'_V hH'_E hP'V_inter_H₁U vm em hvm_H₁ hvm_P' hem_H₁ hem_P' hP_le hSUnion_le
  let η' : SpanEmbedding H' G := ⟨ImG, vm, em, hImG_le, hBij_v, hBij_e, hInc_iff⟩
  refine ⟨P', H', η', hH'_U, hH'_V, hH'_E, hSub_H₁,
    fun i => ⟨hP'_U i, hP'_path i, hSub_P' i, hu'_P'V i, hv'_P'V i⟩,
    hP'_disj, rfl, hvm_H₁, hem_H₁, ?_, ?_⟩
  · intro i e he
    change em e ∈ E(P i)
    rw [hem_P' i e he, ← hη_P_im i]
    exact (η_P i).bijOn_e.mapsTo he
  · intro i b hb
    obtain ⟨e, he, rfl⟩ := (η_P i).bijOn_e.surjOn (hη_P_im i ▸ hb)
    exact ⟨e, he, hem_P' i e he⟩

/-- If `K ⊆ S'` is closed, `H₁.U ⊆ K`, and `L i ∩ K = {u' i, v' i}` for all `i`, then for the
glued drawing `H'`, `H'.U ∩ K = H₁.U`, `H'.V ∩ K = H₁.V`, and `H'.interSet K = H₁`. -/
theorem glued_interSet_base_eq
    {H₁ H' : Drawing S'} {m : ℕ} {u' v' : Fin m → S'} {L : Fin m → Set S'}
    {P' : Fin m → Drawing S'} {K : Set S'}
    (hK : IsClosed K)
    (hu' : ∀ i, u' i ∈ H₁.V) (hv' : ∀ i, v' i ∈ H₁.V)
    (hH₁_sub : H₁.U ⊆ K)
    (hL_K : ∀ i, L i ∩ K = {u' i, v' i})
    (hH'_U : H'.U = H₁.U ∪ ⋃ i : Fin m, L i)
    (hH'_V : H'.V = H₁.V ∪ ⋃ i : Fin m, (P' i).V)
    (hH'_E : H'.E = H₁.E ∪ ⋃ i : Fin m, (P' i).E)
    (hP' : ∀ i, (P' i).U = L i ∧ (P' i).IsPathBetween (u' i) (v' i) ∧ (P' i).IsSubdrawing H' ∧
      u' i ∈ (P' i).V ∧ v' i ∈ (P' i).V) :
    H'.U ∩ K = H₁.U ∧ H'.V ∩ K = H₁.V ∧ H'.interSet K = H₁ := by
  have hUK : H'.U ∩ K = H₁.U := by
    rw [hH'_U, union_inter_distrib_right, inter_eq_left.mpr hH₁_sub]
    refine union_eq_self_of_subset_right ?_
    rintro x ⟨hxL, hxK⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxL
    have hx_pair : x ∈ ({u' i, v' i} : Set S') := hL_K i ▸ ⟨hxi, hxK⟩
    rcases hx_pair with rfl | rfl
    · exact H₁.V_subset_U (hu' i)
    · exact H₁.V_subset_U (hv' i)
  have hVK : H'.V ∩ K = H₁.V := by
    rw [hH'_V, union_inter_distrib_right, inter_eq_left.mpr (H₁.V_subset_U.trans hH₁_sub)]
    refine union_eq_self_of_subset_right ?_
    rintro x ⟨hxP, hxK⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxP
    have hxL : x ∈ L i := (hP' i).1 ▸ (P' i).V_subset_U hxi
    have hx_pair : x ∈ ({u' i, v' i} : Set S') := hL_K i ▸ ⟨hxL, hxK⟩
    rcases hx_pair with rfl | rfl
    · exact hu' i
    · exact hv' i
  refine ⟨hUK, hVK, ?_⟩
  apply Drawing.ext_of_V_E
  · rw [interSet_V_of_isClosed H' hK, hVK]
  · rw [interSet_E H' K, hH'_E]
    ext e
    constructor
    · rintro ⟨he₁ | heP, heK⟩
      · exact he₁
      · obtain ⟨i, hei⟩ := mem_iUnion.mp heP
        obtain ⟨x, hxe⟩ := hei.1
        have hx_diff : x ∈ (P' i).U \ (P' i).V := hei.2.1 hxe
        have hx_pair : x ∈ ({u' i, v' i} : Set S') :=
          hL_K i ▸ ⟨(hP' i).1 ▸ hx_diff.1, heK hxe⟩
        rcases hx_pair with rfl | rfl
        · exact (hx_diff.2 (hP' i).2.2.2.1).elim
        · exact (hx_diff.2 (hP' i).2.2.2.2).elim
    · intro he₁
      exact ⟨Or.inl he₁, fun x hx => hH₁_sub (he₁.2.1 hx).1⟩

/-- If `P₂ ⊆ S'` is closed, `L i ⊆ P₂` for all `i`, and `H₁.U ∩ P₂ ⊆ ⋃ i, {u' i, v' i}`, then
each `P' i` is a subdrawing of `H'.interSet P₂` and `(H'.interSet P₂).U = ⋃ i, (P' i).U`. -/
theorem glued_interSet_paths_eq
    {H₁ H' : Drawing S'} {m : ℕ} {u' v' : Fin m → S'} {L : Fin m → Set S'}
    {P' : Fin m → Drawing S'} {P₂ : Set S'}
    (hP₂ : IsClosed P₂)
    (hL_P₂ : ∀ i, L i ⊆ P₂)
    (hH₁_P₂ : H₁.U ∩ P₂ ⊆ ⋃ i : Fin m, ({u' i, v' i} : Set S'))
    (hH'_V : H'.V = H₁.V ∪ ⋃ i : Fin m, (P' i).V)
    (hH'_E : H'.E = H₁.E ∪ ⋃ i : Fin m, (P' i).E)
    (hP' : ∀ i, (P' i).U = L i ∧ (P' i).IsPathBetween (u' i) (v' i) ∧ (P' i).IsSubdrawing H' ∧
      u' i ∈ (P' i).V ∧ v' i ∈ (P' i).V) :
    (∀ i, (P' i).IsSubdrawing (H'.interSet P₂)) ∧
    (H'.interSet P₂).U = ⋃ i : Fin m, (P' i).U := by
  have hSub_i : ∀ i, (P' i).IsSubdrawing (H'.interSet P₂) := by
    intro i
    refine ⟨?_, ?_⟩
    · rw [interSet_V_of_isClosed H' hP₂]
      intro x hx
      exact ⟨(hP' i).2.2.1.1 hx, hL_P₂ i ((hP' i).1 ▸ (P' i).V_subset_U hx)⟩
    · rw [interSet_E H' P₂]
      intro e he
      exact ⟨(hP' i).2.2.1.2 he, fun x hx => hL_P₂ i ((hP' i).1 ▸ (he.2.1 hx).1)⟩
  refine ⟨hSub_i, ?_⟩
  have hV_eq : (H'.interSet P₂).V = ⋃ i : Fin m, (P' i).V := by
    rw [interSet_V_of_isClosed H' hP₂, hH'_V, union_inter_distrib_right]
    refine Subset.antisymm (union_subset ?_ ?_) ?_
    · intro x ⟨hx₁, hxP₂⟩
      obtain ⟨i, hxi⟩ := mem_iUnion.mp (hH₁_P₂ ⟨H₁.V_subset_U hx₁, hxP₂⟩)
      rcases hxi with rfl | rfl
      · exact mem_iUnion.mpr ⟨i, (hP' i).2.2.2.1⟩
      · exact mem_iUnion.mpr ⟨i, (hP' i).2.2.2.2⟩
    · rintro x ⟨hxP, _⟩
      exact hxP
    · intro x hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      exact Or.inr ⟨hx, hL_P₂ i ((hP' i).1 ▸ (P' i).V_subset_U hxi)⟩
  have hE_eq : (H'.interSet P₂).E = ⋃ i : Fin m, (P' i).E := by
    rw [interSet_E H' P₂, hH'_E]
    ext e
    constructor
    · rintro ⟨he₁ | heP, heP₂⟩
      · obtain ⟨x, hxe⟩ := he₁.1
        have hx_diff : x ∈ H₁.U \ H₁.V := he₁.2.1 hxe
        obtain ⟨i, hxi⟩ := mem_iUnion.mp (hH₁_P₂ ⟨hx_diff.1, heP₂ hxe⟩)
        exfalso
        have hx_P'V : x ∈ (P' i).V := by
          rcases hxi with rfl | rfl
          · exact (hP' i).2.2.2.1
          · exact (hP' i).2.2.2.2
        have hx_H'V : x ∈ H'.V := (hP' i).2.2.1.1 hx_P'V
        have he_H'E : e ∈ H'.E := by rw [hH'_E]; exact Or.inl he₁
        exact (he_H'E.2.1 hxe).2 hx_H'V
      · exact heP
    · intro heP
      obtain ⟨i, hei⟩ := mem_iUnion.mp heP
      exact ⟨Or.inr heP, fun x hx => hL_P₂ i ((hP' i).1 ▸ (hei.2.1 hx).1)⟩
  rw [(H'.interSet P₂).U_eq, hV_eq, hE_eq]
  ext x
  constructor
  · rintro (hxV | hxE)
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxV
      exact mem_iUnion.mpr ⟨i, (P' i).V_subset_U hxi⟩
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxE
      obtain ⟨i, hei⟩ := mem_iUnion.mp he
      have hcl_sub : closure e ⊆ (P' i).U :=
        (P' i).isClosed_U.closure_subset_iff.mpr fun y hy => (hei.2.1 hy).1
      exact mem_iUnion.mpr ⟨i, hcl_sub hxe⟩
  · intro hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    rw [(P' i).U_eq] at hxi
    rcases hxi with hxV | hxE
    · exact Or.inl (mem_iUnion.mpr ⟨i, hxV⟩)
    · obtain ⟨e, hei, hxe⟩ := mem_iUnion₂.mp hxE
      exact Or.inr (mem_iUnion₂.mpr ⟨e, mem_iUnion.mpr ⟨i, hei⟩, hxe⟩)

omit [T2Space S'] in
/-- If a curve `C_j ⊆ S'` meets `H₁.U` in `X_C ⊆ H₁.V` and meets `⋃ i, L i` in `X_C`, then
`H'.IsNormal C_j` and `H'.V ∩ C_j = X_C`. -/
theorem glued_isNormal_and_V_inter
    {H₁ H' : Drawing S'} {m : ℕ} {L : Fin m → Set S'} {P' : Fin m → Drawing S'}
    {C_j X_C : Set S'}
    (hX_sub : X_C ⊆ H₁.V)
    (hH₁_C : H₁.U ∩ C_j = X_C)
    (hL_C : (⋃ i : Fin m, L i) ∩ C_j ⊆ X_C)
    (hH'_U : H'.U = H₁.U ∪ ⋃ i : Fin m, L i)
    (hH'_V : H'.V = H₁.V ∪ ⋃ i : Fin m, (P' i).V) :
    H'.IsNormal C_j ∧ H'.V ∩ C_j = X_C := by
  have hUC : H'.U ∩ C_j = X_C := by
    rw [hH'_U, union_inter_distrib_right, hH₁_C]
    exact union_eq_self_of_subset_right hL_C
  have hX_H'V : X_C ⊆ H'.V := by
    rw [hH'_V]
    exact hX_sub.trans subset_union_left
  refine ⟨?_, ?_⟩
  · intro x ⟨hxC, hxU⟩
    have hxX : x ∈ X_C := hUC ▸ ⟨hxU, hxC⟩
    exact hX_H'V hxX
  · refine Subset.antisymm ?_ ?_
    · intro x ⟨hxV, hxC⟩
      exact hUC ▸ ⟨H'.V_subset_U hxV, hxC⟩
    · intro x hxX
      have hxC : x ∈ C_j := (hUC ▸ hxX).2
      exact ⟨hX_H'V hxX, hxC⟩

end GluePaths

/-! ## 3. `IsCappedDrawing`, `IsTangle`, and `IsControllingTangle` Across a Cut -/

section InducedAcrossControl

variable {α : Type u} {β : Type v}
  {S' S_hat : Type w} [TopologicalSpace S'] [T2Space S']
  [TopologicalSpace S_hat] [T2Space S_hat]

omit [T2Space S_hat] in
/-- When `H₁ = liftDrawingOn hK hg hf hl H hHU` and `H'.U ∩ P₁ = H₁.U`, `H'.V ∩ P₁ = H₁.V`,
and `ι ⟨g y, hy⟩ = y` for all `y ∈ K` with `g y ∈ P₁`, `GM12.IsCappedDrawing ι H' H` holds. -/
theorem isCappedDrawing_of_glued
    {P₁ : Set S'} {ι : P₁ → S_hat}
    {K : Set S_hat} (hK : IsCompact K)
    {g : S_hat → S'} {f : S' → S_hat}
    (hg : ContinuousOn g K) (hf : ContinuousOn f (g '' K)) (hl : LeftInvOn f g K)
    {H : Drawing S_hat} (hHU : H.U ⊆ K)
    {H' : Drawing S'}
    (hU_P₁ : H'.U ∩ P₁ = (liftDrawingOn hK hg hf hl H hHU).U)
    (hV_P₁ : H'.V ∩ P₁ = (liftDrawingOn hK hg hf hl H hHU).V)
    (hι_g : ∀ y ∈ K, ∀ hy : g y ∈ P₁, ι ⟨g y, hy⟩ = y) :
    GM12.IsCappedDrawing ι H' H := by
  constructor
  · ext y
    constructor
    · intro hyU
      have hy_gP₁ : g y ∈ H'.U ∩ P₁ := by
        rw [hU_P₁]
        exact ⟨y, hyU, rfl⟩
      exact ⟨⟨g y, hy_gP₁.2⟩, hy_gP₁.1, hι_g y (hHU hyU) hy_gP₁.2⟩
    · rintro ⟨⟨x, hxP₁⟩, hxU, rfl⟩
      have hx_g : x ∈ g '' H.U := by
        have : x ∈ H'.U ∩ P₁ := ⟨hxU, hxP₁⟩
        rwa [hU_P₁] at this
      obtain ⟨y, hyU, rfl⟩ := hx_g
      rw [hι_g y (hHU hyU) hxP₁]
      exact hyU
  · ext y
    constructor
    · intro hyV
      have hy_gP₁ : g y ∈ H'.V ∩ P₁ := by
        rw [hV_P₁]
        exact ⟨y, hyV, rfl⟩
      exact ⟨⟨g y, hy_gP₁.2⟩, hy_gP₁.1, hι_g y (H.V_subset_U.trans hHU hyV) hy_gP₁.2⟩
    · rintro ⟨⟨x, hxP₁⟩, hxV, rfl⟩
      have hx_g : x ∈ g '' H.V := by
        have : x ∈ H'.V ∩ P₁ := ⟨hxV, hxP₁⟩
        rwa [hV_P₁] at this
      obtain ⟨y, hyV, rfl⟩ := hx_g
      rw [hι_g y (H.V_subset_U.trans hHU hyV) hxP₁]
      exact hyV

/-- Pushforward of a subhypergraph `A' ≤ H'.toHypergraph` to `H.toHypergraph` along `g : S_hat →
S'`. -/
def pushHypergraphOn {K : Set S_hat} (hK : IsCompact K)
    {g : S_hat → S'} {f : S' → S_hat}
    (hg : ContinuousOn g K) (hf : ContinuousOn f (g '' K)) (hl : LeftInvOn f g K)
    {H : Drawing S_hat} (hHU : H.U ⊆ K)
    {H' : Drawing S'}
    (hSub : (liftDrawingOn hK hg hf hl H hHU).IsSubdrawing H')
    (A' : Hypergraph S' (Set S')) (hA' : A' ≤ H'.toHypergraph) :
    Hypergraph S_hat (Set S_hat) where
  vertexSet := {v ∈ H.V | g v ∈ A'.vertexSet}
  edgeSet := {e ∈ H.E | g '' e ∈ A'.edgeSet}
  Inc e v := H.toHypergraph.Inc e v ∧ e ∈ H.E ∧ g '' e ∈ A'.edgeSet
  vertex_mem_of_inc e v h := by
    refine ⟨h.1.2.1, ?_⟩
    have he'_H₁ : g '' e ∈ (liftDrawingOn hK hg hf hl H hHU).E := by
      rw [liftDrawingOn_E hK hg hf hl H hHU]
      exact ⟨e, h.2.1, rfl⟩
    have he'_H' : g '' e ∈ H'.E := hSub.2 he'_H₁
    have hv'_H' : g v ∈ H'.V := hSub.1 ⟨v, h.1.2.1, rfl⟩
    have hv'_cl : g v ∈ closure (g '' e) := by
      rw [liftDrawingOn_closure_edge hK hg hf hl hHU h.2.1]
      exact ⟨v, h.1.2.2, rfl⟩
    have hinc' : H'.toHypergraph.Inc (g '' e) (g v) := ⟨he'_H', hv'_H', hv'_cl⟩
    have hv'_ends : g v ∈ A'.ends (g '' e) := by
      rw [← hA'.ends_eq (g '' e) h.2.2]
      exact hinc'
    exact A'.vertex_mem_of_inc hv'_ends
  edge_mem_of_inc _ _ h := h.2
  vertexSet_finite := H.finite_V.subset fun _ h => h.1
  edgeSet_finite := H.finite_edges.subset fun _ h => h.1

omit [T2Space S_hat] in
theorem pushHypergraphOn_le {K : Set S_hat} (hK : IsCompact K)
    {g : S_hat → S'} {f : S' → S_hat}
    (hg : ContinuousOn g K) (hf : ContinuousOn f (g '' K)) (hl : LeftInvOn f g K)
    {H : Drawing S_hat} (hHU : H.U ⊆ K)
    {H' : Drawing S'}
    (hSub : (liftDrawingOn hK hg hf hl H hHU).IsSubdrawing H')
    (A' : Hypergraph S' (Set S')) (hA' : A' ≤ H'.toHypergraph) :
    pushHypergraphOn hK hg hf hl hHU hSub A' hA' ≤ H.toHypergraph := by
  refine ⟨fun _ h => h.1, fun _ h => h.1, fun e he => ?_⟩
  ext v
  change H.toHypergraph.Inc e v ↔ H.toHypergraph.Inc e v ∧ e ∈ H.E ∧ g '' e ∈ A'.edgeSet
  exact ⟨fun h => ⟨h, he.1, he.2⟩, fun h => h.1⟩

omit [T2Space S_hat] in
theorem isSeparation_pushHypergraphOn {K : Set S_hat} (hK : IsCompact K)
    {g : S_hat → S'} {f : S' → S_hat}
    (hg : ContinuousOn g K) (hf : ContinuousOn f (g '' K)) (hl : LeftInvOn f g K)
    {H : Drawing S_hat} (hHU : H.U ⊆ K)
    {H' : Drawing S'}
    (hSub : (liftDrawingOn hK hg hf hl H hHU).IsSubdrawing H')
    {A' B' : Hypergraph S' (Set S')} (hsep : H'.toHypergraph.IsSeparation A' B') :
    H.toHypergraph.IsSeparation
      (pushHypergraphOn hK hg hf hl hHU hSub A' hsep.left_le)
      (pushHypergraphOn hK hg hf hl hHU hSub B' hsep.right_le) ∧
    separationOrder
      (pushHypergraphOn hK hg hf hl hHU hSub A' hsep.left_le)
      (pushHypergraphOn hK hg hf hl hHU hSub B' hsep.right_le) ≤ separationOrder A' B' := by
  have hAl := pushHypergraphOn_le hK hg hf hl hHU hSub A' hsep.left_le
  have hBl := pushHypergraphOn_le hK hg hf hl hHU hSub B' hsep.right_le
  refine ⟨(isSeparation_iff_of_le hAl hBl).mpr ⟨?_, ?_, ?_⟩, ?_⟩
  · ext v
    change (v ∈ H.V ∧ g v ∈ A'.vertexSet ∨ v ∈ H.V ∧ g v ∈ B'.vertexSet) ↔ v ∈ H.V
    constructor
    · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
    · intro hv
      have hgv : g v ∈ A'.vertexSet ∪ B'.vertexSet := by
        rw [hsep.vertexSet_union]
        exact hSub.1 ⟨v, hv, rfl⟩
      rcases hgv with hvA | hvB
      · exact Or.inl ⟨hv, hvA⟩
      · exact Or.inr ⟨hv, hvB⟩
  · ext e
    change (e ∈ H.E ∧ g '' e ∈ A'.edgeSet ∨ e ∈ H.E ∧ g '' e ∈ B'.edgeSet) ↔ e ∈ H.E
    constructor
    · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
    · intro he
      have hge : g '' e ∈ A'.edgeSet ∪ B'.edgeSet := by
        rw [hsep.edgeSet_union]
        refine hSub.2 ?_
        rw [liftDrawingOn_E hK hg hf hl H hHU]
        exact ⟨e, he, rfl⟩
      rcases hge with heA | heB
      · exact Or.inl ⟨he, heA⟩
      · exact Or.inr ⟨he, heB⟩
  · ext e
    change ((e ∈ H.E ∧ g '' e ∈ A'.edgeSet) ∧ (e ∈ H.E ∧ g '' e ∈ B'.edgeSet)) ↔
      e ∈ (∅ : Set (Set S_hat))
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, heA⟩, ⟨_, heB⟩⟩
    exact hsep.notMem_edgeSet_right heA heB
  · have hinj : InjOn g (pushHypergraphOn hK hg hf hl hHU hSub A' hsep.left_le ∩
        pushHypergraphOn hK hg hf hl hHU hSub B' hsep.right_le).vertexSet :=
      hl.injOn.mono fun v ⟨⟨hv, _⟩, _⟩ => H.V_subset_U.trans hHU hv
    have hsub_img : g '' (pushHypergraphOn hK hg hf hl hHU hSub A' hsep.left_le ∩
        pushHypergraphOn hK hg hf hl hHU hSub B' hsep.right_le).vertexSet ⊆
        (A' ∩ B').vertexSet := by
      rintro _ ⟨v, ⟨⟨_, hvA⟩, ⟨_, hvB⟩⟩, rfl⟩
      exact ⟨hvA, hvB⟩
    calc separationOrder (pushHypergraphOn hK hg hf hl hHU hSub A' hsep.left_le)
          (pushHypergraphOn hK hg hf hl hHU hSub B' hsep.right_le)
      _ = (g '' (pushHypergraphOn hK hg hf hl hHU hSub A' hsep.left_le ∩
          pushHypergraphOn hK hg hf hl hHU hSub B' hsep.right_le).vertexSet).ncard :=
        (hinj.ncard_image).symm
      _ ≤ separationOrder A' B' := Set.ncard_le_ncard hsub_img (A' ∩ B').vertexSet_finite

omit [T2Space S_hat] in
/-- Characterization of `GM12.inducedAcross ι H' H φ T₁` in terms of `pushHypergraphOn`. -/
theorem mem_inducedAcross_iff_pushHypergraphOn
    {P₁ : Set S'} {ι : P₁ → S_hat}
    {K : Set S_hat} (hK : IsCompact K)
    {g : S_hat → S'} {f : S' → S_hat}
    (hg : ContinuousOn g K) (hf : ContinuousOn f (g '' K)) (hl : LeftInvOn f g K)
    {H : Drawing S_hat} (hHU : H.U ⊆ K)
    {H' : Drawing S'}
    (hSub : (liftDrawingOn hK hg hf hl H hHU).IsSubdrawing H')
    (hU_P₁ : H'.U ∩ P₁ = (liftDrawingOn hK hg hf hl H hHU).U)
    (hV_P₁ : H'.V ∩ P₁ = (liftDrawingOn hK hg hf hl H hHU).V)
    (hι_g : ∀ y ∈ K, ∀ hy : g y ∈ P₁, ι ⟨g y, hy⟩ = y)
    {φ : ℕ} {T₁ : Set (Hypergraph S_hat (Set S_hat) × Hypergraph S_hat (Set S_hat))}
    (hT₁ : IsTangle H.toHypergraph φ T₁)
    {A' B' : Hypergraph S' (Set S')} :
    (A', B') ∈ GM12.inducedAcross ι H' H φ T₁ ↔
      ∃ hsep : H'.toHypergraph.IsSeparation A' B',
        separationOrder A' B' < φ ∧
        (pushHypergraphOn hK hg hf hl hHU hSub A' hsep.left_le,
         pushHypergraphOn hK hg hf hl hHU hSub B' hsep.right_le) ∈ T₁ := by
  have hVertex_eq : ∀ {C' : Hypergraph S' (Set S')} (hC' : C' ≤ H'.toHypergraph),
      ι '' ((↑) ⁻¹' C'.vertexSet) =
        (pushHypergraphOn hK hg hf hl hHU hSub C' hC').vertexSet := by
    intro C' hC'
    ext y
    constructor
    · rintro ⟨⟨x, hxP₁⟩, hxC', rfl⟩
      have hx_g : x ∈ g '' H.V := by
        have : x ∈ H'.V ∩ P₁ := ⟨hC'.vertexSet_subset hxC', hxP₁⟩
        rwa [hV_P₁] at this
      obtain ⟨v, hvV, rfl⟩ := hx_g
      rw [hι_g v (H.V_subset_U.trans hHU hvV) hxP₁]
      exact ⟨hvV, hxC'⟩
    · rintro ⟨hyV, hgyC'⟩
      have hgyP₁ : g y ∈ P₁ := by
        have : g y ∈ H'.V ∩ P₁ := by
          rw [hV_P₁]
          exact ⟨y, hyV, rfl⟩
        exact this.2
      exact ⟨⟨g y, hgyP₁⟩, hgyC', hι_g y (H.V_subset_U.trans hHU hyV) hgyP₁⟩
  have hEdge_iff : ∀ {C' : Hypergraph S' (Set S')} (hC' : C' ≤ H'.toHypergraph),
      ∀ e ∈ H.E, (∃ f' ∈ C'.edgeSet, e = ι '' ((↑) ⁻¹' f')) ↔
        e ∈ (pushHypergraphOn hK hg hf hl hHU hSub C' hC').edgeSet := by
    intro C' hC' e he
    constructor
    · rintro ⟨f', hf'C', he_eq⟩
      refine ⟨he, ?_⟩
      have hf'H' : f' ∈ H'.E := hC'.edgeSet_subset hf'C'
      obtain ⟨y, hye⟩ := he.1
      have hy_img : y ∈ ι '' ((↑) ⁻¹' f') := he_eq ▸ hye
      obtain ⟨⟨x, hxP₁⟩, hxf', rfl⟩ := hy_img
      have hx_diff : x ∈ H'.U \ H'.V := hf'H'.2.1 hxf'
      have hx_H₁_diff : x ∈ (liftDrawingOn hK hg hf hl H hHU).U \
          (liftDrawingOn hK hg hf hl H hHU).V := by
        refine ⟨?_, fun hxV₁ => hx_diff.2 (hSub.1 hxV₁)⟩
        rw [← hU_P₁]
        exact ⟨hx_diff.1, hxP₁⟩
      obtain ⟨e₁', he₁'_H₁, hxe₁'⟩ := GM11.exists_mem_arcComponent hx_H₁_diff
      have he₁'_H' : e₁' ∈ H'.E := hSub.2 he₁'_H₁
      have hf'_eq : f' = e₁' :=
        GM11.arcComponent_eq hf'H' he₁'_H' hxf' hxe₁'
      subst hf'_eq
      change f' ∈ (liftDrawingOn hK hg hf hl H hHU).E at he₁'_H₁
      rw [liftDrawingOn_E hK hg hf hl H hHU] at he₁'_H₁
      obtain ⟨e₀, he₀, rfl⟩ := he₁'_H₁
      have h_img_e₀ : ι '' ((↑) ⁻¹' (g '' e₀)) = e₀ := by
        ext z
        constructor
        · rintro ⟨⟨w, hwP₁⟩, ⟨z₀, hz₀, rfl⟩, rfl⟩
          rw [hι_g z₀ (hHU (he₀.2.1 hz₀).1) hwP₁]
          exact hz₀
        · intro hz₀
          have hgz_P₁ : g z ∈ P₁ := by
            have : g z ∈ H'.U ∩ P₁ := by
              rw [hU_P₁]
              exact ⟨z, (he₀.2.1 hz₀).1, rfl⟩
            exact this.2
          exact ⟨⟨g z, hgz_P₁⟩, ⟨z, hz₀, rfl⟩, hι_g z (hHU (he₀.2.1 hz₀).1) hgz_P₁⟩
      have he_e₀ : e = e₀ := he_eq.trans h_img_e₀
      subst he_e₀
      exact hf'C'
    · rintro ⟨_, hge_C'⟩
      refine ⟨g '' e, hge_C', ?_⟩
      ext z
      constructor
      · intro hz
        have hgz_P₁ : g z ∈ P₁ := by
          have : g z ∈ H'.U ∩ P₁ := by
            rw [hU_P₁]
            exact ⟨z, (he.2.1 hz).1, rfl⟩
          exact this.2
        exact ⟨⟨g z, hgz_P₁⟩, ⟨z, hz, rfl⟩, hι_g z (hHU (he.2.1 hz).1) hgz_P₁⟩
      · rintro ⟨⟨w, hwP₁⟩, ⟨z₀, hz₀, rfl⟩, rfl⟩
        rw [hι_g z₀ (hHU (he.2.1 hz₀).1) hwP₁]
        exact hz₀
  constructor
  · rintro ⟨hsep, hord, ⟨q₁, q₂⟩, hq_mem, hq₁V, hq₂V, hq₁E, hq₂E⟩
    refine ⟨hsep, hord, ?_⟩
    have hq_sep := hT₁.isSeparation hq_mem
    have hq₁_eq : q₁ = pushHypergraphOn hK hg hf hl hHU hSub A' hsep.left_le := by
      refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hq_sep.left_le
        (pushHypergraphOn_le hK hg hf hl hHU hSub A' hsep.left_le)
        (hq₁V.trans (hVertex_eq hsep.left_le)) ?_
      ext e
      constructor
      · intro heq₁
        have heH : e ∈ H.E := hq_sep.left_le.edgeSet_subset heq₁
        exact (hEdge_iff hsep.left_le e heH).mp ((hq₁E e heH).mp heq₁)
      · intro hePush
        have heH : e ∈ H.E := hePush.1
        exact (hq₁E e heH).mpr ((hEdge_iff hsep.left_le e heH).mpr hePush)
    have hq₂_eq : q₂ = pushHypergraphOn hK hg hf hl hHU hSub B' hsep.right_le := by
      refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hq_sep.right_le
        (pushHypergraphOn_le hK hg hf hl hHU hSub B' hsep.right_le)
        (hq₂V.trans (hVertex_eq hsep.right_le)) ?_
      ext e
      constructor
      · intro heq₂
        have heH : e ∈ H.E := hq_sep.right_le.edgeSet_subset heq₂
        exact (hEdge_iff hsep.right_le e heH).mp ((hq₂E e heH).mp heq₂)
      · intro hePush
        have heH : e ∈ H.E := hePush.1
        exact (hq₂E e heH).mpr ((hEdge_iff hsep.right_le e heH).mpr hePush)
    rwa [← hq₁_eq, ← hq₂_eq]
  · rintro ⟨hsep, hord, hmem⟩
    refine ⟨hsep, hord,
      (pushHypergraphOn hK hg hf hl hHU hSub A' hsep.left_le,
       pushHypergraphOn hK hg hf hl hHU hSub B' hsep.right_le),
      hmem, (hVertex_eq hsep.left_le).symm, (hVertex_eq hsep.right_le).symm,
      fun e he => (hEdge_iff hsep.left_le e he).symm,
      fun e he => (hEdge_iff hsep.right_le e he).symm⟩

private theorem controlled_gluing_respects_tangle_on_small_sides
    {α : Type u}
    {β : Type v}
    {S' : Type w}
    {S_hat : Type w}
    [TopologicalSpace S']
    [T2Space S']
    [TopologicalSpace S_hat]
    {G : Graph α β}
    {P₁ : Set S'}
    {ι : ↑P₁ → S_hat}
    {K : Set S_hat}
    (hK : IsCompact K)
    {g : S_hat → S'}
    {f : S' → S_hat}
    (hg : ContinuousOn g K)
    (hf : ContinuousOn f (g '' K))
    (hl : LeftInvOn f g K)
    {H : Drawing S_hat}
    (hHU : H.U ⊆ K)
    (η : SpanEmbedding H G)
    {H' : Drawing S'}
    (η' : SpanEmbedding H' G)
    (hSub : (liftDrawingOn hK hg hf hl H hHU).IsSubdrawing H')
    (hU_P₁ : H'.U ∩ P₁ = (liftDrawingOn hK hg hf hl H hHU).U)
    (hV_P₁ : H'.V ∩ P₁ = (liftDrawingOn hK hg hf hl H hHU).V)
    (hι_g : ∀ y ∈ K, ∀ (hy : g y ∈ P₁), ι ⟨g y, hy⟩ = y)
    (hη'_v : ∀ v ∈ H.V, η'.vMap (g v) = η.vMap v)
    (hη'_e : ∀ e ∈ H.E, η'.eMap (g '' e) = η.eMap e)
    {θ_star : ℕ}
    {φ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T₁ : Set (Hypergraph S_hat (Set S_hat) × Hypergraph S_hat (Set S_hat))}
    (hCtrl₁ : IsControllingTangle G H η θ_star φ T_star T₁)
    (hT₁ : IsTangle H.toHypergraph φ T₁)
    (hV_star : V(G).Finite)
    (hE_star : E(G).Finite) :
    ∀ ⦃A B : Hypergraph α β⦄, (ofGraph G hV_star hE_star).IsSeparation A B → A.separationOrder B <
      φ → ∀ ⦃A_H' B_H' : Hypergraph S' (Set S')⦄, IsRestrictedSeparation H' G η' A B A_H' B_H' →
      (A, B) ∈ T_star → (A_H', B_H') ∈ GM12.inducedAcross ι H' H φ T₁ := by
  intro A B hsepAB hordAB A_H' B_H' hRestr' hAB_star
  have hRestr'_v : ∀ {C : Hypergraph α β} {C_H' : Hypergraph S' (Set S')},
      C_H' ≤ H'.toHypergraph →
      η'.vMap '' C_H'.vertexSet = C.vertexSet ∩ V(η'.imageGraph) →
      ∀ x ∈ H'.V, x ∈ C_H'.vertexSet ↔ η'.vMap x ∈ C.vertexSet := by
    intro C C_H' hC_le hImg x hxV
    constructor
    · intro hxC
      have : η'.vMap x ∈ η'.vMap '' C_H'.vertexSet := ⟨x, hxC, rfl⟩
      rw [hImg] at this
      exact this.1
    · intro hxC
      have : η'.vMap x ∈ C.vertexSet ∩ V(η'.imageGraph) := ⟨hxC, η'.bijOn_v.mapsTo hxV⟩
      rw [← hImg] at this
      obtain ⟨x', hx'C, heq⟩ := this
      have hx'V : x' ∈ H'.V := hC_le.vertexSet_subset hx'C
      exact η'.bijOn_v.injOn hx'V hxV heq ▸ hx'C
  have hRestr'_e : ∀ {C : Hypergraph α β} {C_H' : Hypergraph S' (Set S')},
      C_H' ≤ H'.toHypergraph →
      η'.eMap '' C_H'.edgeSet = C.edgeSet ∩ E(η'.imageGraph) →
      ∀ e' ∈ H'.E, e' ∈ C_H'.edgeSet ↔ η'.eMap e' ∈ C.edgeSet := by
    intro C C_H' hC_le hImg e' he'E
    constructor
    · intro he'C
      have : η'.eMap e' ∈ η'.eMap '' C_H'.edgeSet := ⟨e', he'C, rfl⟩
      rw [hImg] at this
      exact this.1
    · intro he'C
      have : η'.eMap e' ∈ C.edgeSet ∩ E(η'.imageGraph) := ⟨he'C, η'.bijOn_e.mapsTo he'E⟩
      rw [← hImg] at this
      obtain ⟨e'', he''C, heq⟩ := this
      have he''E : e'' ∈ H'.E := hC_le.edgeSet_subset he''C
      exact η'.bijOn_e.injOn he''E he'E heq ▸ he''C
  have hord_le : separationOrder A_H' B_H' ≤ separationOrder A B := by
    have hsub_img : η'.vMap '' (A_H' ∩ B_H').vertexSet ⊆ (A ∩ B).vertexSet := by
      rintro a ⟨x, ⟨hxA, hxB⟩, rfl⟩
      have hxV : x ∈ H'.V := hRestr'.1.left_le.vertexSet_subset hxA
      exact ⟨(hRestr'_v hRestr'.1.left_le hRestr'.2.1 x hxV).mp hxA,
        (hRestr'_v hRestr'.1.right_le hRestr'.2.2.2.1 x hxV).mp hxB⟩
    have hinj : InjOn η'.vMap (A_H' ∩ B_H').vertexSet :=
      η'.bijOn_v.injOn.mono fun x ⟨hxA, _⟩ => hRestr'.1.left_le.vertexSet_subset hxA
    calc separationOrder A_H' B_H'
      _ = (η'.vMap '' (A_H' ∩ B_H').vertexSet).ncard := (hinj.ncard_image).symm
      _ ≤ separationOrder A B := Set.ncard_le_ncard hsub_img (A ∩ B).vertexSet_finite
  let A_push := pushHypergraphOn hK hg hf hl hHU hSub A_H' hRestr'.1.left_le
  let B_push := pushHypergraphOn hK hg hf hl hHU hSub B_H' hRestr'.1.right_le
  have hRestr_push : IsRestrictedSeparation H G η A B A_push B_push := by
    refine ⟨(isSeparation_pushHypergraphOn hK hg hf hl hHU hSub hRestr'.1).1, ?_, ?_, ?_, ?_⟩
    · ext a
      constructor
      · rintro ⟨v, ⟨hvH, hgvA⟩, rfl⟩
        have hgvH' : g v ∈ H'.V := hSub.1 ⟨v, hvH, rfl⟩
        have hvA : η.vMap v ∈ A.vertexSet := by
          rw [← hη'_v v hvH]
          exact (hRestr'_v hRestr'.1.left_le hRestr'.2.1 (g v) hgvH').mp hgvA
        exact ⟨hvA, η.bijOn_v.mapsTo hvH⟩
      · rintro ⟨haA, haIm⟩
        obtain ⟨v, hvH, rfl⟩ := η.bijOn_v.surjOn haIm
        have hgvH' : g v ∈ H'.V := hSub.1 ⟨v, hvH, rfl⟩
        refine ⟨v, ⟨hvH, ?_⟩, rfl⟩
        refine (hRestr'_v hRestr'.1.left_le hRestr'.2.1 (g v) hgvH').mpr ?_
        rwa [hη'_v v hvH]
    · ext b
      constructor
      · rintro ⟨e, ⟨heH, hgeA⟩, rfl⟩
        have hgeH' : g '' e ∈ H'.E := by
          refine hSub.2 ?_
          rw [liftDrawingOn_E hK hg hf hl H hHU]
          exact ⟨e, heH, rfl⟩
        have heA : η.eMap e ∈ A.edgeSet := by
          rw [← hη'_e e heH]
          exact (hRestr'_e hRestr'.1.left_le hRestr'.2.2.1 (g '' e) hgeH').mp hgeA
        exact ⟨heA, η.bijOn_e.mapsTo heH⟩
      · rintro ⟨hbA, hbIm⟩
        obtain ⟨e, heH, rfl⟩ := η.bijOn_e.surjOn hbIm
        have hgeH' : g '' e ∈ H'.E := by
          refine hSub.2 ?_
          rw [liftDrawingOn_E hK hg hf hl H hHU]
          exact ⟨e, heH, rfl⟩
        refine ⟨e, ⟨heH, ?_⟩, rfl⟩
        refine (hRestr'_e hRestr'.1.left_le hRestr'.2.2.1 (g '' e) hgeH').mpr ?_
        rwa [hη'_e e heH]
    · ext a
      constructor
      · rintro ⟨v, ⟨hvH, hgvB⟩, rfl⟩
        have hgvH' : g v ∈ H'.V := hSub.1 ⟨v, hvH, rfl⟩
        have hvB : η.vMap v ∈ B.vertexSet := by
          rw [← hη'_v v hvH]
          exact (hRestr'_v hRestr'.1.right_le hRestr'.2.2.2.1 (g v) hgvH').mp hgvB
        exact ⟨hvB, η.bijOn_v.mapsTo hvH⟩
      · rintro ⟨haB, haIm⟩
        obtain ⟨v, hvH, rfl⟩ := η.bijOn_v.surjOn haIm
        have hgvH' : g v ∈ H'.V := hSub.1 ⟨v, hvH, rfl⟩
        refine ⟨v, ⟨hvH, ?_⟩, rfl⟩
        refine (hRestr'_v hRestr'.1.right_le hRestr'.2.2.2.1 (g v) hgvH').mpr ?_
        rwa [hη'_v v hvH]
    · ext b
      constructor
      · rintro ⟨e, ⟨heH, hgeB⟩, rfl⟩
        have hgeH' : g '' e ∈ H'.E := by
          refine hSub.2 ?_
          rw [liftDrawingOn_E hK hg hf hl H hHU]
          exact ⟨e, heH, rfl⟩
        have heB : η.eMap e ∈ B.edgeSet := by
          rw [← hη'_e e heH]
          exact (hRestr'_e hRestr'.1.right_le hRestr'.2.2.2.2 (g '' e) hgeH').mp hgeB
        exact ⟨heB, η.bijOn_e.mapsTo heH⟩
      · rintro ⟨hbB, hbIm⟩
        obtain ⟨e, heH, rfl⟩ := η.bijOn_e.surjOn hbIm
        have hgeH' : g '' e ∈ H'.E := by
          refine hSub.2 ?_
          rw [liftDrawingOn_E hK hg hf hl H hHU]
          exact ⟨e, heH, rfl⟩
        refine ⟨e, ⟨heH, ?_⟩, rfl⟩
        refine (hRestr'_e hRestr'.1.right_le hRestr'.2.2.2.2 (g '' e) hgeH').mpr ?_
        rwa [hη'_e e heH]
  have hPush_in_T₁ : (A_push, B_push) ∈ T₁ :=
    (hCtrl₁.controls hsepAB hordAB hRestr_push).mp hAB_star
  exact (mem_inducedAcross_iff_pushHypergraphOn hK hg hf hl hHU hSub
    hU_P₁ hV_P₁ hι_g hT₁).mpr ⟨hRestr'.1, lt_of_le_of_lt hord_le hordAB, hPush_in_T₁⟩

omit [T2Space S_hat] in
/-- `GM12.inducedAcross ι H' H φ T₁` is a tangle of order `φ` in `H'.toHypergraph`, and if `T₁` is
controlled by `T_star` via `η`, then `GM12.inducedAcross ι H' H φ T₁` is controlled by `T_star`
via `η'`. -/
theorem isTangle_and_isControlling_inducedAcross
    {G : Graph α β}
    {P₁ : Set S'} {ι : P₁ → S_hat}
    {K : Set S_hat} (hK : IsCompact K)
    {g : S_hat → S'} {f : S' → S_hat}
    (hg : ContinuousOn g K) (hf : ContinuousOn f (g '' K)) (hl : LeftInvOn f g K)
    {H : Drawing S_hat} (hHU : H.U ⊆ K) (η : SpanEmbedding H G)
    {H' : Drawing S'} (η' : SpanEmbedding H' G)
    (hSub : (liftDrawingOn hK hg hf hl H hHU).IsSubdrawing H')
    (hU_P₁ : H'.U ∩ P₁ = (liftDrawingOn hK hg hf hl H hHU).U)
    (hV_P₁ : H'.V ∩ P₁ = (liftDrawingOn hK hg hf hl H hHU).V)
    (hι_g : ∀ y ∈ K, ∀ hy : g y ∈ P₁, ι ⟨g y, hy⟩ = y)
    (hη'_v : ∀ v ∈ H.V, η'.vMap (g v) = η.vMap v)
    (hη'_e : ∀ e ∈ H.E, η'.eMap (g '' e) = η.eMap e)
    {θ_star φ : ℕ} {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T₁ : Set (Hypergraph S_hat (Set S_hat) × Hypergraph S_hat (Set S_hat))}
    (hCtrl₁ : IsControllingTangle G H η θ_star φ T_star T₁) :
    IsTangle H'.toHypergraph φ (GM12.inducedAcross ι H' H φ T₁) ∧
    IsControllingTangle G H' η' θ_star φ T_star (GM12.inducedAcross ι H' H φ T₁) := by
  have hT₁ := hCtrl₁.isTangle_H
  have hT' : IsTangle H'.toHypergraph φ (GM12.inducedAcross ι H' H φ T₁) := by
    refine ⟨hT₁.one_le, fun _ _ h => h.1, fun _ _ h => h.2.1, ?_, ?_, ?_⟩
    · intro A' B' hsep hord
      obtain ⟨hsep₁, hle₁⟩ := isSeparation_pushHypergraphOn hK hg hf hl hHU hSub hsep
      have hord₁ := lt_of_le_of_lt hle₁ hord
      rcases hT₁.axiom1 hsep₁ hord₁ with h1 | h2
      · exact Or.inl ((mem_inducedAcross_iff_pushHypergraphOn hK hg hf hl hHU hSub
          hU_P₁ hV_P₁ hι_g hT₁).mpr ⟨hsep, hord, h1⟩)
      · exact Or.inr ((mem_inducedAcross_iff_pushHypergraphOn hK hg hf hl hHU hSub
          hU_P₁ hV_P₁ hι_g hT₁).mpr ⟨hsep.symm, by rwa [separationOrder_comm], h2⟩)
    · intro A₁ B₁ A₂ B₂ A₃ B₃ h1 h2 h3 hcov
      obtain ⟨hsep1, _, hm1⟩ := (mem_inducedAcross_iff_pushHypergraphOn hK hg hf hl hHU hSub
        hU_P₁ hV_P₁ hι_g hT₁).mp h1
      obtain ⟨hsep2, _, hm2⟩ := (mem_inducedAcross_iff_pushHypergraphOn hK hg hf hl hHU hSub
        hU_P₁ hV_P₁ hι_g hT₁).mp h2
      obtain ⟨hsep3, _, hm3⟩ := (mem_inducedAcross_iff_pushHypergraphOn hK hg hf hl hHU hSub
        hU_P₁ hV_P₁ hι_g hT₁).mp h3
      apply hT₁.axiom2 hm1 hm2 hm3
      have hle1 := pushHypergraphOn_le hK hg hf hl hHU hSub A₁ hsep1.left_le
      have hle2 := pushHypergraphOn_le hK hg hf hl hHU hSub A₂ hsep2.left_le
      have hle3 := pushHypergraphOn_le hK hg hf hl hHU hSub A₃ hsep3.left_le
      refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
        (union_le (union_le hle1 hle2) hle3) le_rfl ?_ ?_
      · ext v
        change (v ∈ H.V ∧ g v ∈ A₁.vertexSet ∨ v ∈ H.V ∧ g v ∈ A₂.vertexSet) ∨
          (v ∈ H.V ∧ g v ∈ A₃.vertexSet) ↔ v ∈ H.V
        have hV : A₁.vertexSet ∪ A₂.vertexSet ∪ A₃.vertexSet = H'.V :=
          congrArg Hypergraph.vertexSet hcov
        constructor
        · rintro ((⟨hv, _⟩ | ⟨hv, _⟩) | ⟨hv, _⟩) <;> exact hv
        · intro hv
          have hgv : g v ∈ A₁.vertexSet ∪ A₂.vertexSet ∪ A₃.vertexSet :=
            hV.symm ▸ hSub.1 ⟨v, hv, rfl⟩
          rcases hgv with (h1' | h2') | h3'
          · exact Or.inl (Or.inl ⟨hv, h1'⟩)
          · exact Or.inl (Or.inr ⟨hv, h2'⟩)
          · exact Or.inr ⟨hv, h3'⟩
      · ext e
        change (e ∈ H.E ∧ g '' e ∈ A₁.edgeSet ∨ e ∈ H.E ∧ g '' e ∈ A₂.edgeSet) ∨
          (e ∈ H.E ∧ g '' e ∈ A₃.edgeSet) ↔ e ∈ H.E
        have hE : A₁.edgeSet ∪ A₂.edgeSet ∪ A₃.edgeSet = H'.E :=
          congrArg Hypergraph.edgeSet hcov
        constructor
        · rintro ((⟨he, _⟩ | ⟨he, _⟩) | ⟨he, _⟩) <;> exact he
        · intro he
          have hge : g '' e ∈ A₁.edgeSet ∪ A₂.edgeSet ∪ A₃.edgeSet := by
            rw [hE]
            refine hSub.2 ?_
            rw [liftDrawingOn_E hK hg hf hl H hHU]
            exact ⟨e, he, rfl⟩
          rcases hge with (h1' | h2') | h3'
          · exact Or.inl (Or.inl ⟨he, h1'⟩)
          · exact Or.inl (Or.inr ⟨he, h2'⟩)
          · exact Or.inr ⟨he, h3'⟩
    · intro A' B' hAB' hV
      obtain ⟨hsep, _, hm⟩ := (mem_inducedAcross_iff_pushHypergraphOn hK hg hf hl hHU hSub
        hU_P₁ hV_P₁ hι_g hT₁).mp hAB'
      apply hT₁.axiom3 hm
      ext v
      change v ∈ H.V ∧ g v ∈ A'.vertexSet ↔ v ∈ H.V
      rw [hV]
      exact ⟨fun h => h.1, fun hv => ⟨hv, hSub.1 ⟨v, hv, rfl⟩⟩⟩
  refine ⟨hT', ⟨hCtrl₁.theta_le, hCtrl₁.isTangle_star, hT', ?_⟩⟩
  have hV_star := hCtrl₁.isTangle_star.finite_V
  have hE_star := hCtrl₁.isTangle_star.finite_E
  have hForward : ∀ ⦃A B : Hypergraph α β⦄,
      (Hypergraph.ofGraph G hV_star hE_star).IsSeparation A B →
      separationOrder A B < φ →
      ∀ ⦃A_H' B_H' : Hypergraph S' (Set S')⦄,
        IsRestrictedSeparation H' G η' A B A_H' B_H' →
        (A, B) ∈ T_star → (A_H', B_H') ∈ GM12.inducedAcross ι H' H φ T₁ := by
    exact controlled_gluing_respects_tangle_on_small_sides (α := α) (β := β) (S' := S') (S_hat :=
      S_hat) (G := G) (P₁ := P₁) (ι := ι) (K := K) hK (g := g) (f := f) hg hf hl (H := H) hHU η
      (H' := H') η' hSub hU_P₁ hV_P₁ hι_g hη'_v hη'_e (θ_star := θ_star) (φ := φ) (T_star :=
      T_star) (T₁ := T₁) hCtrl₁ hT₁ hV_star hE_star
  intro A B hsepAB hordAB A_H' B_H' hRestr'
  refine ⟨hForward hsepAB hordAB hRestr', fun hAB' => ?_⟩
  by_contra hnot
  have hord_star : separationOrder A B < θ_star := lt_of_lt_of_le hordAB hCtrl₁.theta_le
  have hBA_star : (B, A) ∈ T_star :=
    (hCtrl₁.isTangle_star.isTangle.axiom1 hsepAB hord_star).resolve_left hnot
  have hRestr'_symm : IsRestrictedSeparation H' G η' B A B_H' A_H' :=
    ⟨hRestr'.1.symm, hRestr'.2.2.2.1, hRestr'.2.2.2.2, hRestr'.2.1, hRestr'.2.2.1⟩
  have hBA' : (B_H', A_H') ∈ GM12.inducedAcross ι H' H φ T₁ :=
    hForward hsepAB.symm (by rwa [separationOrder_comm]) hRestr'_symm hBA_star
  exact GM10.theorem_2_1_proof hT' hAB' hBA'

omit [T2Space S'] in
/-- When `H` is a subdrawing of `H'` on the same surface `S'` and `2 ≤ θ`,
`GM10.inducedTangle H'.toHypergraph H.toHypergraph T θ` equals
`GM12.inducedBySubgraph H'.toHypergraph H.toHypergraph θ T`, and if `T` is controlled by `T_star`
via `η` and `η'` agrees with `η` on `H.V` and `H.E`, then `GM10.inducedTangle` is controlled by
`T_star` via `η'`. -/
theorem inducedTangle_eq_and_isControlling_of_isSubdrawing
    {G : Graph α β} {H H' : Drawing S'} {η : SpanEmbedding H G} {η' : SpanEmbedding H' G}
    (hSub : H.IsSubdrawing H')
    (hη'_v : ∀ v ∈ H.V, η'.vMap v = η.vMap v)
    (hη'_e : ∀ e ∈ H.E, η'.eMap e = η.eMap e)
    {θ_star θ : ℕ} {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))}
    (hθ : 2 ≤ θ)
    (hCtrl : IsControllingTangle G H η θ_star θ T_star T) :
    GM10.inducedTangle H'.toHypergraph H.toHypergraph T θ =
      GM12.inducedBySubgraph H'.toHypergraph H.toHypergraph θ T ∧
    IsTangle H'.toHypergraph θ (GM10.inducedTangle H'.toHypergraph H.toHypergraph T θ) ∧
    IsControllingTangle G H' η' θ_star θ T_star
      (GM10.inducedTangle H'.toHypergraph H.toHypergraph T θ) := by
  have hSubHyp : H.toHypergraph ≤ H'.toHypergraph := toHypergraph_le_of_isSubdrawing hSub
  have hT := hCtrl.isTangle_H
  have hEq : GM10.inducedTangle H'.toHypergraph H.toHypergraph T θ =
      GM12.inducedBySubgraph H'.toHypergraph H.toHypergraph θ T := by
    ext ⟨A, B⟩
    constructor
    · rintro ⟨hsep, hord, ⟨C, D⟩, hCD, hCE⟩
      refine ⟨hsep, hord, ?_⟩
      obtain ⟨hsep₀, hle₀⟩ := isSeparation_inter_subhypergraph hSubHyp hsep
      have hord₀ : separationOrder (A ∩ H.toHypergraph) (B ∩ H.toHypergraph) < θ :=
        lt_of_le_of_lt hle₀ hord
      exact GM10.theorem_2_9_proof hT hCD hsep₀ hord₀
        (Or.inr (Or.inr ⟨hθ, subset_of_eq hCE.symm⟩))
    · rintro ⟨hsep, hord, hmem₀⟩
      exact ⟨hsep, hord, (A ∩ H.toHypergraph, B ∩ H.toHypergraph), hmem₀, rfl⟩
  have hT' : IsTangle H'.toHypergraph θ
      (GM10.inducedTangle H'.toHypergraph H.toHypergraph T θ) := by
    rw [hEq]
    exact isTangle_inducedBySubgraph hSubHyp hT
  refine ⟨hEq, hT', ⟨hCtrl.theta_le, hCtrl.isTangle_star, hT', ?_⟩⟩
  have hV_star := hCtrl.isTangle_star.finite_V
  have hE_star := hCtrl.isTangle_star.finite_E
  have hForward : ∀ ⦃A B : Hypergraph α β⦄,
      (Hypergraph.ofGraph G hV_star hE_star).IsSeparation A B →
      separationOrder A B < θ →
      ∀ ⦃A_H' B_H' : Hypergraph S' (Set S')⦄,
        IsRestrictedSeparation H' G η' A B A_H' B_H' →
        (A, B) ∈ T_star →
        (A_H', B_H') ∈ GM10.inducedTangle H'.toHypergraph H.toHypergraph T θ := by
    intro A B hsepAB hordAB A_H' B_H' hRestr' hAB_star
    have hRestr'_e : ∀ e' ∈ H'.E, e' ∈ A_H'.edgeSet ↔ η'.eMap e' ∈ A.edgeSet := by
      intro e' he'E
      constructor
      · intro he'A
        have : η'.eMap e' ∈ η'.eMap '' A_H'.edgeSet := ⟨e', he'A, rfl⟩
        rw [hRestr'.2.2.1] at this
        exact this.1
      · intro he'A
        have : η'.eMap e' ∈ A.edgeSet ∩ E(η'.imageGraph) := ⟨he'A, η'.bijOn_e.mapsTo he'E⟩
        rw [← hRestr'.2.2.1] at this
        obtain ⟨e'', he''A, heq⟩ := this
        have he''E : e'' ∈ H'.E := hRestr'.1.left_le.edgeSet_subset he''A
        exact η'.bijOn_e.injOn he''E he'E heq ▸ he''A
    have hord_le : separationOrder A_H' B_H' ≤ separationOrder A B := by
      have hsub_img : η'.vMap '' (A_H' ∩ B_H').vertexSet ⊆ (A ∩ B).vertexSet := by
        rintro a ⟨x, ⟨hxA, hxB⟩, rfl⟩
        have h1 : η'.vMap x ∈ η'.vMap '' A_H'.vertexSet := ⟨x, hxA, rfl⟩
        have h2 : η'.vMap x ∈ η'.vMap '' B_H'.vertexSet := ⟨x, hxB, rfl⟩
        rw [hRestr'.2.1] at h1
        rw [hRestr'.2.2.2.1] at h2
        exact ⟨h1.1, h2.1⟩
      have hinj : InjOn η'.vMap (A_H' ∩ B_H').vertexSet :=
        η'.bijOn_v.injOn.mono fun x ⟨hxA, _⟩ => hRestr'.1.left_le.vertexSet_subset hxA
      calc separationOrder A_H' B_H'
        _ = (η'.vMap '' (A_H' ∩ B_H').vertexSet).ncard := (hinj.ncard_image).symm
        _ ≤ separationOrder A B := Set.ncard_le_ncard hsub_img (A ∩ B).vertexSet_finite
    have hRestr_inter : IsRestrictedSeparation H G η A B
        (A_H' ∩ H.toHypergraph) (B_H' ∩ H.toHypergraph) := by
      refine ⟨(isSeparation_inter_subhypergraph hSubHyp hRestr'.1).1, ?_, ?_, ?_, ?_⟩
      · ext a
        constructor
        · rintro ⟨v, ⟨hvA', hvH⟩, rfl⟩
          rw [← hη'_v v hvH]
          have : η'.vMap v ∈ η'.vMap '' A_H'.vertexSet := ⟨v, hvA', rfl⟩
          rw [hRestr'.2.1] at this
          exact ⟨this.1, hη'_v v hvH ▸ η.bijOn_v.mapsTo hvH⟩
        · rintro ⟨haA, haIm⟩
          obtain ⟨v, hvH, rfl⟩ := η.bijOn_v.surjOn haIm
          have hvA' : v ∈ A_H'.vertexSet := by
            have : η'.vMap v ∈ A.vertexSet ∩ V(η'.imageGraph) :=
              ⟨hη'_v v hvH ▸ haA, η'.bijOn_v.mapsTo (hSub.1 hvH)⟩
            rw [← hRestr'.2.1] at this
            obtain ⟨v', hv'A, heq⟩ := this
            exact η'.bijOn_v.injOn (hRestr'.1.left_le.vertexSet_subset hv'A) (hSub.1 hvH) heq ▸ hv'A
          exact ⟨v, ⟨hvA', hvH⟩, rfl⟩
      · ext b
        constructor
        · rintro ⟨e, ⟨heA', heH⟩, rfl⟩
          rw [← hη'_e e heH]
          exact ⟨(hRestr'_e e (hSub.2 heH)).mp heA', hη'_e e heH ▸ η.bijOn_e.mapsTo heH⟩
        · rintro ⟨hbA, hbIm⟩
          obtain ⟨e, heH, rfl⟩ := η.bijOn_e.surjOn hbIm
          refine ⟨e, ⟨(hRestr'_e e (hSub.2 heH)).mpr (hη'_e e heH ▸ hbA), heH⟩, rfl⟩
      · ext a
        constructor
        · rintro ⟨v, ⟨hvB', hvH⟩, rfl⟩
          rw [← hη'_v v hvH]
          have : η'.vMap v ∈ η'.vMap '' B_H'.vertexSet := ⟨v, hvB', rfl⟩
          rw [hRestr'.2.2.2.1] at this
          exact ⟨this.1, hη'_v v hvH ▸ η.bijOn_v.mapsTo hvH⟩
        · rintro ⟨haB, haIm⟩
          obtain ⟨v, hvH, rfl⟩ := η.bijOn_v.surjOn haIm
          have hvB' : v ∈ B_H'.vertexSet := by
            have : η'.vMap v ∈ B.vertexSet ∩ V(η'.imageGraph) :=
              ⟨hη'_v v hvH ▸ haB, η'.bijOn_v.mapsTo (hSub.1
                hvH)⟩
            rw [← hRestr'.2.2.2.1] at this
            obtain ⟨v', hv'B, heq⟩
              :=
              this
            exact η'.bijOn_v.injOn (hRestr'.1.right_le.vertexSet_subset hv'B)
              (hSub.1 hvH) heq ▸ hv'B
          exact ⟨v, ⟨hvB', hvH⟩, rfl⟩
      · ext b
        constructor
        · rintro ⟨e, ⟨heB', heH⟩, rfl⟩
          rw [← hη'_e e heH]
          have : η'.eMap e ∈ η'.eMap '' B_H'.edgeSet := ⟨e, heB', rfl⟩
          rw [hRestr'.2.2.2.2] at this
          exact ⟨this.1, hη'_e e heH ▸ η.bijOn_e.mapsTo heH⟩
        · rintro ⟨hbB, hbIm⟩
          obtain ⟨e, heH, rfl⟩ := η.bijOn_e.surjOn hbIm
          have heB' : e ∈ B_H'.edgeSet := by
            have : η'.eMap e ∈ B.edgeSet ∩ E(η'.imageGraph) :=
              ⟨hη'_e e heH ▸ hbB, η'.bijOn_e.mapsTo (hSub.2 heH)⟩
            rw [← hRestr'.2.2.2.2] at this
            obtain ⟨e', he'B, heq⟩ := this
            exact η'.bijOn_e.injOn (hRestr'.1.right_le.edgeSet_subset he'B) (hSub.2 heH) heq ▸ he'B
          exact ⟨e, ⟨heB', heH⟩, rfl⟩
    have hMem_T : (A_H' ∩ H.toHypergraph, B_H' ∩ H.toHypergraph) ∈ T :=
      (hCtrl.controls hsepAB hordAB hRestr_inter).mp hAB_star
    exact ⟨hRestr'.1, lt_of_le_of_lt hord_le hordAB,
      (A_H' ∩ H.toHypergraph, B_H' ∩ H.toHypergraph), hMem_T, rfl⟩
  intro A B hsepAB hordAB A_H' B_H' hRestr'
  refine ⟨hForward hsepAB hordAB hRestr', fun hAB' => ?_⟩
  by_contra hnot
  have hord_star : separationOrder A B < θ_star := lt_of_lt_of_le hordAB hCtrl.theta_le
  have hBA_star : (B, A) ∈ T_star :=
    (hCtrl.isTangle_star.isTangle.axiom1 hsepAB hord_star).resolve_left hnot
  have hRestr'_symm : IsRestrictedSeparation H' G η' B A B_H' A_H' :=
    ⟨hRestr'.1.symm, hRestr'.2.2.2.1, hRestr'.2.2.2.2, hRestr'.2.1, hRestr'.2.2.1⟩
  have hBA' : (B_H', A_H') ∈ GM10.inducedTangle H'.toHypergraph H.toHypergraph T θ :=
    hForward hsepAB.symm (by rwa [separationOrder_comm]) hRestr'_symm hBA_star
  exact GM10.theorem_2_1_proof hT' hAB' hBA'

end InducedAcrossControl

/-! ## 4. Dials and Chords in a Striped Closed Disc (for (3.2)(iii) and (3.2)(iv)) -/

section StripedDisc

variable {S' : Type w} [TopologicalSpace S'] [T2Space S']

omit [T2Space S'] in
/-- For any subdrawing `P` of `H'`, `P.U ⊆ H'.U`. -/
theorem isSubdrawing_U_subset {P H' : Drawing S'} (hSub : P.IsSubdrawing H') :
    P.U ⊆ H'.U := by
  rw [P.U_eq, H'.U_eq]
  refine union_subset (hSub.1.trans subset_union_left) ?_
  refine iUnion₂_subset fun e he => ?_
  exact (subset_iUnion₂ (s := fun e (_ : e ∈ H'.E) => closure e) e (hSub.2 he)).trans
    subset_union_right

omit [T2Space S'] in
/-- For any subdrawing `P` of `H'`, `P.U ∩ H'.V = P.V`. -/
theorem isSubdrawing_U_inter_V {P H' : Drawing S'} (hSub : P.IsSubdrawing H') :
    P.U ∩ H'.V = P.V := by
  refine Subset.antisymm ?_ (subset_inter P.V_subset_U hSub.1)
  rintro x ⟨hxU, hxV⟩
  rw [P.U_eq] at hxU
  rcases hxU with hxPV | hxPE
  · exact hxPV
  · obtain ⟨e, heP, hxe⟩ := mem_iUnion₂.mp hxPE
    by_cases hxe_in : x ∈ e
    · exact ((hSub.2 heP).2.1 hxe_in).2 hxV |>.elim
    · have hx_cl_V : x ∈ closure e ∩ H'.V := ⟨hxe, hxV⟩
      rw [← hSub.closure_inter_V heP] at hx_cl_V
      exact hx_cl_V.2

/-- Verification of condition (iv) of (3.2) inside a closed disc `D ⊆ S'` where `D ∩ H'.U` is
contained in `B_bd ∪ ⋃ j, (Q' j).U` with `B_bd ⊆ discBd D` and no path `P` containing both ends
`u' j, v' j` of any `Q' j`. -/
theorem openDisc_of_chord_in_striped_disc
    (hS' : IsClosedSurface S')
    {H' : Drawing S'} {D B_bd : Set S'} {m' : ℕ}
    {u' v' : Fin m' → S'} {Q' : Fin m' → Drawing S'}
    (hD : IsClosedDisc D)
    (hB_bd : B_bd ⊆ discBd D)
    (hD_U : D ∩ H'.U ⊆ B_bd ∪ ⋃ j : Fin m', (Q' j).U)
    (hQ'_line : ∀ j, IsLineWithEnds (Q' j).U (u' j) (v' j))
    (hQ'_sub : ∀ j, (Q' j).IsSubdrawing H')
    (hQ'_V : ∀ j, u' j ∈ (Q' j).V ∧ v' j ∈ (Q' j).V)
    (hQ'_bd : ∀ j, (Q' j).U ∩ discBd D = {u' j, v' j})
    {F : Set S'} {u v : S'} {P : Drawing S'}
    (hPU_D : P.U ⊆ D) (hF_D : F ⊆ D)
    (hPU_bd : P.U ⊆ discBd D)
    (hF_line : IsLineWithEnds F u v)
    (hF_U : F ∩ H'.U ⊆ {u, v})
    (hP_sub : P.IsSubdrawing H')
    (hP_path : P.IsPathBetween u v)
    (hNo_both : ∀ j : Fin m', ¬ (u' j ∈ P.V ∧ v' j ∈ P.V)) :
    ∃ U₀ : Set S', IsOpenDisc U₀ ∧ IsClosedDisc (closure U₀) ∧ U₀ ⊆ D ∧
      subBd U₀ = P.U ∪ F ∧ Disjoint U₀ H'.U := by
  have : LocallyConnectedSpace S' := IsClosedSurface.locallyConnectedSpace hS'
  obtain ⟨ψ_F, hψ_F0, hψ_F1⟩ := hF_line
  have huv : u ≠ v := fun heq => zero_ne_one
    (ψ_F.injective (Subtype.ext (hψ_F0.trans (heq.trans hψ_F1.symm))))
  have huF : u ∈ F := hψ_F0 ▸ (ψ_F 0).2
  have hvF : v ∈ F := hψ_F1 ▸ (ψ_F 1).2
  have hP_line : IsLineWithEnds P.U u v := GM14.isLine_of_isPathBetween hP_path huv
  obtain ⟨ψ_P, hψ_P0, hψ_P1⟩ := hP_line
  have huPU : u ∈ P.U := hψ_P0 ▸ (ψ_P 0).2
  have hvPU : v ∈ P.U := hψ_P1 ▸ (ψ_P 1).2
  have hPU_H'U : P.U ⊆ H'.U := isSubdrawing_U_subset hP_sub
  have hPF_inter : P.U ∩ F = {u, v} := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hxP, hxF⟩
      exact hF_U ⟨hxF, hPU_H'U hxP⟩
    · rintro x (rfl | rfl)
      · exact ⟨huPU, huF⟩
      · exact ⟨hvPU, hvF⟩
  let K : Set S' := P.U ∪ F
  have hK_oArc : IsOArc K := Surface.oArc_of_lines ⟨ψ_P, hψ_P0, hψ_P1⟩ ⟨ψ_F, hψ_F0, hψ_F1⟩ hPF_inter
  have hK_D : K ⊆ D := union_subset hPU_D hF_D
  obtain ⟨Δ, ⟨hΔ_sub_D, hΔ_disc, hΔ_discBd, -, hΔ_disj_bd, -⟩, -⟩ :=
    disc_oArc D K hD hK_D hK_oArc
  have hΔ_subBd : subBd Δ = K := (IsClosedDisc.subBd_eq_discBd hS' hΔ_disc).trans hΔ_discBd
  have hΔ_fr : frontier Δ = K := (subBd_eq_frontier Δ).symm.trans hΔ_subBd
  obtain ⟨hOD_U₀, hcl_U₀, hbd_U₀⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS' hΔ_disc
  let U₀ : Set S' := Δ \ subBd Δ
  have hU₀_eq : U₀ = Δ \ K := by dsimp [U₀]; rw [hΔ_subBd]
  refine ⟨U₀, hOD_U₀, hcl_U₀.symm ▸ hΔ_disc, sdiff_subset.trans hΔ_sub_D,
    hbd_U₀.trans hΔ_subBd, ?_⟩
  rw [hU₀_eq]
  refine Set.disjoint_left.mpr fun z ⟨hzΔ, hz_not_K⟩ hzU => ?_
  have hz_not_bdD : z ∉ discBd D := Set.disjoint_left.mp hΔ_disj_bd ⟨hzΔ, hz_not_K⟩
  have hz_DU : z ∈ D ∩ H'.U := ⟨hΔ_sub_D hzΔ, hzU⟩
  rcases hD_U hz_DU with hzB | hzQ
  · exact hz_not_bdD (hB_bd hzB)
  · obtain ⟨j, hzj⟩ := mem_iUnion.mp hzQ
    have huj_bd : u' j ∈ discBd D := by
      have hmem : u' j ∈ (Q' j).U ∩ discBd D := (hQ'_bd j).symm ▸ Or.inl rfl
      exact hmem.2
    have hvj_bd : v' j ∈ discBd D := by
      have hmem : v' j ∈ (Q' j).U ∩ discBd D := (hQ'_bd j).symm ▸ Or.inr rfl
      exact hmem.2
    have hz_not_uvj : z ∉ ({u' j, v' j} : Set S') := by
      rintro (rfl | rfl)
      · exact hz_not_bdD huj_bd
      · exact hz_not_bdD hvj_bd
    have hQj_H'U : (Q' j).U ⊆ H'.U := isSubdrawing_U_subset (hQ'_sub j)
    have hdisj_fr : Disjoint ((Q' j).U \ {u' j, v' j}) (frontier Δ) := by
      rw [hΔ_fr]
      refine Set.disjoint_left.mpr fun w hw hwK => hw.2 ?_
      have hw_bd : w ∈ discBd D := by
        rcases hwK with hwP | hwF
        · exact hPU_bd hwP
        · rcases hF_U ⟨hwF, hQj_H'U hw.1⟩ with rfl | rfl
          · exact hPU_bd huPU
          · exact hPU_bd hvPU
      exact hQ'_bd j ▸ ⟨hw.1, hw_bd⟩
    have hdiff_sub : (Q' j).U \ {u' j, v' j} ⊆ Δ :=
      GM14.subset_of_disjoint_frontier
        (GM11.isPathConnected_sdiff_pair (hQ'_line j)).isConnected.isPreconnected
        hΔ_disc.isClosed hdisj_fr ⟨hzj, hz_not_uvj⟩ hzΔ
    have hQj_sub_Δ : (Q' j).U ⊆ Δ :=
      (GM11.closure_sdiff_pair (hQ'_line j)).symm.subset.trans
        (hΔ_disc.isClosed.closure_subset_iff.mpr hdiff_sub)
    have huj_U : u' j ∈ (Q' j).U := (Q' j).V_subset_U (hQ'_V j).1
    have hvj_U : v' j ∈ (Q' j).U := (Q' j).V_subset_U (hQ'_V j).2
    have huj_K : u' j ∈ K := by
      by_contra hnot
      exact Set.disjoint_left.mp hΔ_disj_bd ⟨hQj_sub_Δ huj_U, hnot⟩ huj_bd
    have hvj_K : v' j ∈ K := by
      by_contra hnot
      exact Set.disjoint_left.mp hΔ_disj_bd ⟨hQj_sub_Δ hvj_U, hnot⟩ hvj_bd
    have hKU_sub_PU : K ∩ H'.U ⊆ P.U := by
      rintro w ⟨hwP | hwF, hwU⟩
      · exact hwP
      · rcases hF_U ⟨hwF, hwU⟩ with rfl | rfl
        · exact huPU
        · exact hvPU
    have huj_PU : u' j ∈ P.U := hKU_sub_PU ⟨huj_K, hQj_H'U huj_U⟩
    have hvj_PU : v' j ∈ P.U := hKU_sub_PU ⟨hvj_K, hQj_H'U hvj_U⟩
    have huj_PV : u' j ∈ P.V :=
      (isSubdrawing_U_inter_V hP_sub) ▸ ⟨huj_PU, (hQ'_sub j).1 (hQ'_V j).1⟩
    have hvj_PV : v' j ∈ P.V :=
      (isSubdrawing_U_inter_V hP_sub) ▸ ⟨hvj_PU, (hQ'_sub j).1 (hQ'_V j).2⟩
    exact hNo_both j ⟨huj_PV, hvj_PV⟩

private theorem gluing_arc_meets_subdisc_in_closed_interval
    {S' : Type w}
    [TopologicalSpace S']
    [T2Space S']
    {D : Set S'}
    {ι : Type*}
    {u' : ι → S'}
    {v' : ι → S'}
    {F : Set S'}
    (Δ : Set S')
    (hΔ_disc : IsClosedDisc Δ)
    (hΔ_disj_bd : Disjoint (Δ \ F) (discBd D))
    (hΔ_fr : frontier Δ = F)
    (j : ι)
    (huj_bd : ∀ (k : ι), u' k ∈ discBd D)
    (hvj_bd : ∀ (k : ι), v' k ∈ discBd D)
    (aR : ℝ → S')
    (haR_cont : Continuous aR)
    (haR_0 : aR 0 = u' j)
    (haR_1 : aR 1 = v' j)
    (t₁ : ℝ)
    (t₂ : ℝ)
    (ht₁₂ : t₁ < t₂)
    (ha_F_iff : ∀ t ∈ Icc 0 1, aR t ∈ F ↔ t = t₁ ∨ t = t₂)
    (hIcc_sub_Δ : aR '' Icc t₁ t₂ ⊆ Δ) :
    ∀ t ∈ Icc 0 1, aR t ∈ Δ ↔ t ∈ Icc t₁ t₂ := by
  intro t ht
  refine ⟨fun hat_Δ => ?_, fun ht12 => hIcc_sub_Δ ⟨t, ht12, rfl⟩⟩
  constructor
  · by_contra hlt
    have hlt' : t < t₁ := lt_of_not_ge hlt
    have hI_sub : Icc 0 t ⊆ Icc 0 1 := Icc_subset_Icc_right ht.2
    have hconn : IsPreconnected (aR '' Icc 0 t) :=
      (isConnected_Icc ht.1).isPreconnected.image aR haR_cont.continuousOn
    have hdis : Disjoint (aR '' Icc 0 t) (frontier Δ) := by
      rw [hΔ_fr]
      refine Set.disjoint_left.mpr ?_
      rintro _ ⟨s, hs, rfl⟩ hsF
      rcases (ha_F_iff s (hI_sub hs)).mp hsF with rfl | rfl
      · linarith [hs.2]
      · linarith [hs.2, ht₁₂]
    have hsub0 : aR '' Icc 0 t ⊆ Δ :=
      GM14.subset_of_disjoint_frontier hconn hΔ_disc.isClosed hdis
        ⟨t, ⟨ht.1, le_rfl⟩, rfl⟩ hat_Δ
    have ha0_Δ : aR 0 ∈ Δ := hsub0 ⟨0, ⟨le_rfl, ht.1⟩, rfl⟩
    have ha0_F : aR 0 ∈ F := by
      by_contra hnot
      exact Set.disjoint_left.mp hΔ_disj_bd ⟨ha0_Δ, hnot⟩ (haR_0 ▸ huj_bd j)
    rcases (ha_F_iff 0 ⟨le_rfl, zero_le_one⟩).mp ha0_F with h1 | h2
    · linarith [ht.1]
    · linarith [ht.1, ht₁₂]
  · by_contra hgt
    have hgt' : t₂ < t := lt_of_not_ge hgt
    have hI_sub : Icc t 1 ⊆ Icc 0 1 := Icc_subset_Icc_left ht.1
    have hconn : IsPreconnected (aR '' Icc t 1) :=
      (isConnected_Icc ht.2).isPreconnected.image aR haR_cont.continuousOn
    have hdis : Disjoint (aR '' Icc t 1) (frontier Δ) := by
      rw [hΔ_fr]
      refine Set.disjoint_left.mpr ?_
      rintro _ ⟨s, hs, rfl⟩ hsF
      rcases (ha_F_iff s (hI_sub hs)).mp hsF with rfl | rfl
      · linarith [hs.1, ht₁₂]
      · linarith [hs.1]
    have hsub1 : aR '' Icc t 1 ⊆ Δ :=
      GM14.subset_of_disjoint_frontier hconn hΔ_disc.isClosed hdis
        ⟨t, ⟨le_rfl, ht.2⟩, rfl⟩ hat_Δ
    have ha1_Δ : aR 1 ∈ Δ := hsub1 ⟨1, ⟨ht.2, le_rfl⟩, rfl⟩
    have ha1_F : aR 1 ∈ F := by
      by_contra hnot
      exact Set.disjoint_left.mp hΔ_disj_bd ⟨ha1_Δ, hnot⟩ (haR_1 ▸ hvj_bd j)
    rcases (ha_F_iff 1 ⟨zero_le_one, le_rfl⟩).mp ha1_F with h1 | h2
    · linarith [ht.2, ht₁₂]
    · linarith [ht.2]

private theorem other_gluing_arcs_avoid_subdisc
    {S' : Type w}
    [TopologicalSpace S']
    [T2Space S']
    {H' : Drawing S'}
    {D : Set S'}
    {ι : Type*}
    {u' : ι → S'}
    {v' : ι → S'}
    {Q' : ι → Drawing S'}
    (hQ'_line : ∀ (j : ι), IsLineWithEnds (Q' j).U (u' j) (v' j))
    (hQ'_bd : ∀ (j : ι), (Q' j).U ∩ discBd D = {u' j, v' j})
    (hQ'_disj : Pairwise fun i j => Disjoint (Q' i).U (Q' j).U)
    {F : Set S'}
    (Δ : Set S')
    (hΔ_disc : IsClosedDisc Δ)
    (hΔ_disj_bd : Disjoint (Δ \ F) (discBd D))
    (hΔ_fr : frontier Δ = F)
    (j : ι)
    (hQj_H'U : ∀ (k : ι), (Q' k).U ⊆ H'.U)
    (huj_bd : ∀ (k : ι), u' k ∈ discBd D)
    (u : S')
    (v : S')
    (hu_Qj : u ∈ (Q' j).U)
    (hv_Qj : v ∈ (Q' j).U)
    (hFU_eq : F ∩ H'.U = {u, v}) :
    ∀ (k : ι), k ≠ j → Disjoint (Q' k).U Δ := by
  intro k hkj
  have hdis_fr : Disjoint (Q' k).U (frontier Δ) := by
    rw [hΔ_fr]
    refine Set.disjoint_left.mpr fun w hwk hwF => ?_
    have hw_uv : w ∈ ({u, v} : Set S') := hFU_eq ▸ ⟨hwF, hQj_H'U k hwk⟩
    rcases hw_uv with rfl | rfl
    · exact Set.disjoint_left.mp (hQ'_disj hkj) hwk hu_Qj
    · exact Set.disjoint_left.mp (hQ'_disj hkj) hwk hv_Qj
  refine Set.disjoint_left.mpr fun w hwk hwΔ => ?_
  obtain ⟨ψ_k, _, _⟩ := hQ'_line k
  have hconn_k : IsPreconnected (Q' k).U := by
    have hEq : (Q' k).U = range (fun s : unitInterval => (ψ_k s).1) := by
      ext x
      exact ⟨fun hx => ⟨ψ_k.symm ⟨x, hx⟩, by simp⟩, fun ⟨s, hs⟩ => hs ▸ (ψ_k s).2⟩
    rw [hEq]
    exact isPreconnected_range (continuous_subtype_val.comp ψ_k.continuous)
  have hsub_k : (Q' k).U ⊆ Δ :=
    GM14.subset_of_disjoint_frontier hconn_k hΔ_disc.isClosed hdis_fr hwk hwΔ
  have huk_U : u' k ∈ (Q' k).U := by
    have hmem : u' k ∈ (Q' k).U ∩ discBd D := (hQ'_bd k).symm ▸ Or.inl rfl
    exact hmem.1
  have huk_F : u' k ∈ F := by
    by_contra hnot
    exact Set.disjoint_left.mp hΔ_disj_bd ⟨hsub_k huk_U, hnot⟩ (huj_bd k)
  exact Set.disjoint_left.mp hdis_fr huk_U (hΔ_fr.symm ▸ huk_F)

/-- Verification of condition (iii) of (3.2) inside a closed disc `D ⊆ S'` where `D ∩ H'.U` is
contained in `B_bd ∪ ⋃ j, (Q' j).U` with `B_bd ⊆ discBd D`. -/
theorem dial_of_oArc_in_striped_disc_family
    (hS' : IsClosedSurface S')
    {H' : Drawing S'} {D B_bd : Set S'} {ι : Type*}
    {u' v' : ι → S'} {Q' : ι → Drawing S'}
    (hD : IsClosedDisc D)
    (hB_bd : B_bd ⊆ discBd D)
    (hD_U : D ∩ H'.U ⊆ B_bd ∪ ⋃ j : ι, (Q' j).U)
    (hQ'_line : ∀ j, IsLineWithEnds (Q' j).U (u' j) (v' j))
    (hQ'_sub : ∀ j, (Q' j).IsSubdrawing H')
    (hQ'_bd : ∀ j, (Q' j).U ∩ discBd D = {u' j, v' j})
    (hQ'_disj : Pairwise (fun i j => Disjoint (Q' i).U (Q' j).U))
    {F : Set S'}
    (hFD : F ⊆ D) (hF : IsOArc F) (hFU : F ∩ H'.U ⊆ H'.V) (hFV : (F ∩ H'.V).ncard ≤ 2) :
    ∃ Δ : Set S', Δ ⊆ D ∧ IsDial H' F Δ := by
  have : LocallyConnectedSpace S' := IsClosedSurface.locallyConnectedSpace hS'
  obtain ⟨Δ, ⟨hΔ_sub_D, hΔ_disc, hΔ_discBd, -, hΔ_disj_bd, -⟩, -⟩ :=
    disc_oArc D F hD hFD hF
  have hΔ_subBd : subBd Δ = F := (IsClosedDisc.subBd_eq_discBd hS' hΔ_disc).trans hΔ_discBd
  have hΔ_fr : frontier Δ = F := (subBd_eq_frontier Δ).symm.trans hΔ_subBd
  have hΔ_inter_U : (H'.interSet Δ).U = H'.U ∩ Δ :=
    (GM14.interSet_V_and_U hΔ_disc.isClosed (hΔ_subBd ▸ hFU)).2
  have hF_sub_Δ : F ⊆ Δ := hΔ_discBd ▸ Surface.discBd_subset Δ
  refine ⟨Δ, hΔ_sub_D, hΔ_disc, hΔ_subBd, ?_⟩
  by_cases hne : ((Δ \ F) ∩ H'.U).Nonempty
  · right
    obtain ⟨z₀, ⟨hz₀_Δ, hz₀_not_F⟩, hz₀_U⟩ := hne
    have hz₀_not_bdD : z₀ ∉ discBd D := Set.disjoint_left.mp hΔ_disj_bd ⟨hz₀_Δ, hz₀_not_F⟩
    have hz₀_DU : z₀ ∈ D ∩ H'.U := ⟨hΔ_sub_D hz₀_Δ, hz₀_U⟩
    have hz₀_Q : z₀ ∈ ⋃ j : ι, (Q' j).U := by
      rcases hD_U hz₀_DU with hzB | hzQ
      · exact (hz₀_not_bdD (hB_bd hzB)).elim
      · exact hzQ
    obtain ⟨j, hz₀_j⟩ := mem_iUnion.mp hz₀_Q
    have hQj_H'U : ∀ k, (Q' k).U ⊆ H'.U := fun k => isSubdrawing_U_subset (hQ'_sub k)
    have huj_bd : ∀ k, u' k ∈ discBd D := fun k => by
      have hmem : u' k ∈ (Q' k).U ∩ discBd D := (hQ'_bd k).symm ▸ Or.inl rfl
      exact hmem.2
    have hvj_bd : ∀ k, v' k ∈ discBd D := fun k => by
      have hmem : v' k ∈ (Q' k).U ∩ discBd D := (hQ'_bd k).symm ▸ Or.inr rfl
      exact hmem.2
    obtain ⟨a, ha, ha_range, ha0, ha1⟩ := (hQ'_line j).exists_arc
    obtain ⟨t₀, ht₀_eq⟩ : z₀ ∈ range a := ha_range ▸ hz₀_j
    let aR : ℝ → S' := extI a
    have haR_cont : Continuous aR := continuous_extI ha.1
    have haR_inj : InjOn aR (Icc (0 : ℝ) 1) := extI_injOn ha.2
    have haR_t₀ : aR t₀.1 = z₀ := (extI_coe a t₀).trans ht₀_eq
    have haR_0 : aR 0 = u' j := (extI_coe a 0).trans ha0
    have haR_1 : aR 1 = v' j := (extI_coe a 1).trans ha1
    have haR_mem : ∀ t ∈ Icc (0 : ℝ) 1, aR t ∈ (Q' j).U := fun t ht => by
      rw [← ha_range]
      exact ⟨⟨t, ht⟩, (extI_of_mem a ht).symm⟩
    have hex_t₁ : ∃ t₁ ∈ Icc (0 : ℝ) t₀.1, aR t₁ ∈ F := by
      by_contra hnot
      have hnot' : ∀ t ∈ Icc (0 : ℝ) t₀.1, aR t ∉ F := fun t ht htF => hnot ⟨t, ht, htF⟩
      have hconn : IsPreconnected (aR '' Icc (0 : ℝ) t₀.1) :=
        (isConnected_Icc t₀.2.1).isPreconnected.image aR haR_cont.continuousOn
      have hdis : Disjoint (aR '' Icc (0 : ℝ) t₀.1) (frontier Δ) := by
        rw [hΔ_fr]
        refine Set.disjoint_left.mpr ?_
        rintro _ ⟨t, ht, rfl⟩ htF
        exact hnot' t ht htF
      have hsub_Δ : aR '' Icc (0 : ℝ) t₀.1 ⊆ Δ :=
        GM14.subset_of_disjoint_frontier hconn hΔ_disc.isClosed hdis
          ⟨t₀.1, ⟨t₀.2.1, le_rfl⟩, rfl⟩ (haR_t₀.symm ▸ hz₀_Δ)
      have ha0_Δ : aR 0 ∈ Δ := hsub_Δ ⟨0, ⟨le_rfl, t₀.2.1⟩, rfl⟩
      have ha0_not_F : aR 0 ∉ F := hnot' 0 ⟨le_rfl, t₀.2.1⟩
      exact Set.disjoint_left.mp hΔ_disj_bd ⟨ha0_Δ, ha0_not_F⟩ (haR_0 ▸ huj_bd j)
    have hex_t₂ : ∃ t₂ ∈ Icc t₀.1 1, aR t₂ ∈ F := by
      by_contra hnot
      have hnot' : ∀ t ∈ Icc t₀.1 1, aR t ∉ F := fun t ht htF => hnot ⟨t, ht, htF⟩
      have hconn : IsPreconnected (aR '' Icc t₀.1 1) :=
        (isConnected_Icc t₀.2.2).isPreconnected.image aR haR_cont.continuousOn
      have hdis : Disjoint (aR '' Icc t₀.1 1) (frontier Δ) := by
        rw [hΔ_fr]
        refine Set.disjoint_left.mpr ?_
        rintro _ ⟨t, ht, rfl⟩ htF
        exact hnot' t ht htF
      have hsub_Δ : aR '' Icc t₀.1 1 ⊆ Δ :=
        GM14.subset_of_disjoint_frontier hconn hΔ_disc.isClosed hdis
          ⟨t₀.1, ⟨le_rfl, t₀.2.2⟩, rfl⟩ (haR_t₀.symm ▸ hz₀_Δ)
      have ha1_Δ : aR 1 ∈ Δ := hsub_Δ ⟨1, ⟨t₀.2.2, le_rfl⟩, rfl⟩
      have ha1_not_F : aR 1 ∉ F := hnot' 1 ⟨t₀.2.2, le_rfl⟩
      exact Set.disjoint_left.mp hΔ_disj_bd ⟨ha1_Δ, ha1_not_F⟩ (haR_1 ▸ hvj_bd j)
    obtain ⟨t₁, ht₁, ha_t₁_F⟩ := hex_t₁
    obtain ⟨t₂, ht₂, ha_t₂_F⟩ := hex_t₂
    have ht₁_mem : t₁ ∈ Icc (0 : ℝ) 1 := ⟨ht₁.1, ht₁.2.trans t₀.2.2⟩
    have ht₂_mem : t₂ ∈ Icc (0 : ℝ) 1 := ⟨t₀.2.1.trans ht₂.1, ht₂.2⟩
    have ht₁_lt : t₁ < t₀.1 := lt_of_le_of_ne ht₁.2 fun h => hz₀_not_F (haR_t₀ ▸ h ▸ ha_t₁_F)
    have ht₂_gt : t₀.1 < t₂ := lt_of_le_of_ne ht₂.1 fun h => hz₀_not_F (haR_t₀ ▸ h.symm ▸ ha_t₂_F)
    have ht₁₂ : t₁ < t₂ := ht₁_lt.trans ht₂_gt
    let u := aR t₁
    let v := aR t₂
    have huv : u ≠ v := fun h => ht₁₂.ne (haR_inj ht₁_mem ht₂_mem h)
    have hu_Qj : u ∈ (Q' j).U := haR_mem t₁ ht₁_mem
    have hv_Qj : v ∈ (Q' j).U := haR_mem t₂ ht₂_mem
    have hu_FV : u ∈ F ∩ H'.V := ⟨ha_t₁_F, hFU ⟨ha_t₁_F, hQj_H'U j hu_Qj⟩⟩
    have hv_FV : v ∈ F ∩ H'.V := ⟨ha_t₂_F, hFU ⟨ha_t₂_F, hQj_H'U j hv_Qj⟩⟩
    have hpair_sub : ({u, v} : Set S') ⊆ F ∩ H'.V := by
      rintro w (rfl | rfl)
      · exact hu_FV
      · exact hv_FV
    have hFV_eq : F ∩ H'.V = {u, v} := by
      refine (Set.eq_of_subset_of_ncard_le hpair_sub ?_
        (H'.finite_V.subset inter_subset_right)).symm
      rw [Set.ncard_pair huv]
      exact hFV
    have hFU_sub_FV : F ∩ H'.U ⊆ F ∩ H'.V := fun x hx => ⟨hx.1, hFU hx⟩
    have hFU_eq : F ∩ H'.U = {u, v} :=
      Subset.antisymm (hFU_sub_FV.trans hFV_eq.subset)
        (hFV_eq ▸ inter_subset_inter_right _ H'.V_subset_U)
    have ha_F_iff : ∀ t ∈ Icc (0 : ℝ) 1, aR t ∈ F ↔ t = t₁ ∨ t = t₂ := by
      intro t ht
      constructor
      · intro hatF
        have hat_Qj : aR t ∈ (Q' j).U := haR_mem t ht
        have hat_uv : aR t ∈ ({u, v} : Set S') := hFU_eq ▸ ⟨hatF, hQj_H'U j hat_Qj⟩
        rcases hat_uv with h1 | h2
        · exact Or.inl (haR_inj ht ht₁_mem h1)
        · exact Or.inr (haR_inj ht ht₂_mem h2)
      · rintro (rfl | rfl)
        · exact ha_t₁_F
        · exact ha_t₂_F
    have hIoo_sub_Δ : aR '' Ioo t₁ t₂ ⊆ Δ := by
      have hIoo_sub : Ioo t₁ t₂ ⊆ Icc 0 1 :=
        Ioo_subset_Icc_self.trans (Icc_subset_Icc ht₁_mem.1 ht₂_mem.2)
      have hconn : IsPreconnected (aR '' Ioo t₁ t₂) :=
        isPreconnected_Ioo.image aR haR_cont.continuousOn
      have hdis : Disjoint (aR '' Ioo t₁ t₂) (frontier Δ) := by
        rw [hΔ_fr]
        refine Set.disjoint_left.mpr ?_
        rintro _ ⟨t, ht, rfl⟩ htF
        rcases (ha_F_iff t (hIoo_sub ht)).mp htF with rfl | rfl
        · exact ht.1.ne rfl
        · exact ht.2.ne rfl
      exact GM14.subset_of_disjoint_frontier hconn hΔ_disc.isClosed hdis
        ⟨t₀.1, ⟨ht₁_lt, ht₂_gt⟩, rfl⟩ (haR_t₀.symm ▸ hz₀_Δ)
    have hIcc_sub_Δ : aR '' Icc t₁ t₂ ⊆ Δ := by
      rintro _ ⟨t, ht, rfl⟩
      rcases eq_or_lt_of_le ht.1 with rfl | hgt1
      · exact hF_sub_Δ ha_t₁_F
      · rcases eq_or_lt_of_le ht.2 with rfl | hlt2
        · exact hF_sub_Δ ha_t₂_F
        · exact hIoo_sub_Δ ⟨t, ⟨hgt1, hlt2⟩, rfl⟩
    have ha_Δ_iff : ∀ t ∈ Icc (0 : ℝ) 1, aR t ∈ Δ ↔ t ∈ Icc t₁ t₂ := by
      exact gluing_arc_meets_subdisc_in_closed_interval (S' := S') (D := D) (ι := ι) (u' := u')
        (v' := v') (F := F) Δ hΔ_disc hΔ_disj_bd hΔ_fr j huj_bd hvj_bd aR haR_cont haR_0 haR_1 t₁
        t₂ ht₁₂ ha_F_iff hIcc_sub_Δ
    have hdisj_other : ∀ k : ι, k ≠ j → Disjoint (Q' k).U Δ := by
      exact other_gluing_arcs_avoid_subdisc (S' := S') (H' := H') (D := D) (ι := ι) (u' := u')
        (v' := v') (Q' := Q') hQ'_line hQ'_bd hQ'_disj (F := F) Δ hΔ_disc hΔ_disj_bd hΔ_fr j
        hQj_H'U huj_bd u v hu_Qj hv_Qj hFU_eq
    have hU_eq_pieceA : (H'.interSet Δ).U = range (pieceA a t₁ t₂) := by
      rw [hΔ_inter_U, range_pieceA a ht₁_mem.1 ht₁₂.le ht₂_mem.2]
      ext x
      constructor
      · rintro ⟨hxU, hxΔ⟩
        rcases hD_U ⟨hΔ_sub_D hxΔ, hxU⟩ with hxB | hxQ
        · have hxF : x ∈ F := by
            by_contra hnot
            exact Set.disjoint_left.mp hΔ_disj_bd ⟨hxΔ, hnot⟩ (hB_bd hxB)
          have hx_uv : x ∈ ({u, v} : Set S') := hFU_eq ▸ ⟨hxF, hxU⟩
          rcases hx_uv with rfl | rfl
          · exact ⟨t₁, ⟨le_rfl, ht₁₂.le⟩, rfl⟩
          · exact ⟨t₂, ⟨ht₁₂.le, le_rfl⟩, rfl⟩
        · obtain ⟨k, hxk⟩ := mem_iUnion.mp hxQ
          by_cases hkj : k = j
          · subst hkj
            obtain ⟨t, rfl⟩ : x ∈ range a := ha_range ▸ hxk
            have ht_Icc : t.1 ∈ Icc (0 : ℝ) 1 := t.2
            have haR_t : aR t.1 = a t := extI_coe a t
            exact ⟨t.1, (ha_Δ_iff t.1 ht_Icc).mp (haR_t.symm ▸ hxΔ), haR_t⟩
          · exact (Set.disjoint_left.mp (hdisj_other k hkj) hxk hxΔ).elim
      · rintro ⟨t, ht, rfl⟩
        have ht_mem : t ∈ Icc (0 : ℝ) 1 := ⟨ht₁_mem.1.trans ht.1, ht.2.trans ht₂_mem.2⟩
        exact ⟨hQj_H'U j (haR_mem t ht_mem), hIcc_sub_Δ ⟨t, ht, rfl⟩⟩
    have hLine_U : IsLineWithEnds (H'.interSet Δ).U u v := by
      rw [hU_eq_pieceA]
      have h := (isArcMap_pieceA ha ht₁_mem.1 ht₁₂ ht₂_mem.2).isLineWithEnds
      rwa [pieceA_zero, pieceA_one] at h
    have hu_interV : u ∈ (H'.interSet Δ).V := by
      rw [interSet_V_of_isClosed H' hΔ_disc.isClosed]
      exact ⟨hu_FV.2, hF_sub_Δ hu_FV.1⟩
    have hv_interV : v ∈ (H'.interSet Δ).V := by
      rw [interSet_V_of_isClosed H' hΔ_disc.isClosed]
      exact ⟨hv_FV.2, hF_sub_Δ hv_FV.1⟩
    exact ⟨u, v, huv, hFV_eq,
      GM16.drawing_isPathBetween_of_isLine_U hLine_U huv hu_interV hv_interV⟩
  · left
    rw [not_nonempty_iff_eq_empty] at hne
    intro x ⟨hxΔ, hxU⟩
    by_contra hx_not_F
    exact Set.eq_empty_iff_forall_notMem.mp hne x ⟨⟨hxΔ, hx_not_F⟩, hxU⟩

/-- Verification of condition (iii) of (3.2) inside a closed disc `D ⊆ S'` where `D ∩ H'.U` is
contained in `B_bd ∪ ⋃ j, (Q' j).U` with `B_bd ⊆ discBd D`. -/
theorem dial_of_oArc_in_striped_disc
    (hS' : IsClosedSurface S')
    {H' : Drawing S'} {D B_bd : Set S'} {m' : ℕ}
    {u' v' : Fin m' → S'} {Q' : Fin m' → Drawing S'}
    (hD : IsClosedDisc D)
    (hB_bd : B_bd ⊆ discBd D)
    (hD_U : D ∩ H'.U ⊆ B_bd ∪ ⋃ j : Fin m', (Q' j).U)
    (_hQ'_D : ∀ j, (Q' j).U ⊆ D)
    (hQ'_line : ∀ j, IsLineWithEnds (Q' j).U (u' j) (v' j))
    (hQ'_sub : ∀ j, (Q' j).IsSubdrawing H')
    (hQ'_bd : ∀ j, (Q' j).U ∩ discBd D = {u' j, v' j})
    (hQ'_disj : Pairwise (fun i j => Disjoint (Q' i).U (Q' j).U))
    {F : Set S'}
    (hFD : F ⊆ D) (hF : IsOArc F) (hFU : F ∩ H'.U ⊆ H'.V) (hFV : (F ∩ H'.V).ncard ≤ 2) :
    ∃ Δ : Set S', Δ ⊆ D ∧ IsDial H' F Δ :=
  dial_of_oArc_in_striped_disc_family hS' hD hB_bd hD_U hQ'_line hQ'_sub hQ'_bd hQ'_disj
    hFD hF hFU hFV

/-- A striped disc built by omitting one line retains the dial conclusion for the
remaining paths. -/
theorem dial_of_oArc_in_remaining_stripes
    (hS' : IsClosedSurface S')
    {H' : Drawing S'} {D B_bd : Set S'} {m : ℕ} {omitted : Fin m}
    {u v : Fin m → S'} {Q : Fin m → Drawing S'} {L : Fin m → Set S'}
    (hD : IsClosedDisc D) (hB : B_bd ⊆ discBd D)
    (hcover : D ∩ H'.U ⊆ B_bd ∪ ⋃ j : {i : Fin m // i ≠ omitted}, (Q j.1).U)
    (hpaths : ∀ i, (Q i).U = L i ∧ (Q i).IsSubdrawing H')
    (hline : ∀ i, IsLineWithEnds (L i) (u i) (v i))
    (hends : ∀ j : {i : Fin m // i ≠ omitted}, (Q j.1).U ∩ discBd D = {u j.1, v j.1})
    (hdisjoint : Pairwise fun i j => Disjoint (L i) (L j))
    {F : Set S'} (hFD : F ⊆ D) (hF : IsOArc F)
    (hFU : F ∩ H'.U ⊆ H'.V) (hFV : (F ∩ H'.V).ncard ≤ 2) :
    ∃ Δ : Set S', Δ ⊆ D ∧ IsDial H' F Δ := by
  refine dial_of_oArc_in_striped_disc_family hS' hD hB hcover
    (fun j => (hpaths j.1).1 ▸ hline j.1) (fun j => (hpaths j.1).2) hends ?_ hFD hF hFU hFV
  intro j k hjk
  rw [(hpaths j.1).1, (hpaths k.1).1]
  exact hdisjoint (fun heq => hjk (Subtype.ext heq))

end StripedDisc

end GraphMinor.GM15
