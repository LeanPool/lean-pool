/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.MoveOff
public import LeanPool.GraphMinor.GM07.CylinderCap
public import LeanPool.GraphMinor.GM12.Section3SubspaceDrawing
public import LeanPool.GraphMinor.GM12.Section3PuncturedBoundary
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs
import LeanPool.GraphMinor.GM12.Section4DiscMatch

/-!
# Moving a digraph off a disc and lifting to a punctured surface

This file provides the surface-digraph transport lemmas used in Graph Minors VII,
Section 9, (9.3)–(9.5) (pages 244–246):

- `exists_move_drawing_off_disc`: for any drawing `H` on a connected surface `S` and any closed
  disc `B ⊆ S` disjoint from `bd S`, there is a homeomorphism `β : S ≃ₜ S` fixing `bd S`
  pointwise such that `Disjoint (β '' H.U) B`.
- `embedDrawing`: the image of a drawing `G` under a closed embedding `f : S → T`, matching `G`
  via `IsMatched`.
- `liftSurfaceDigraph`: lifts a `SurfaceDigraph S` along a closed embedding `f : S → T` into a
  subspace `C ⊆ T` containing `f '' H.G.U`, with underlying drawing
  `GM12.drawingInSubspace (embedDrawing hf H.G) C hUC`.
- `isBoundaryRootedMinor_of_lift`: transfers `IsBoundaryRootedMinor` from the lifted surface
  digraphs on `C` back to `S`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM12

universe u v

/-- Every edge closure in a drawing is a union of at most two lines. -/
theorem edge_closure_subset_lines {S : Type u} [TopologicalSpace S] [T2Space S] (H : Drawing S) :
    ∃ 𝓛 : Set (Set S), 𝓛.Finite ∧
      (∀ L ∈ 𝓛, ∃ a b, IsLineWithEnds L a b) ∧
      (⋃ e ∈ H.E, closure e) = ⋃₀ 𝓛 := by
  classical
  have hpiece : ∀ e ∈ H.E, ∃ P : Set (Set S), P.Finite ∧
      (∀ L ∈ P, ∃ a b, IsLineWithEnds L a b) ∧ closure e = ⋃₀ P := by
    intro e he
    rcases H.edge_cond e he with ⟨u, v, _, _, hL⟩ | ⟨_, _, hO⟩
    · refine ⟨{closure e}, finite_singleton _, ?_, (sUnion_singleton _).symm⟩
      rintro L rfl
      exact ⟨u, v, hL⟩
    · obtain ⟨φ⟩ := id hO
      have hne : (φ 1).1 ≠ (φ (-1)).1 := fun h => by
        have h1 := φ.injective (Subtype.ext h)
        have h2 := congrArg (fun z : Circle => (z : ℂ)) h1
        norm_num at h2
      obtain ⟨A, B, hA, hB, hu, -⟩ := hO.lines (φ 1).2 (φ (-1)).2 hne
      refine ⟨{A, B}, (finite_singleton B).insert A, ?_, ?_⟩
      · rintro L (rfl | rfl)
        · exact ⟨_, _, hA⟩
        · exact ⟨_, _, hB⟩
      · rw [sUnion_insert, sUnion_singleton, hu]
  choose! P hPfin hPline hPeq using hpiece
  refine ⟨⋃ e ∈ H.E, P e, H.finite_edges.biUnion fun e he => hPfin e he, ?_, ?_⟩
  · rintro L hL
    obtain ⟨e, he, hLP⟩ := mem_iUnion₂.mp hL
    exact hPline e he L hLP
  · ext x
    simp only [mem_iUnion, mem_sUnion, exists_prop]
    constructor
    · rintro ⟨e, he, hxe⟩
      rw [hPeq e he, mem_sUnion] at hxe
      obtain ⟨L, hLP, hxL⟩ := hxe
      exact ⟨L, ⟨e, he, hLP⟩, hxL⟩
    · rintro ⟨L, ⟨e, he, hLP⟩, hxL⟩
      refine ⟨e, he, ?_⟩
      rw [hPeq e he, mem_sUnion]
      exact ⟨L, hLP, hxL⟩

/-- In any closed disc `B` in the interior of a surface `S`, there is a closed disc `A ⊆ discInt B`
disjoint from `H.U`. -/
theorem exists_subdisc_disjoint_drawing {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) [ConnectedSpace S] (H : Drawing S)
    {B : Set S} (hB : IsClosedDisc B) (hoff : B ∩ bd S = ∅) :
    ∃ A : Set S, IsClosedDisc A ∧ A ⊆ discInt B ∧ Disjoint A H.U := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hman := hS.2.2
  have hBint : ∀ x ∈ B, IsInteriorPoint x := fun x hx => by
    by_contra hn
    have h1 : x ∈ B ∩ bd S := ⟨hx, hn⟩
    rw [hoff] at h1
    exact h1
  obtain ⟨𝓛, hfin, hlines, hUeq⟩ := edge_closure_subset_lines H
  obtain ⟨p, hp, hpoff⟩ := exists_mem_discInt_off hS hB hfin hlines
  have hUclosed : IsClosed (⋃ e ∈ H.E, closure e) :=
    H.finite_edges.isClosed_biUnion fun _ _ => isClosed_closure
  have hp_not_edges : p ∉ ⋃ e ∈ H.E, closure e := by rwa [hUeq]
  have hOpen := (hB.isOpen_discInt hman).inter hUclosed.isOpen_compl
  obtain ⟨D₀, hD₀, hpD₀, hD₀s⟩ := exists_disc_in_open (hBint p hp.1) hOpen ⟨hp, hp_not_edges⟩
  obtain ⟨q, hq, hqV⟩ : ∃ q ∈ discBd D₀, q ∉ H.V := by
    by_contra hn
    have hsub : discBd D₀ ⊆ H.V := fun x hx => by
      by_contra hxV
      exact hn ⟨x, hx, hxV⟩
    exact (infinite_of_isOArc hD₀.isOArc_discBd) (H.finite_V.subset hsub)
  have hqO := hD₀s (Surface.discBd_subset _ hq)
  have hqU : q ∉ H.U := fun hU => by
    rw [H.U_eq] at hU
    rcases hU with hV | hE_mem
    · exact hqV hV
    · exact hqO.2 hE_mem
  obtain ⟨A, hA, _, hAs⟩ := exists_disc_in_open (hBint q hqO.1.1)
    ((hB.isOpen_discInt hman).inter H.isClosed_U.isOpen_compl) ⟨hqO.1, hqU⟩
  exact ⟨A, hA, fun x hx => (hAs hx).1, disjoint_left.mpr fun x hx hxU => (hAs hx).2 hxU⟩

/-- Graph Minors VII, proof of (9.3) (page 244):
"Moreover, by replacing $(H, H^+, H^-)$ by an isomorphic copy (under an isomorphism which fixes all
elements of $V(H) \cap \mathrm{bd}(\Sigma)$) we may arrange that $U(H) \cap \Delta = \emptyset$, so
that $(H, H^+, H^-)$ is also a proper digraph in $\Sigma'$."
For any drawing `H` on a connected surface `S` and any closed disc `B ⊆ S` with `B ∩ bd S = ∅`,
there is a homeomorphism `β : S ≃ₜ S` fixing `bd S` pointwise such that
`Disjoint (β '' H.U) B`. -/
theorem exists_move_drawing_off_disc {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) [ConnectedSpace S] (H : Drawing S)
    {B : Set S} (hB : IsClosedDisc B) (hoff : B ∩ bd S = ∅) :
    ∃ β : S ≃ₜ S, (∀ x ∈ bd S, β x = x) ∧ Disjoint (β '' H.U) B := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hman := hS.2.2
  have hBint : ∀ x ∈ B, IsInteriorPoint x := fun x hx => by
    by_contra hn
    have h1 : x ∈ B ∩ bd S := ⟨hx, hn⟩
    rw [hoff] at h1
    exact h1
  obtain ⟨E, hE, hBE, hEs⟩ := exists_disc_around hman hB
    (fun x hx => hBint x (Surface.discBd_subset _ hx))
    (isClosed_bd S).isOpen_compl
    (fun x hx hb => by
      have h1 : x ∈ B ∩ bd S := ⟨Surface.discBd_subset _ hx, hb⟩
      rw [hoff] at h1
      exact h1)
  have hEoff : ∀ x ∈ bd S, x ∉ E := fun x hx hxE => by
    rcases hEs hxE with h1 | h1
    · have h2 : x ∈ B ∩ bd S := ⟨h1, hx⟩
      rw [hoff] at h2
      exact h2
    · exact h1 hx
  obtain ⟨A, hA, hAB, hdisj⟩ := exists_subdisc_disjoint_drawing hS H hB hoff
  obtain ⟨e, he, hfix⟩ := GraphMinor.GM12.exists_disc_onto_nested hman hA hB hE hAB hBE
  refine ⟨e, fun x hx => hfix x (hEoff x hx), ?_⟩
  rw [disjoint_left]
  rintro _ ⟨x, hxU, rfl⟩ hxB
  rw [← he] at hxB
  obtain ⟨y, hy, hyx⟩ := hxB
  rw [e.injective hyx] at hy
  exact disjoint_left.mp hdisj hy hxU

/-- Concrete image drawing under a closed embedding `f : S → T`. -/
noncomputable def embedDrawing {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) (G : Drawing S) : Drawing T where
  U := f '' G.U
  V := f '' G.V
  V_subset_U := image_mono G.V_subset_U
  isClosed_U := hf.isClosedMap _ G.isClosed_U
  finite_V := G.finite_V.image _
  finite_edges := by
    by_cases hne : Nonempty S
    · have hset : f '' G.U \ f '' G.V = f '' (G.U \ G.V) :=
        (image_sdiff hf.injective _ _).symm
      have harc : arcComponentsIn (f '' (G.U \ G.V)) = image f '' arcComponentsIn (G.U \ G.V) := by
        refine arcComponentsIn_image (g := invFun f) hf.continuous.continuousOn ?_
          fun x _ => leftInverse_invFun hf.injective x
        rw [hf.isInducing.continuousOn_iff]
        refine continuousOn_id.congr ?_
        rintro _ ⟨x, -, rfl⟩
        simp [leftInverse_invFun hf.injective x]
      rw [hset, harc]
      exact G.finite_edges.image _
    · rw [not_nonempty_iff] at hne
      have : f '' G.U \ f '' G.V = ∅ := eq_empty_of_forall_notMem fun _ ⟨⟨x, _, _⟩, _⟩
        => hne.false x
      rw [this]
      exact finite_empty.subset fun C hC => by
        obtain ⟨x, hx⟩ := hC.1
        exact False.elim (hC.2.1 hx)
  edge_cond := by
    by_cases hne : Nonempty S
    · have hset : f '' G.U \ f '' G.V = f '' (G.U \ G.V) :=
        (image_sdiff hf.injective _ _).symm
      have harc : arcComponentsIn (f '' (G.U \ G.V)) = image f '' arcComponentsIn (G.U \ G.V) := by
        refine arcComponentsIn_image (g := invFun f) hf.continuous.continuousOn ?_
          fun x _ => leftInverse_invFun hf.injective x
        rw [hf.isInducing.continuousOn_iff]
        refine continuousOn_id.congr ?_
        rintro _ ⟨x, -, rfl⟩
        simp [leftInverse_invFun hf.injective x]
      have hcl : ∀ e : Set S, closure (f '' e) = f '' closure e := fun e =>
        (image_closure_subset_closure_image hf.continuous).antisymm'
          (closure_minimal (image_mono subset_closure) (hf.isClosedMap _ isClosed_closure))
      have hcap : ∀ e : Set S, closure (f '' e) ∩ f '' G.V = f '' (closure e ∩ G.V) := fun e => by
        rw [hcl, image_inter hf.injective]
      rw [hset, harc]
      rintro _ ⟨e, he, rfl⟩
      rcases G.edge_cond e he with ⟨u, v, h1, h2, h3⟩ | ⟨u, h2, h3⟩
      · refine .inl ⟨f u, f v, hf.injective.ne h1, by rw [hcap, h2, image_pair], ?_⟩
        rw [hcl]
        exact image_line hf.isEmbedding h3
      · refine .inr ⟨f u, by rw [hcap, h2, image_singleton], ?_⟩
        rw [hcl]
        exact h3.elim fun φ => ⟨φ.trans (hf.isEmbedding.homeomorphImage _)⟩
    · rw [not_nonempty_iff] at hne
      rintro C ⟨⟨w, hw⟩, hC, -⟩
      obtain ⟨⟨x, _, _⟩, _⟩ := hC hw
      exact (hne.false x).elim

@[simp]
theorem embedDrawing_U {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) (G : Drawing S) :
    (embedDrawing hf G).U = f '' G.U := rfl

@[simp]
theorem embedDrawing_V {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) (G : Drawing S) :
    (embedDrawing hf G).V = f '' G.V := rfl

theorem embedDrawing_E {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T] [Nonempty S]
    {f : S → T} (hf : IsClosedEmbedding f) (G : Drawing S) :
    (embedDrawing hf G).E = image f '' G.E := by
  have hset : f '' G.U \ f '' G.V = f '' (G.U \ G.V) :=
    (image_sdiff hf.injective _ _).symm
  have harc : arcComponentsIn (f '' (G.U \ G.V)) = image f '' arcComponentsIn (G.U \ G.V) := by
    refine arcComponentsIn_image (g := invFun f) hf.continuous.continuousOn ?_
      fun x _ => leftInverse_invFun hf.injective x
    rw [hf.isInducing.continuousOn_iff]
    refine continuousOn_id.congr ?_
    rintro _ ⟨x, -, rfl⟩
    simp [leftInverse_invFun hf.injective x]
  change arcComponentsIn (f '' G.U \ f '' G.V) = _
  rw [hset, harc]
  rfl

theorem embedDrawing_isMatched {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T] [Nonempty S]
    {f : S → T} (hf : IsClosedEmbedding f) (G : Drawing S) :
    IsMatched G (embedDrawing hf G) f ∅ :=
  ⟨hf.continuous, hf.injective.injOn, empty_subset _, fun _ _ => disjoint_empty _,
    by simp, by simp, embedDrawing_E hf G⟩

/-- Lifts a subset `s ⊆ S` into a subspace `C ⊆ T` along `f : S → T`. -/
def liftEdge {S : Type u} {T : Type v} (f : S → T) (C : Set T) (s : Set S) : Set C :=
  (Subtype.val : C → T) ⁻¹' (f '' s)

/-- Unlifts a subset `s' ⊆ C` back to `S` along `f : S → T`. -/
def unliftEdge {S : Type u} {T : Type v} (f : S → T) (C : Set T) (s' : Set C) : Set S :=
  f ⁻¹' ((Subtype.val : C → T) '' s')

/-- Lifts a point `x ∈ G.U` into `C` along `f : S → T`. -/
def liftPt {S : Type u} {T : Type v} [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) {G : Drawing S} {C : Set T}
    (hUC : (embedDrawing hf G).U ⊆ C) (x : S) (hx : x ∈ G.U) : C :=
  ⟨f x, hUC ⟨x, hx, rfl⟩⟩

@[simp]
theorem liftPt_val {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) {G : Drawing S} {C : Set T}
    (hUC : (embedDrawing hf G).U ⊆ C) (x : S) (hx : x ∈ G.U) :
    (liftPt hf hUC x hx).val = f x := rfl

theorem liftPt_inj {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) {G : Drawing S} {C : Set T}
    (hUC : (embedDrawing hf G).U ⊆ C) {x y : S} (hx : x ∈ G.U) (hy : y ∈ G.U) :
    liftPt hf hUC x hx = liftPt hf hUC y hy ↔ x = y := by
  simp [liftPt, Subtype.ext_iff, hf.injective.eq_iff]

theorem subtype_image_liftEdge {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) {G : Drawing S} {C : Set T}
    (hUC : (embedDrawing hf G).U ⊆ C) {s : Set S} (hs : s ⊆ G.U) :
    (Subtype.val : C → T) '' liftEdge f C s = f '' s := by
  rw [liftEdge, Subtype.image_preimage_coe, inter_eq_right.mpr ((image_mono hs).trans hUC)]

theorem unliftEdge_liftEdge {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) {G : Drawing S} {C : Set T}
    (hUC : (embedDrawing hf G).U ⊆ C) {s : Set S} (hs : s ⊆ G.U) :
    unliftEdge f C (liftEdge f C s) = s := by
  rw [unliftEdge, subtype_image_liftEdge hf hUC hs, preimage_image_eq _ hf.injective]

theorem liftEdge_inj {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) {G : Drawing S} {C : Set T}
    (hUC : (embedDrawing hf G).U ⊆ C) {s₁ s₂ : Set S} (hs₁ : s₁ ⊆ G.U) (hs₂ : s₂ ⊆ G.U) :
    liftEdge f C s₁ = liftEdge f C s₂ ↔ s₁ = s₂ := by
  constructor
  · intro h
    rw [← unliftEdge_liftEdge hf hUC hs₁, ← unliftEdge_liftEdge hf hUC hs₂, h]
  · rintro rfl
    rfl

theorem closure_liftEdge {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) {G : Drawing S} {C : Set T}
    (hUC : (embedDrawing hf G).U ⊆ C) {s : Set S} (hs : s ⊆ G.U) :
    closure (liftEdge f C s) = liftEdge f C (closure s) := by
  have hsC : f '' s ⊆ C := (image_mono hs).trans hUC
  have hcl : closure (f '' s) = f '' closure s :=
    (image_closure_subset_closure_image hf.continuous).antisymm'
      (closure_minimal (image_mono subset_closure) (hf.isClosedMap _ isClosed_closure))
  rw [liftEdge, closure_subtype_preimage hsC, hcl, liftEdge]

theorem liftEdge_inter {S : Type u} {T : Type v}
    {f : S → T} (hf : Injective f) (C : Set T) (s₁ s₂ : Set S) :
    liftEdge f C (s₁ ∩ s₂) = liftEdge f C s₁ ∩ liftEdge f C s₂ := by
  rw [liftEdge, image_inter hf, preimage_inter, ← liftEdge, ← liftEdge]

theorem liftEdge_sdiff {S : Type u} {T : Type v}
    {f : S → T} (hf : Injective f) (C : Set T) (s₁ s₂ : Set S) :
    liftEdge f C (s₁ \ s₂) = liftEdge f C s₁ \ liftEdge f C s₂ := by
  rw [liftEdge, image_sdiff hf, preimage_sdiff, ← liftEdge, ← liftEdge]

theorem liftPt_mem_liftEdge {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) {G : Drawing S} {C : Set T}
    (hUC : (embedDrawing hf G).U ⊆ C) {x : S} (hx : x ∈ G.U) (s : Set S) :
    liftPt hf hUC x hx ∈ liftEdge f C s ↔ x ∈ s := by
  simp [liftEdge, liftPt, hf.injective.eq_iff]

theorem liftEdge_singleton {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) {G : Drawing S} {C : Set T}
    (hUC : (embedDrawing hf G).U ⊆ C) {x : S} (hx : x ∈ G.U) :
    liftEdge f C {x} = {liftPt hf hUC x hx} := by
  ext y
  simp [liftEdge, Subtype.ext_iff]

theorem liftEdge_pair {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) {G : Drawing S} {C : Set T}
    (hUC : (embedDrawing hf G).U ⊆ C) {x y : S} (hx : x ∈ G.U) (hy : y ∈ G.U) :
    liftEdge f C {x, y} = {liftPt hf hUC x hx, liftPt hf hUC y hy} := by
  ext z
  simp [liftEdge, Subtype.ext_iff]

theorem drawingInSubspace_embedDrawing_U {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) (G : Drawing S) (C : Set T)
    (hUC : (embedDrawing hf G).U ⊆ C) :
    (drawingInSubspace (embedDrawing hf G) C hUC).U = liftEdge f C G.U := by
  rw [drawingInSubspace_U, embedDrawing_U]
  rfl

theorem drawingInSubspace_embedDrawing_V {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) (G : Drawing S) (C : Set T)
    (hUC : (embedDrawing hf G).U ⊆ C) :
    (drawingInSubspace (embedDrawing hf G) C hUC).V = liftEdge f C G.V := by
  rw [drawingInSubspace_V, embedDrawing_V]
  rfl

theorem drawingInSubspace_embedDrawing_E {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T] [Nonempty S]
    {f : S → T} (hf : IsClosedEmbedding f) (G : Drawing S) (C : Set T)
    (hUC : (embedDrawing hf G).U ⊆ C) :
    (drawingInSubspace (embedDrawing hf G) C hUC).E = liftEdge f C '' G.E := by
  rw [drawingInSubspace_E, embedDrawing_E, image_image]
  rfl

theorem drawingInSubspace_embedDrawing_V_eq_image {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) (G : Drawing S) (C : Set T)
    (hUC : (embedDrawing hf G).U ⊆ C) :
    (Subtype.val : C → T) '' (drawingInSubspace (embedDrawing hf G) C hUC).V = f '' G.V := by
  rw [drawingInSubspace_embedDrawing_V]
  exact subtype_image_liftEdge hf hUC G.V_subset_U

theorem drawingInSubspace_embedDrawing_V_ncard {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) (G : Drawing S) (C : Set T)
    (hUC : (embedDrawing hf G).U ⊆ C) :
    (drawingInSubspace (embedDrawing hf G) C hUC).V.ncard = G.V.ncard := by
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective,
    drawingInSubspace_embedDrawing_V_eq_image, Set.ncard_image_of_injective _ hf.injective]

theorem drawingInSubspace_embedDrawing_E_ncard {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T] [Nonempty S]
    {f : S → T} (hf : IsClosedEmbedding f) (G : Drawing S) (C : Set T)
    (hUC : (embedDrawing hf G).U ⊆ C) :
    (drawingInSubspace (embedDrawing hf G) C hUC).E.ncard = G.E.ncard := by
  rw [drawingInSubspace_embedDrawing_E]
  refine Set.InjOn.ncard_image fun e₁ he₁ e₂ he₂ h => ?_
  exact (liftEdge_inj hf hUC ((subset_closure.trans (G.closure_subset_U he₁)))
    ((subset_closure.trans (G.closure_subset_U he₂)))).mp h

/-- Head function for `liftSurfaceDigraph`. -/
noncomputable def liftPlus {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) (D : SurfaceDigraph S) (C : Set T) [Nonempty C]
    (hUC : (embedDrawing hf D.G).U ⊆ C) (e' : Set C) : C :=
  letI := Classical.dec
  if he : unliftEdge f C e' ∈ D.G.E then
    liftPt hf hUC (D.plus (unliftEdge f C e')) (D.G.V_subset_U (D.plus_mem _ he))
  else Classical.arbitrary C

/-- Tail function for `liftSurfaceDigraph`. -/
noncomputable def liftMinus {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) (D : SurfaceDigraph S) (C : Set T) [Nonempty C]
    (hUC : (embedDrawing hf D.G).U ⊆ C) (e' : Set C) : C :=
  letI := Classical.dec
  if he : unliftEdge f C e' ∈ D.G.E then
    liftPt hf hUC (D.minus (unliftEdge f C e')) (D.G.V_subset_U (D.minus_mem _ he))
  else Classical.arbitrary C

theorem liftPlus_eq {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) (D : SurfaceDigraph S) (C : Set T) [Nonempty C]
    (hUC : (embedDrawing hf D.G).U ⊆ C) {e' : Set C} {e : Set S}
    (hun : unliftEdge f C e' = e) (he : e ∈ D.G.E) :
    liftPlus hf D C hUC e' = liftPt hf hUC (D.plus e) (D.G.V_subset_U (D.plus_mem e he)) := by
  subst hun
  simp [liftPlus, he]

theorem liftMinus_eq {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) (D : SurfaceDigraph S) (C : Set T) [Nonempty C]
    (hUC : (embedDrawing hf D.G).U ⊆ C) {e' : Set C} {e : Set S}
    (hun : unliftEdge f C e' = e) (he : e ∈ D.G.E) :
    liftMinus hf D C hUC e' = liftPt hf hUC (D.minus e) (D.G.V_subset_U (D.minus_mem e he)) := by
  subst hun
  simp [liftMinus, he]

/-- Lifts a `SurfaceDigraph S` along a closed embedding `f : S → T` into a subspace `C ⊆ T`
containing `f '' D.G.U`, with underlying drawing
`GM12.drawingInSubspace (embedDrawing hf D.G) C hUC`. -/
noncomputable def liftSurfaceDigraph {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T] [Nonempty S]
    {f : S → T} (hf : IsClosedEmbedding f) (D : SurfaceDigraph S) (C : Set T) [Nonempty C]
    (hUC : (embedDrawing hf D.G).U ⊆ C) : SurfaceDigraph C where
  G := drawingInSubspace (embedDrawing hf D.G) C hUC
  plus := liftPlus hf D C hUC
  minus := liftMinus hf D C hUC
  plus_mem := by
    rw [drawingInSubspace_embedDrawing_E, drawingInSubspace_embedDrawing_V]
    rintro _ ⟨e, he, rfl⟩
    have heU : e ⊆ D.G.U := subset_closure.trans (D.G.closure_subset_U he)
    rw [liftPlus_eq hf D C hUC (unliftEdge_liftEdge hf hUC heU) he]
    exact (liftPt_mem_liftEdge hf hUC _ _).mpr (D.plus_mem e he)
  minus_mem := by
    rw [drawingInSubspace_embedDrawing_E, drawingInSubspace_embedDrawing_V]
    rintro _ ⟨e, he, rfl⟩
    have heU : e ⊆ D.G.U := subset_closure.trans (D.G.closure_subset_U he)
    rw [liftMinus_eq hf D C hUC (unliftEdge_liftEdge hf hUC heU) he]
    exact (liftPt_mem_liftEdge hf hUC _ _).mpr (D.minus_mem e he)
  ends_eq := by
    rw [drawingInSubspace_embedDrawing_E]
    rintro _ ⟨e, he, rfl⟩
    have heU : e ⊆ D.G.U := subset_closure.trans (D.G.closure_subset_U he)
    have hun := unliftEdge_liftEdge hf hUC heU
    rw [liftPlus_eq hf D C hUC hun he, liftMinus_eq hf D C hUC hun he]
    have htilde : tilde (liftEdge f C e) = liftEdge f C (tilde e) := by
      rw [tilde, tilde, closure_liftEdge hf hUC heU, liftEdge_sdiff hf.injective]
    rw [htilde, ← D.ends_eq e he, liftEdge_pair hf hUC]

/-- Pulling a subdrawing of `drawingInSubspace (embedDrawing hf G) C hUC` back to `G`. -/
theorem exists_pull_from_subspace {S : Type u} {T : Type v}
    [TopologicalSpace S] [T1Space S] [TopologicalSpace T] [Nonempty S]
    {f : S → T} (hf : IsClosedEmbedding f) {G : Drawing S} {C : Set T}
    (hUC : (embedDrawing hf G).U ⊆ C) {D' : Drawing C}
    (hD' : D'.IsSubdrawing (drawingInSubspace (embedDrawing hf G) C hUC)) :
    ∃ D : Drawing S, D.IsSubdrawing G ∧
      liftEdge f C D.V = D'.V ∧ liftEdge f C '' D.E = D'.E ∧
      (D'.V.Nonempty → D.V.Nonempty) ∧ (D'.IsConnected → D.IsConnected) := by
  classical
  let G' := drawingInSubspace (embedDrawing hf G) C hUC
  let D := G.span (unliftEdge f C D'.V) {e | liftEdge f C e ∈ D'.E}
  have hDE : D.E = {e ∈ G.E | liftEdge f C e ∈ D'.E} := by
    rw [G.span_E]
    exact inter_comm _ _
  have hDV : D.V = unliftEdge f C D'.V ∩ G.V := by
    rw [G.span_V, Drawing.spanV]
    refine subset_antisymm ?_ (fun x hx => Or.inl hx)
    rintro x (hx | hx)
    · exact hx
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      have heD : e ∈ D.E := by rw [hDE]; exact ⟨he.2, he.1⟩
      have heU : e ⊆ G.U := subset_closure.trans (G.closure_subset_U he.2)
      have hxU : x ∈ G.U := G.V_subset_U hxe.2
      have hmem : liftPt hf hUC x hxU ∈ closure (liftEdge f C e) ∩ G'.V := by
        rw [closure_liftEdge hf hUC heU, drawingInSubspace_embedDrawing_V,
          ← liftEdge_inter hf.injective]
        exact (liftPt_mem_liftEdge hf hUC hxU _).mpr hxe
      rw [← hD'.closure_inter_V he.1] at hmem
      exact ⟨⟨liftPt hf hUC x hxU, hmem.2, rfl⟩, hxe.2⟩
  have hIV : liftEdge f C D.V = D'.V := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      rw [hDV] at hx
      obtain ⟨y', hy', hfy⟩ := hx.1
      have hyy' : y = y' := Subtype.ext (hxy.symm.trans hfy.symm)
      rwa [hyy']
    · intro hy
      have hyG' := hD'.1 hy
      rw [drawingInSubspace_embedDrawing_V] at hyG'
      obtain ⟨x, hxV, hxy⟩ := hyG'
      refine ⟨x, ?_, hxy⟩
      rw [hDV]
      exact ⟨⟨y, hy, hxy.symm⟩, hxV⟩
  have hIE : liftEdge f C '' D.E = D'.E := by
    rw [hDE]
    refine subset_antisymm ?_ fun e' he' => ?_
    · rintro _ ⟨e, he, rfl⟩
      exact he.2
    · have heG' := hD'.2 he'
      rw [drawingInSubspace_embedDrawing_E] at heG'
      obtain ⟨e, he, rfl⟩ := heG'
      exact ⟨e, ⟨he, he'⟩, rfl⟩
  have hDV_sub : D.V ⊆ G.U := (G.span_isSubdrawing _ _).1.trans G.V_subset_U
  have hne : D'.V.Nonempty → D.V.Nonempty := by
    rintro ⟨y, hy⟩
    rw [← hIV] at hy
    obtain ⟨x, hx, -⟩ := hy
    exact ⟨x, hx⟩
  refine ⟨D, G.span_isSubdrawing _ _, hIV, hIE, hne, ?_⟩
  rintro ⟨hne', hwalk'⟩
  refine ⟨hne hne', fun x hx y hy => ?_⟩
  have hx' : liftPt hf hUC x (hDV_sub hx) ∈ D'.V := by
    rw [← hIV]
    exact (liftPt_mem_liftEdge hf hUC (hDV_sub hx) _).mpr hx
  have hy' : liftPt hf hUC y (hDV_sub hy) ∈ D'.V := by
    rw [← hIV]
    exact (liftPt_mem_liftEdge hf hUC (hDV_sub hy) _).mpr hy
  obtain ⟨W'⟩ := hwalk' _ hx' _ hy'
  have hg : ∀ z : S, invFun f (f z) = z := leftInverse_invFun hf.injective
  have hpull_walk : ∀ {u' v' : C}, GraphWalk D'.toGraph u' v' →
      Nonempty (GraphWalk D.toGraph (invFun f u'.val) (invFun f v'.val)) := by
    intro u' v' W
    induction W with
    | nil hv' =>
      change _ ∈ D'.V at hv'
      rw [← hIV] at hv'
      obtain ⟨u, hu, hfu⟩ := hv'
      rw [← hfu, hg]
      exact ⟨.nil hu⟩
    | @cons a' b' c' e' hlink rest ih =>
      obtain ⟨W_rest⟩ := ih
      obtain ⟨he', ha', hb', hcap'⟩ := hlink
      rw [← hIE] at he'
      obtain ⟨e, he, rfl⟩ := he'
      have heG : e ∈ G.E := (G.span_isSubdrawing _ _).2 he
      have heU : e ⊆ G.U := subset_closure.trans (G.closure_subset_U heG)
      rw [← hIV] at ha' hb'
      obtain ⟨a, ha, hfa⟩ := ha'
      obtain ⟨b, hb, hfb⟩ := hb'
      have haU : a ∈ G.U := hDV_sub ha
      have hbU : b ∈ G.U := hDV_sub hb
      have ha'_eq : a' = liftPt hf hUC a haU := Subtype.ext hfa.symm
      have hb'_eq : b' = liftPt hf hUC b hbU := Subtype.ext hfb.symm
      have hcap : closure e ∩ D.V = {a, b} := by
        apply (liftEdge_inj hf hUC (inter_subset_right.trans hDV_sub) (pair_subset haU hbU)).mp
        rw [liftEdge_inter hf.injective, ← closure_liftEdge hf hUC heU, hIV, hcap',
          ha'_eq, hb'_eq, liftEdge_pair hf hUC haU hbU]
      have hlink_D : D.toGraph.IsLink e (invFun f a'.val) (invFun f b'.val) := by
        change _ ∧ _ ∧ _ ∧ _
        rw [← hfa, ← hfb, hg, hg]
        exact ⟨he, ha, hb, hcap⟩
      exact ⟨.cons hlink_D W_rest⟩
  obtain ⟨W⟩ := hpull_walk W'
  dsimp only [liftPt_val] at W
  rw [hg, hg] at W
  exact ⟨W⟩

/-- Transfers `IsBoundaryRootedMinor` from lifted surface digraphs in `C` back to `S`. -/
theorem isBoundaryRootedMinor_of_lift {S : Type u} {T : Type v}
    [TopologicalSpace S] [T1Space S] [TopologicalSpace T] [Nonempty S]
    {f_H f_G : S → T} (hf_H : IsClosedEmbedding f_H) (hf_G : IsClosedEmbedding f_G)
    (H G : SurfaceDigraph S) (C : Set T) [Nonempty C]
    (hC_H : (embedDrawing hf_H H.G).U ⊆ C) (hC_G : (embedDrawing hf_G G.G).U ⊆ C)
    (hbd_VG : H.G.V ∩ bd S = G.G.V ∩ bd S)
    (hbd_eq : ∀ x ∈ bd S, f_H x = f_G x)
    (hbd_lift : ∀ v (hv : v ∈ H.G.V ∩ bd S),
      liftPt hf_H hC_H v (H.G.V_subset_U hv.1) ∈ bd C)
    (hminor : IsBoundaryRootedMinor
      (liftSurfaceDigraph hf_H H C hC_H) (liftSurfaceDigraph hf_G G C hC_G)) :
    IsBoundaryRootedMinor H G := by
  classical
  let H' := liftSurfaceDigraph hf_H H C hC_H
  let G' := liftSurfaceDigraph hf_G G C hC_G
  obtain ⟨_, φv', φe', hsub', hedge', hdisj', hinj', hnotMem', hends', hbd'⟩ := hminor
  have hpull : ∀ v (hv : v ∈ H.G.V), ∃ D : Drawing S, D.IsSubdrawing G.G ∧
      liftEdge f_G C D.V = (φv' (liftPt hf_H hC_H v (H.G.V_subset_U hv))).V ∧
      liftEdge f_G C '' D.E = (φv' (liftPt hf_H hC_H v (H.G.V_subset_U hv))).E ∧
      D.V.Nonempty ∧ D.IsConnected := by
    intro v hv
    have hv' : liftPt hf_H hC_H v (H.G.V_subset_U hv) ∈ H'.G.V := by
      rw [show H'.G = drawingInSubspace (embedDrawing hf_H H.G) C hC_H from rfl,
        drawingInSubspace_embedDrawing_V]
      exact (liftPt_mem_liftEdge hf_H hC_H _ _).mpr hv
    obtain ⟨h1, h2, h3⟩ := hsub' _ hv'
    obtain ⟨D, hDsub, hDV, hDE, hne, hconn⟩ := exists_pull_from_subspace hf_G hC_G h1
    exact ⟨D, hDsub, hDV, hDE, hne h2, hconn h3⟩
  choose! φv hφv_sub hφv_V hφv_E hφv_ne hφv_conn using hpull
  let φe : Set S → Set S := fun e => unliftEdge f_G C (φe' (liftEdge f_H C e))
  have hφe_lift : ∀ e ∈ H.G.E, φe e ∈ G.G.E ∧ liftEdge f_G C (φe e) = φe' (liftEdge f_H C e) := by
    intro e he
    have he' : liftEdge f_H C e ∈ H'.G.E := by
      rw [show H'.G = drawingInSubspace (embedDrawing hf_H H.G) C hC_H from rfl,
        drawingInSubspace_embedDrawing_E]
      exact ⟨e, he, rfl⟩
    have hmem := hedge' _ he'
    rw [show G'.G = drawingInSubspace (embedDrawing hf_G G.G) C hC_G from rfl,
      drawingInSubspace_embedDrawing_E] at hmem
    obtain ⟨g, hg, hg_eq⟩ := hmem
    have hgU : g ⊆ G.G.U := subset_closure.trans (G.G.closure_subset_U hg)
    have hφe_eq : φe e = g := by
      change unliftEdge f_G C (φe' (liftEdge f_H C e)) = g
      rw [← hg_eq, unliftEdge_liftEdge hf_G hC_G hgU]
    rw [hφe_eq]
    exact ⟨hg, hg_eq⟩
  refine ⟨hbd_VG, φv, φe,
    fun v hv => ⟨hφv_sub v hv, hφv_ne v hv, hφv_conn v hv⟩,
    fun e he => (hφe_lift e he).1, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv v' hv' hne
    rw [disjoint_left]
    intro x hxv hxv'
    have hxU : x ∈ G.G.U := G.G.V_subset_U ((hφv_sub v hv).1 hxv)
    have hx1 : liftPt hf_G hC_G x hxU ∈ (φv' (liftPt hf_H hC_H v (H.G.V_subset_U hv))).V := by
      rw [← hφv_V v hv]
      exact (liftPt_mem_liftEdge hf_G hC_G hxU _).mpr hxv
    have hx2 : liftPt hf_G hC_G x hxU ∈ (φv' (liftPt hf_H hC_H v' (H.G.V_subset_U hv'))).V := by
      rw [← hφv_V v' hv']
      exact (liftPt_mem_liftEdge hf_G hC_G hxU _).mpr hxv'
    have hv_mem : liftPt hf_H hC_H v (H.G.V_subset_U hv) ∈ H'.G.V := by
      rw [show H'.G = drawingInSubspace (embedDrawing hf_H H.G) C hC_H from rfl,
        drawingInSubspace_embedDrawing_V]
      exact (liftPt_mem_liftEdge hf_H hC_H _ _).mpr hv
    have hv'_mem : liftPt hf_H hC_H v' (H.G.V_subset_U hv') ∈ H'.G.V := by
      rw [show H'.G = drawingInSubspace (embedDrawing hf_H H.G) C hC_H from rfl,
        drawingInSubspace_embedDrawing_V]
      exact (liftPt_mem_liftEdge hf_H hC_H _ _).mpr hv'
    have hne' : liftPt hf_H hC_H v (H.G.V_subset_U hv) ≠
        liftPt hf_H hC_H v' (H.G.V_subset_U hv') := by
      rwa [Ne, liftPt_inj hf_H hC_H]
    exact disjoint_left.mp (hdisj' _ hv_mem _ hv'_mem hne') hx1 hx2
  · intro e₁ he₁ e₂ he₂ hne heq
    have he₁' : liftEdge f_H C e₁ ∈ H'.G.E := by
      rw [show H'.G = drawingInSubspace (embedDrawing hf_H H.G) C hC_H from rfl,
        drawingInSubspace_embedDrawing_E]
      exact ⟨e₁, he₁, rfl⟩
    have he₂' : liftEdge f_H C e₂ ∈ H'.G.E := by
      rw [show H'.G = drawingInSubspace (embedDrawing hf_H H.G) C hC_H from rfl,
        drawingInSubspace_embedDrawing_E]
      exact ⟨e₂, he₂, rfl⟩
    have hne' : liftEdge f_H C e₁ ≠ liftEdge f_H C e₂ := by
      rwa [Ne, liftEdge_inj hf_H hC_H (subset_closure.trans (H.G.closure_subset_U he₁))
        (subset_closure.trans (H.G.closure_subset_U he₂))]
    apply hinj' _ he₁' _ he₂' hne'
    rw [← (hφe_lift e₁ he₁).2, ← (hφe_lift e₂ he₂).2, heq]
  · intro v hv e he hmem
    have hv' : liftPt hf_H hC_H v (H.G.V_subset_U hv) ∈ H'.G.V := by
      rw [show H'.G = drawingInSubspace (embedDrawing hf_H H.G) C hC_H from rfl,
        drawingInSubspace_embedDrawing_V]
      exact (liftPt_mem_liftEdge hf_H hC_H _ _).mpr hv
    have he' : liftEdge f_H C e ∈ H'.G.E := by
      rw [show H'.G = drawingInSubspace (embedDrawing hf_H H.G) C hC_H from rfl,
        drawingInSubspace_embedDrawing_E]
      exact ⟨e, he, rfl⟩
    apply hnotMem' _ hv' _ he'
    rw [← (hφe_lift e he).2, ← hφv_E v hv]
    exact ⟨φe e, hmem, rfl⟩
  · intro e he
    have he' : liftEdge f_H C e ∈ H'.G.E := by
      rw [show H'.G = drawingInSubspace (embedDrawing hf_H H.G) C hC_H from rfl,
        drawingInSubspace_embedDrawing_E]
      exact ⟨e, he, rfl⟩
    obtain ⟨hp', hm'⟩ := hends' _ he'
    have heU_H : e ⊆ H.G.U := subset_closure.trans (H.G.closure_subset_U he)
    have hun_H : unliftEdge f_H C (liftEdge f_H C e) = e := unliftEdge_liftEdge hf_H hC_H heU_H
    have hHplus : H'.plus (liftEdge f_H C e) =
        liftPt hf_H hC_H (H.plus e) (H.G.V_subset_U (H.plus_mem e he)) :=
      liftPlus_eq hf_H H C hC_H hun_H he
    have hHminus : H'.minus (liftEdge f_H C e) =
        liftPt hf_H hC_H (H.minus e) (H.G.V_subset_U (H.minus_mem e he)) :=
      liftMinus_eq hf_H H C hC_H hun_H he
    have hφeG := (hφe_lift e he).1
    have hφeU_G : φe e ⊆ G.G.U := subset_closure.trans (G.G.closure_subset_U hφeG)
    have hun_G : unliftEdge f_G C (φe' (liftEdge f_H C e)) = φe e := by
      rw [← (hφe_lift e he).2, unliftEdge_liftEdge hf_G hC_G hφeU_G]
    have hGplus : G'.plus (φe' (liftEdge f_H C e)) =
        liftPt hf_G hC_G (G.plus (φe e)) (G.G.V_subset_U (G.plus_mem _ hφeG)) :=
      liftPlus_eq hf_G G C hC_G hun_G hφeG
    have hGminus : G'.minus (φe' (liftEdge f_H C e)) =
        liftPt hf_G hC_G (G.minus (φe e)) (G.G.V_subset_U (G.minus_mem _ hφeG)) :=
      liftMinus_eq hf_G G C hC_G hun_G hφeG
    rw [hHplus, hGplus, ← hφv_V (H.plus e) (H.plus_mem e he),
      liftPt_mem_liftEdge hf_G hC_G] at hp'
    rw [hHminus, hGminus, ← hφv_V (H.minus e) (H.minus_mem e he),
      liftPt_mem_liftEdge hf_G hC_G] at hm'
    exact ⟨hp', hm'⟩
  · intro v hv
    have hv' : liftPt hf_H hC_H v (H.G.V_subset_U hv.1) ∈ H'.G.V ∩ bd C := by
      refine ⟨?_, hbd_lift v hv⟩
      rw [show H'.G = drawingInSubspace (embedDrawing hf_H H.G) C hC_H from rfl,
        drawingInSubspace_embedDrawing_V]
      exact (liftPt_mem_liftEdge hf_H hC_H _ _).mpr hv.1
    have hmem := hbd' _ hv'
    have hvG : v ∈ G.G.V := (hbd_VG ▸ hv).1
    have hpt_eq : liftPt hf_H hC_H v (H.G.V_subset_U hv.1) =
        liftPt hf_G hC_G v (G.G.V_subset_U hvG) :=
      Subtype.ext (hbd_eq v hv.2)
    rw [← hφv_V v hv.1] at hmem
    rw [hpt_eq, liftPt_mem_liftEdge hf_G hC_G] at hmem
    exact hmem

/-- Arithmetic bound on `numInternalIsolatedVertices` used in the proofs of (9.3)–(9.5). -/
theorem numInternalIsolatedVertices_add_bd_le {X : Type*} [TopologicalSpace X] (Γ : Drawing X) :
    numInternalIsolatedVertices Γ + (Γ.V ∩ bd X).ncard ≤ Γ.V.ncard := by
  have hle : numInternalIsolatedVertices Γ ≤ (Γ.V \ bd X).ncard :=
    Set.ncard_le_ncard (fun _ hx => hx.1) Γ.finite_V.sdiff
  have heq : (Γ.V ∩ bd X).ncard + (Γ.V \ bd X).ncard = Γ.V.ncard :=
    Set.ncard_inter_add_ncard_sdiff_eq_ncard Γ.V (bd X) Γ.finite_V
  omega

/-! ### Transport of arcs, normality, vertex counts, and disjoint paths along `liftEdge` -/

theorem subtype_image_liftEdge_of_subset {S : Type u} {T : Type v}
    {f : S → T} {C : Set T} {s : Set S} (hsC : f '' s ⊆ C) :
    (Subtype.val : C → T) '' liftEdge f C s = f '' s := by
  rw [liftEdge, Subtype.image_preimage_coe, inter_eq_right.mpr hsC]

theorem unliftEdge_liftEdge_of_subset {S : Type u} {T : Type v}
    {f : S → T} (hf : Injective f) {C : Set T} {s : Set S} (hsC : f '' s ⊆ C) :
    unliftEdge f C (liftEdge f C s) = s := by
  rw [unliftEdge, subtype_image_liftEdge_of_subset hsC, preimage_image_eq _ hf]

theorem image_unliftEdge_of_subset {S : Type u} {T : Type v}
    {f : S → T} {C : Set T} {s' : Set C} (hs' : (Subtype.val : C → T) '' s' ⊆ range f) :
    f '' unliftEdge f C s' = (Subtype.val : C → T) '' s' := by
  rw [unliftEdge, image_preimage_eq_inter_range, inter_eq_left.mpr hs']

theorem liftEdge_unliftEdge_of_subset {S : Type u} {T : Type v}
    {f : S → T} {C : Set T} {s' : Set C} (hs' : (Subtype.val : C → T) '' s' ⊆ range f) :
    liftEdge f C (unliftEdge f C s') = s' := by
  rw [liftEdge, image_unliftEdge_of_subset hs', preimage_image_eq _ Subtype.val_injective]

theorem disjoint_liftEdge {S : Type u} {T : Type v}
    {f : S → T} (hf : Injective f) (C : Set T) {s₁ s₂ : Set S} (hd : Disjoint s₁ s₂) :
    Disjoint (liftEdge f C s₁) (liftEdge f C s₂) := by
  rw [disjoint_iff_inter_eq_empty, ← liftEdge_inter hf, hd.inter_eq, liftEdge, image_empty,
    preimage_empty]

theorem nonempty_liftEdge_iff {S : Type u} {T : Type v}
    {f : S → T} {C : Set T} {s : Set S} (hsC : f '' s ⊆ C) :
    (liftEdge f C s).Nonempty ↔ s.Nonempty := by
  constructor
  · rintro ⟨y, x, hx, _⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨f x, hsC ⟨x, hx, rfl⟩⟩, x, hx, rfl⟩

theorem nonempty_unliftEdge_iff {S : Type u} {T : Type v}
    {f : S → T} {C : Set T} {s' : Set C} (hs' : (Subtype.val : C → T) '' s' ⊆ range f) :
    (unliftEdge f C s').Nonempty ↔ s'.Nonempty := by
  constructor
  · rintro ⟨x, y, hy, _⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hs' ⟨y, hy, rfl⟩
    exact ⟨x, y, hy, hx.symm⟩

/-- Homeomorphism between `F : Set S` and `liftEdge f C F : Set C` when `f : S → T` is an embedding
and `f '' F ⊆ C`. -/
noncomputable def liftEdgeHomeomorph {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsEmbedding f) {C : Set T} {F : Set S} (hFC : f '' F ⊆ C) :
    F ≃ₜ liftEdge f C F :=
  (hf.homeomorphImage F).trans
    { toFun := fun x => ⟨⟨x.1, hFC x.2⟩, x.2⟩
      invFun := fun x => ⟨x.1.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }

/-- Homeomorphism between `F' : Set C` and `unliftEdge f C F' : Set S` when `f : S → T` is an
embedding and `(Subtype.val : C → T) '' F' ⊆ range f`. -/
noncomputable def unliftEdgeHomeomorph {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsEmbedding f) {C : Set T} {F' : Set C}
    (hF' : (Subtype.val : C → T) '' F' ⊆ range f) :
    F' ≃ₜ unliftEdge f C F' :=
  let e : F' ≃ₜ f '' unliftEdge f C F' :=
    (IsEmbedding.subtypeVal.homeomorphImage F').trans
      (Homeomorph.setCongr (image_unliftEdge_of_subset hF').symm)
  e.trans (hf.homeomorphImage (unliftEdge f C F')).symm

theorem isOArc_liftEdge {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsEmbedding f) {C : Set T} {F : Set S}
    (hFC : f '' F ⊆ C) (hF : IsOArc F) :
    IsOArc (liftEdge f C F) :=
  hF.elim fun φ => ⟨φ.trans (liftEdgeHomeomorph hf hFC)⟩

theorem isLine_liftEdge {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsEmbedding f) {C : Set T} {F : Set S}
    (hFC : f '' F ⊆ C) (hF : IsLine F) :
    IsLine (liftEdge f C F) :=
  hF.elim fun φ => ⟨φ.trans (liftEdgeHomeomorph hf hFC)⟩

theorem isLine_unliftEdge {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsEmbedding f) {C : Set T} {F' : Set C}
    (hF' : (Subtype.val : C → T) '' F' ⊆ range f) (hL : IsLine F') :
    IsLine (unliftEdge f C F') :=
  hL.elim fun φ => ⟨φ.trans (unliftEdgeHomeomorph hf hF')⟩

theorem isOArc_unliftEdge {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsEmbedding f) {C : Set T} {F' : Set C}
    (hF' : (Subtype.val : C → T) '' F' ⊆ range f) (hO : IsOArc F') :
    IsOArc (unliftEdge f C F') :=
  hO.elim fun φ => ⟨φ.trans (unliftEdgeHomeomorph hf hF')⟩

theorem drawingInSubspace_embedDrawing_isNormal_unliftEdge {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) (G : Drawing S) (C : Set T)
    (hUC : (embedDrawing hf G).U ⊆ C) {F' : Set C}
    (hn : (drawingInSubspace (embedDrawing hf G) C hUC).IsNormal F') :
    G.IsNormal (unliftEdge f C F') := by
  rintro x ⟨⟨y, hyF', hfy⟩, hxU⟩
  have hyU : y ∈ (drawingInSubspace (embedDrawing hf G) C hUC).U := by
    rw [drawingInSubspace_embedDrawing_U]
    exact ⟨x, hxU, hfy.symm⟩
  have hyV := hn ⟨hyF', hyU⟩
  rw [drawingInSubspace_embedDrawing_V] at hyV
  obtain ⟨z, hzV, hfz⟩ := hyV
  rwa [hf.injective (hfy.symm.trans hfz.symm)]

theorem drawingInSubspace_embedDrawing_isNormal_liftEdge {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) (G : Drawing S) (C : Set T)
    (hUC : (embedDrawing hf G).U ⊆ C) {F : Set S}
    (hn : G.IsNormal F) :
    (drawingInSubspace (embedDrawing hf G) C hUC).IsNormal (liftEdge f C F) := by
  rintro y ⟨⟨x, hxF, hfx⟩, hyU⟩
  rw [drawingInSubspace_embedDrawing_U] at hyU
  obtain ⟨z, hzU, hfz⟩ := hyU
  have hxz : x = z := hf.injective (hfx.trans hfz.symm)
  subst hxz
  rw [drawingInSubspace_embedDrawing_V]
  exact ⟨x, hn ⟨hxF, hzU⟩, hfx⟩

theorem drawingInSubspace_embedDrawing_V_inter_unliftEdge_ncard {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) (G : Drawing S) (C : Set T)
    (hUC : (embedDrawing hf G).U ⊆ C) (F' : Set C) :
    ((drawingInSubspace (embedDrawing hf G) C hUC).V ∩ F').ncard =
      (G.V ∩ unliftEdge f C F').ncard := by
  have heq : (Subtype.val : C → T) '' ((drawingInSubspace (embedDrawing hf G) C hUC).V ∩ F') =
      f '' (G.V ∩ unliftEdge f C F') := by
    rw [drawingInSubspace_image_vertices_inter, embedDrawing_V]
    ext z
    constructor
    · rintro ⟨⟨x, hxV, rfl⟩, y, hyF', hfy⟩
      exact ⟨x, ⟨hxV, y, hyF', hfy⟩, rfl⟩
    · rintro ⟨x, ⟨hxV, y, hyF', hfy⟩, rfl⟩
      exact ⟨⟨x, hxV, rfl⟩, y, hyF', hfy⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, heq,
    Set.ncard_image_of_injective _ hf.injective]

theorem drawingInSubspace_embedDrawing_V_inter_liftEdge_ncard {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : IsClosedEmbedding f) (G : Drawing S) (C : Set T)
    (hUC : (embedDrawing hf G).U ⊆ C) (F : Set S) :
    ((drawingInSubspace (embedDrawing hf G) C hUC).V ∩ liftEdge f C F).ncard =
      (G.V ∩ F).ncard := by
  rw [drawingInSubspace_embedDrawing_V, ← liftEdge_inter hf.injective]
  have hsub : f '' (G.V ∩ F) ⊆ C :=
    (image_mono (inter_subset_left.trans G.V_subset_U)).trans hUC
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective,
    subtype_image_liftEdge_of_subset hsub, Set.ncard_image_of_injective _ hf.injective]

theorem hasDisjointPathsBetween_zero {S : Type u} [TopologicalSpace S]
    (G : Drawing S) (X Y : Set S) : HasDisjointPathsBetween G X Y 0 :=
  ⟨Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩

theorem hasDisjointPathsBetween_le_ncard_V {S : Type u} [TopologicalSpace S]
    {G : Drawing S} {X Y : Set S} {k : ℕ} (h : HasDisjointPathsBetween G X Y k) :
    k ≤ G.V.ncard := by
  classical
  obtain ⟨P, s, t, hP, hdisj⟩ := h
  have hsV : ∀ i, s i ∈ (P i).V := fun i => by
    obtain ⟨W, _, hV, _⟩ := (hP i).2.2.2
    rw [hV]
    exact W.start_mem_support
  have hsG : range s ⊆ G.V := by
    rintro _ ⟨i, rfl⟩
    exact (hP i).1.1 (hsV i)
  have hinj : Injective s := fun i j hij => by
    by_contra hne
    exact disjoint_left.mp (hdisj i j hne) (hsV i) (hij ▸ hsV j)
  have hcard : (range s).ncard = k := by
    rw [Set.ncard_range_of_injective hinj, Nat.card_fin]
  rw [← hcard]
  exact Set.ncard_le_ncard hsG G.finite_V

/-- Pushing a graph walk of `D` to `drawingInSubspace (embedDrawing hf D) C hDU`. -/
noncomputable def liftGraphWalk {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T] [Nonempty S]
    {f : S → T} (hf : IsClosedEmbedding f) {D : Drawing S} {C : Set T}
    (hDU : (embedDrawing hf D).U ⊆ C) :
    ∀ {u v : S} (W : GraphWalk D.toGraph u v),
      GraphWalk (drawingInSubspace (embedDrawing hf D) C hDU).toGraph
        (liftPt hf hDU u (D.V_subset_U (W.mem_vertexSet_of_mem_support W.start_mem_support)))
        (liftPt hf hDU v (D.V_subset_U (W.mem_vertexSet_of_mem_support W.end_mem_support)))
  | _, _, .nil hv => .nil (by
      change _ ∈ (drawingInSubspace (embedDrawing hf D) C hDU).V
      rw [drawingInSubspace_embedDrawing_V]
      exact (liftPt_mem_liftEdge hf hDU (D.V_subset_U hv) D.V).mpr hv)
  | a, _, @GraphWalk.cons _ _ _ _ b c e hlink rest =>
    have ha : a ∈ D.V := hlink.2.1
    have hb : b ∈ D.V := hlink.2.2.1
    have he : e ∈ D.E := hlink.1
    have heU : e ⊆ D.U := subset_closure.trans (D.closure_subset_U he)
    have hlink' : (drawingInSubspace (embedDrawing hf D) C hDU).toGraph.IsLink
        (liftEdge f C e)
        (liftPt hf hDU a (D.V_subset_U ha))
        (liftPt hf hDU b (D.V_subset_U hb)) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [drawingInSubspace_embedDrawing_E]
        exact ⟨e, he, rfl⟩
      · rw [drawingInSubspace_embedDrawing_V]
        exact (liftPt_mem_liftEdge hf hDU (D.V_subset_U ha) D.V).mpr ha
      · rw [drawingInSubspace_embedDrawing_V]
        exact (liftPt_mem_liftEdge hf hDU (D.V_subset_U hb) D.V).mpr hb
      · rw [closure_liftEdge hf hDU heU, drawingInSubspace_embedDrawing_V,
          ← liftEdge_inter hf.injective, hlink.2.2.2,
          liftEdge_pair hf hDU (D.V_subset_U ha) (D.V_subset_U hb)]
    .cons hlink' (liftGraphWalk hf hDU rest)

theorem liftGraphWalk_support_val {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T] [Nonempty S]
    {f : S → T} (hf : IsClosedEmbedding f) {D : Drawing S} {C : Set T}
    (hDU : (embedDrawing hf D).U ⊆ C) {u v : S} (W : GraphWalk D.toGraph u v) :
    (liftGraphWalk hf hDU W).support.map Subtype.val = W.support.map f := by
  induction W with
  | nil _ => rfl
  | cons _ _ ih => simp [liftGraphWalk, ih]

theorem liftGraphWalk_edges {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T] [Nonempty S]
    {f : S → T} (hf : IsClosedEmbedding f) {D : Drawing S} {C : Set T}
    (hDU : (embedDrawing hf D).U ⊆ C) {u v : S} (W : GraphWalk D.toGraph u v) :
    (liftGraphWalk hf hDU W).edges = W.edges.map (liftEdge f C) := by
  induction W with
  | nil _ => rfl
  | cons _ _ ih => simp [liftGraphWalk, ih]

theorem hasDisjointPathsBetween_liftEdge {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T] [Nonempty S]
    {f : S → T} (hf : IsClosedEmbedding f) (G : Drawing S) (C : Set T)
    (hUC : (embedDrawing hf G).U ⊆ C) {X Y : Set S} {k : ℕ}
    (h : HasDisjointPathsBetween G X Y k) :
    HasDisjointPathsBetween (drawingInSubspace (embedDrawing hf G) C hUC)
      (liftEdge f C X) (liftEdge f C Y) k := by
  obtain ⟨P, s, t, hP, hdisj⟩ := h
  have hPU : ∀ i, (embedDrawing hf (P i)).U ⊆ C := fun i =>
    (image_mono (hP i).1.U_subset).trans hUC
  let P' : Fin k → Drawing C := fun i => drawingInSubspace (embedDrawing hf (P i)) C (hPU i)
  have hsV : ∀ i, s i ∈ (P i).V := fun i => by
    obtain ⟨W, _, hV, _⟩ := (hP i).2.2.2
    rw [hV]
    exact W.start_mem_support
  have htV : ∀ i, t i ∈ (P i).V := fun i => by
    obtain ⟨W, _, hV, _⟩ := (hP i).2.2.2
    rw [hV]
    exact W.end_mem_support
  let s' : Fin k → C := fun i => liftPt hf (hPU i) (s i) ((P i).V_subset_U (hsV i))
  let t' : Fin k → C := fun i => liftPt hf (hPU i) (t i) ((P i).V_subset_U (htV i))
  refine ⟨P', s', t', fun i => ?_, fun i j hij => ?_⟩
  · obtain ⟨hsub, hsX, htY, W, hWsim, hPV, hPE⟩ := hP i
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [drawingInSubspace_embedDrawing_V, drawingInSubspace_embedDrawing_V]
      exact preimage_mono (image_mono hsub.1)
    · rw [drawingInSubspace_embedDrawing_E, drawingInSubspace_embedDrawing_E]
      exact image_mono hsub.2
    · exact (liftPt_mem_liftEdge hf (hPU i) ((P i).V_subset_U (hsV i)) X).mpr hsX
    · exact (liftPt_mem_liftEdge hf (hPU i) ((P i).V_subset_U (htV i)) Y).mpr htY
    · refine ⟨liftGraphWalk hf (hPU i) W, ?_, ?_, ?_⟩
      · change (liftGraphWalk hf (hPU i) W).support.Nodup
        have hmap : (liftGraphWalk hf (hPU i) W).support.map Subtype.val = W.support.map f :=
          liftGraphWalk_support_val hf (hPU i) W
        exact List.Nodup.of_map Subtype.val (hmap ▸ hWsim.map hf.injective)
      · ext y
        rw [show (P' i).V = liftEdge f C (P i).V from drawingInSubspace_embedDrawing_V _ _ _ _]
        constructor
        · rintro ⟨x, hx, hfx⟩
          rw [hPV] at hx
          have hmem : f x ∈ (liftGraphWalk hf (hPU i) W).support.map Subtype.val := by
            rw [liftGraphWalk_support_val]
            exact List.mem_map_of_mem hx
          obtain ⟨y', hy', hfy'⟩ := List.mem_map.mp hmem
          rwa [Subtype.ext (hfx.symm.trans hfy'.symm)]
        · intro hy
          have hmem : y.val ∈ W.support.map f := by
            rw [← liftGraphWalk_support_val hf (hPU i) W]
            exact List.mem_map_of_mem hy
          obtain ⟨x, hx, hfx⟩ := List.mem_map.mp hmem
          have hxV : x ∈ (P i).V := by rw [hPV]; exact hx
          exact ⟨x, hxV, hfx⟩
      · ext e'
        rw [show (P' i).E = liftEdge f C '' (P i).E from drawingInSubspace_embedDrawing_E _ _ _ _,
          liftGraphWalk_edges]
        simp [hPE]
  · rw [show (P' i).V = liftEdge f C (P i).V from drawingInSubspace_embedDrawing_V _ _ _ _,
      show (P' j).V = liftEdge f C (P j).V from drawingInSubspace_embedDrawing_V _ _ _ _]
    exact disjoint_liftEdge hf.injective C (hdisj i j hij)

theorem maxDisjointPaths_le_liftEdge {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T] [Nonempty S]
    {f : S → T} (hf : IsClosedEmbedding f) (G : Drawing S) (C : Set T)
    (hUC : (embedDrawing hf G).U ⊆ C) (X Y : Set S) :
    maxDisjointPaths G X Y ≤
      maxDisjointPaths (drawingInSubspace (embedDrawing hf G) C hUC)
        (liftEdge f C X) (liftEdge f C Y) := by
  let G' := drawingInSubspace (embedDrawing hf G) C hUC
  have hne : {k : ℕ | HasDisjointPathsBetween G X Y k}.Nonempty :=
    ⟨0, hasDisjointPathsBetween_zero G X Y⟩
  have hbdd' : BddAbove {k : ℕ | HasDisjointPathsBetween G' (liftEdge f C X) (liftEdge f C Y) k} :=
    ⟨G'.V.ncard, fun k hk => hasDisjointPathsBetween_le_ncard_V hk⟩
  exact csSup_le hne fun k hk =>
    le_csSup hbdd' (hasDisjointPathsBetween_liftEdge hf G C hUC hk)

end GraphMinor.GM07
