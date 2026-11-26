/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.Surface.Circle
public import LeanPool.GraphMinor.GM10.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Definitions of Graph Minors XI

This file formalizes the definitions of N. Robertson and P. D. Seymour,
*Graph Minors. XI. Circuits on a surface*, J. Combin. Theory Ser. B 60 (1994) 72–106. Everything
is stated over the actual drawings and paintings of `GraphMinor/Surface/Defs.lean`.

- **Section 2:** tangles are those of Graph Minors X (`GM10.IsTangle`).
- **Section 3:** the type `PaintingOrDrawing` for the paper's "painting or drawing". Subdrawings:
  `Drawing.span` builds the subdrawing with given vertices and edges, and adds the ends of the
  edges. Circuits and paths (`Drawing.IsCircuit`, `Drawing.IsPathBetween`). Radial drawings
  (`PaintingOrDrawing.IsRadialDrawing`). Walks: concatenation, reverse, and `Γ | W`.
- **Section 4:** `Γ ∩ Δ` (`PaintingOrDrawing.inter`), respectful tangles, slopes (`IsSlope`),
  capture, confined subdrawings, `ins(Γ')` (`insOf`), non-separable drawings.
- **Section 5:** weightings, `N(Z)`, small sets.
- **Section 6:** pretangles (`IsPretangle`), the derived slope, the induced pretangle, perimeters
  of regions and even slopes.
- **Section 7:** nice sets, and the terms of Graph Minors VII, Section 11, that (7.3) and (7.5)
  quote: arc-connected, locally arc-connected, solid, flat, planar.
- **Section 8:** `Γ`-nice sets, perimeter walks, `l(X)`, restraints, extreme and optimal restraints.
- **Section 9:** atoms (in `Surface/Defs.lean`), the distance `d`, ties.

The paper's `θ ≥ 1` is half an integer. We write `k = 2θ`, a natural number with `2 ≤ k`, so that
"length `< 2θ`" reads `length < k`.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Hypergraph

universe u

/-! ## Section 3: subdrawings -/

section Subdrawing

variable {S : Type u} [TopologicalSpace S]

/-- An `O`-arc minus one of its points is path connected. -/
theorem isPathConnected_oArc_diff {F : Set S} (hF : IsOArc F) {u : S} (hu : u ∈ F) :
    IsPathConnected (F \ {u}) :=
  hF.isPathConnected_sdiff_singleton hu

namespace Drawing

variable (Γ : Drawing S)

section


theorem closure_subset_U {e : Set S} (he : e ∈ Γ.E) : closure e ⊆ Γ.U :=
  closure_minimal (he.2.1.trans sdiff_subset) Γ.isClosed_U

/-- An edge is its closure minus the vertices: "the ends" are all that the closure adds. -/
theorem closure_diff_V {e : Set S} (he : e ∈ Γ.E) : closure e \ Γ.V = e := by
  have hsub : e ⊆ closure e \ Γ.V := fun x hx => ⟨subset_closure hx, (he.2.1 hx).2⟩
  have hU := Γ.closure_subset_U he
  rcases Γ.edge_cond e he with ⟨u, v, huv, hcap, hL⟩ | ⟨u, hcap, hF⟩
  · have hEq : closure e \ {u, v} = closure e \ Γ.V := by
      rw [← hcap]
      ext x
      simp only [mem_sdiff, mem_inter_iff, not_and]
      tauto
    have hconn := hL.isPathConnected_interior
    rw [hEq] at hconn
    exact he.2.2.2 _ (fun x hx => ⟨hU hx.1, hx.2⟩) hconn hsub
  · have hEq : closure e \ {u} = closure e \ Γ.V := by
      rw [← hcap]
      ext x
      simp only [mem_sdiff, mem_inter_iff, not_and]
      tauto
    have huc : u ∈ closure e := by
      have : u ∈ closure e ∩ Γ.V := by rw [hcap]; exact mem_singleton u
      exact this.1
    have hconn := isPathConnected_oArc_diff hF huc
    rw [hEq] at hconn
    exact he.2.2.2 _ (fun x hx => ⟨hU hx.1, hx.2⟩) hconn hsub

/-- Two edges that share a point are equal. -/
theorem edge_eq_of_mem {e f : Set S} (he : e ∈ Γ.E) (hf : f ∈ Γ.E) {x : S} (hxe : x ∈ e)
    (hxf : x ∈ f) : e = f := by
  have hun : IsPathConnected (e ∪ f) := he.2.2.1.union hf.2.2.1 ⟨x, hxe, hxf⟩
  have h1 := he.2.2.2 (e ∪ f) (union_subset he.2.1 hf.2.1) hun subset_union_left
  have h2 := hf.2.2.2 (e ∪ f) (union_subset he.2.1 hf.2.1) hun subset_union_right
  exact h1.symm.trans h2

/-- The vertex set of `Γ.span V' E'`: the members of `V'` that are vertices of `Γ`, and the ends of
the edges in `E'`. -/
def spanV (V' : Set S) (E' : Set (Set S)) : Set S :=
  (V' ∩ Γ.V) ∪ ⋃ e ∈ E' ∩ Γ.E, closure e ∩ Γ.V

/-- The point set of `Γ.span V' E'`. -/
def spanU (V' : Set S) (E' : Set (Set S)) : Set S :=
  Γ.spanV V' E' ∪ ⋃ e ∈ E' ∩ Γ.E, closure e

theorem spanV_subset (V' : Set S) (E' : Set (Set S)) : Γ.spanV V' E' ⊆ Γ.V := by
  refine union_subset inter_subset_right ?_
  exact iUnion₂_subset fun _ _ => inter_subset_right

theorem spanU_diff_spanV (V' : Set S) (E' : Set (Set S)) :
    Γ.spanU V' E' \ Γ.spanV V' E' = ⋃₀ (E' ∩ Γ.E) := by
  ext x
  constructor
  · rintro ⟨hx, hxV⟩
    rcases hx with hx | hx
    · exact absurd hx hxV
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      refine ⟨e, he, ?_⟩
      rw [← Γ.closure_diff_V he.2]
      refine ⟨hxe, fun hxv => hxV ?_⟩
      exact Or.inr (mem_iUnion₂.mpr ⟨e, he, hxe, hxv⟩)
  · rintro ⟨e, he, hxe⟩
    refine ⟨Or.inr (mem_iUnion₂.mpr ⟨e, he, subset_closure hxe⟩), fun hxV => ?_⟩
    exact (he.2.2.1 hxe).2 (Γ.spanV_subset V' E' hxV)

private theorem preconnected_subset_edge (E' : Set (Set S)) {D : Set S}
    (hD : IsPreconnected D) (hDsub : D ⊆ ⋃₀ (E' ∩ Γ.E)) {e : Set S} (he : e ∈ E' ∩ Γ.E) {x : S}
    (hxD : x ∈ D) (hxe : x ∈ e) : D ⊆ e := by
  have hfin : (E' ∩ Γ.E).Finite := Γ.finite_edges.subset inter_subset_right
  set B : Set S := ⋃ f ∈ (E' ∩ Γ.E) \ {e}, closure f with hB
  have hBcl : IsClosed B :=
    (hfin.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure
  have hAcl : IsClosed (closure e) := isClosed_closure
  have hcover : D ⊆ closure e ∪ B := by
    intro y hy
    obtain ⟨f, hf, hyf⟩ := hDsub hy
    by_cases hfe : f = e
    · exact Or.inl (subset_closure (hfe ▸ hyf))
    · exact Or.inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hfe⟩, subset_closure hyf⟩)
  have hdisj : ∀ y ∈ D, y ∈ closure e → y ∉ B := by
    intro y hy hye hyB
    obtain ⟨f, hf, hyf⟩ := mem_iUnion₂.mp hyB
    obtain ⟨g, hg, hyg⟩ := hDsub hy
    have hyV : y ∉ Γ.V := (hg.2.2.1 hyg).2
    have h1 : y ∈ e := by rw [← Γ.closure_diff_V he.2]; exact ⟨hye, hyV⟩
    have h2 : y ∈ f := by rw [← Γ.closure_diff_V hf.1.2]; exact ⟨hyf, hyV⟩
    exact hf.2 (Γ.edge_eq_of_mem hf.1.2 he.2 h2 h1)
  have hnone : ¬ (D ∩ B).Nonempty := by
    intro hne
    obtain ⟨y, hy, hyA, hyB⟩ := isPreconnected_closed_iff.mp hD _ _ hAcl hBcl hcover
      ⟨x, hxD, subset_closure hxe⟩ hne
    exact hdisj y hy hyA hyB
  intro y hy
  have hyA : y ∈ closure e := (hcover hy).resolve_right fun hyB => hnone ⟨y, hy, hyB⟩
  obtain ⟨g, hg, hyg⟩ := hDsub hy
  rw [← Γ.closure_diff_V he.2]
  exact ⟨hyA, (hg.2.2.1 hyg).2⟩

theorem arcComponentsIn_span (V' : Set S) (E' : Set (Set S)) :
    arcComponentsIn (Γ.spanU V' E' \ Γ.spanV V' E') = E' ∩ Γ.E := by
  rw [Γ.spanU_diff_spanV]
  ext C
  constructor
  · rintro ⟨⟨x, hx⟩, hsub, hconn, hmax⟩
    obtain ⟨e, he, hxe⟩ := hsub hx
    have hCe : C ⊆ e := Γ.preconnected_subset_edge E' hconn.isConnected.isPreconnected hsub he
      hx hxe
    have : e = C := hmax e (subset_sUnion_of_mem he) he.2.2.2.1 hCe
    exact this ▸ he
  · intro he
    refine ⟨he.2.1, subset_sUnion_of_mem he, he.2.2.2.1, fun D hD hconn heD => ?_⟩
    obtain ⟨x, hx⟩ := he.2.1
    exact (Γ.preconnected_subset_edge E' hconn.isConnected.isPreconnected hD he (heD hx)
      hx).antisymm heD

end

variable [T1Space S]

/-- `Γ.span V' E'` is the subdrawing of `Γ` formed by the vertices in `V'`, the edges in `E'`, and
the ends of those edges. Members of `V'` that are not vertices of `Γ`, and members of `E'` that are
not edges of `Γ`, are ignored. Every subdrawing of `Γ` has this form (`Graph Minors XI`, Section 3,
page 74: "$\Gamma'$ is a *subdrawing* of a drawing $\Gamma$ if $V(\Gamma') \subseteq V(\Gamma)$ and
$E(\Gamma') \subseteq E(\Gamma)$"). -/
def span (V' : Set S) (E' : Set (Set S)) : Drawing S where
  U := Γ.spanU V' E'
  V := Γ.spanV V' E'
  V_subset_U := subset_union_left
  isClosed_U := by
    have hfin : (E' ∩ Γ.E).Finite := Γ.finite_edges.subset inter_subset_right
    refine IsClosed.union ?_ (hfin.isClosed_biUnion fun _ _ => isClosed_closure)
    exact ((Γ.finite_V.subset (Γ.spanV_subset V' E')).isClosed)
  finite_V := Γ.finite_V.subset (Γ.spanV_subset V' E')
  finite_edges := by
    rw [Γ.arcComponentsIn_span]
    exact Γ.finite_edges.subset inter_subset_right
  edge_cond := by
    intro e he
    rw [Γ.arcComponentsIn_span] at he
    have hcap : closure e ∩ Γ.spanV V' E' = closure e ∩ Γ.V := by
      apply subset_antisymm (inter_subset_inter_right _ (Γ.spanV_subset V' E'))
      rintro x ⟨hxe, hxV⟩
      exact ⟨hxe, Or.inr (mem_iUnion₂.mpr ⟨e, he, hxe, hxV⟩)⟩
    rw [hcap]
    exact Γ.edge_cond e he.2

theorem span_V (V' : Set S) (E' : Set (Set S)) : (Γ.span V' E').V = Γ.spanV V' E' := rfl

theorem span_U (V' : Set S) (E' : Set (Set S)) : (Γ.span V' E').U = Γ.spanU V' E' := rfl

theorem span_E (V' : Set S) (E' : Set (Set S)) : (Γ.span V' E').E = E' ∩ Γ.E :=
  Γ.arcComponentsIn_span V' E'

/-- The subdrawing formed by the vertices and edges of `Γ` included in `T`. This is the paper's
`Γ ∩ T` when `T` is a union of atoms of `Γ` (Graph Minors XI, Section 8, page 96: `Γ ∩ bd(X)`). -/
def interSet (T : Set S) : Drawing S :=
  Γ.span (Γ.V ∩ T) {e | e ∈ Γ.E ∧ e ⊆ T}

/-- `Γ \ e`, the subdrawing obtained by deleting the edge `e`
(Graph Minors XI, Section 4, proof of (4.4), page 80). -/
def deleteEdge (e : Set S) : Drawing S :=
  Γ.span Γ.V (Γ.E \ {e})

/-- `Γ₁ ∪ Γ₂` for subdrawings `Γ₁, Γ₂` of `Γ` (Graph Minors XI, Section 3, page 74). -/
def sup (Γ₁ Γ₂ : Drawing S) : Drawing S :=
  Γ.span (Γ₁.V ∪ Γ₂.V) (Γ₁.E ∪ Γ₂.E)

/-- `Γ` is connected: it has a vertex, and any two vertices are joined by a walk. -/
def IsConnected : Prop :=
  Γ.V.Nonempty ∧ ∀ u ∈ Γ.V, ∀ v ∈ Γ.V, Nonempty (GraphWalk Γ.toGraph u v)

/-- The *length* of a path or circuit is the number of edges in it
(Graph Minors XI, Section 4, pages 78–79). -/
noncomputable def length : ℕ := Γ.E.ncard

/-- `Γ` is a *circuit*: its vertices and edges are those of a simple-closed walk of positive length
(Graph Minors XI, Section 3, page 77, and Section 4, page 78: paths and circuits have no
"repeated" vertices). A loop with its end is a circuit of length one. -/
def IsCircuit : Prop :=
  ∃ (u : S) (W : GraphWalk Γ.toGraph u u), W.IsSimpleClosed ∧ 0 < W.length ∧
    Γ.V = {x | x ∈ W.support} ∧ Γ.E = {e | e ∈ W.edges}

/-- `Γ` is a *path* between `a` and `b`: its vertices and edges are those of a simple walk from `a`
to `b`. -/
def IsPathBetween (a b : S) : Prop :=
  ∃ W : GraphWalk Γ.toGraph a b, W.IsSimple ∧
    Γ.V = {x | x ∈ W.support} ∧ Γ.E = {e | e ∈ W.edges}

/-- `Γ` is *non-separable* if "it is connected and there is no separation $(A, B)$ of order $1$ with
$E(A), E(B) \ne
\emptyset$" (Graph Minors XI, Section 4, page 79). -/
def IsNonSeparable : Prop :=
  Γ.IsConnected ∧ ∀ A B : Hypergraph S (Set S), Γ.toHypergraph.IsSeparation A B →
    separationOrder A B = 1 → A.edgeSet.Nonempty → B.edgeSet.Nonempty → False

/-- `e` is a *loop* of `Γ`: an edge with exactly one end. -/
def IsLoop (e : Set S) : Prop :=
  e ∈ Γ.E ∧ ∃ u, closure e ∩ Γ.V = {u}

end Drawing


end Subdrawing

namespace GraphWalk

variable {α : Type u} {β : Type*} {G : Graph α β}

/-- `W + W'`, the concatenation of walks (Graph Minors XI, Section 3, page 77). -/
def append {u v w : α} : GraphWalk G u v → GraphWalk G v w → GraphWalk G u w
  | .nil _, W' => W'
  | .cons h r, W' => .cons h (r.append W')

/-- `W⁻¹`, the reverse of a walk (Graph Minors XI, Section 3, page 77). -/
def reverse {u v : α} : GraphWalk G u v → GraphWalk G v u
  | .nil h => .nil h
  | .cons h r => r.reverse.append (.cons h.symm (.nil h.left_mem))

end GraphWalk

end GraphMinor.Surface

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface Hypergraph

universe u

/-! ## Section 2 and the start of Section 6: pretangles -/

/-- A *pretangle* of order `θ ≥ 1` in a hypergraph `G` (Graph Minors XI, Section 6, page 87):
"a set $\mathscr{T}$ of separations of $G$, all of order $< \theta$, satisfying the first and
second tangle axioms". -/
structure IsPretangle {α β : Type*} (G : Hypergraph α β) (θ : ℕ)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) : Prop where
  /-- The order satisfies `θ ≥ 1`. -/
  one_le : 1 ≤ θ
  /-- Every member of `𝒯` is a separation of `G`. -/
  isSeparation : ∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ 𝒯 → G.IsSeparation A B
  /-- Every member of `𝒯` has order `< θ`. -/
  order_lt : ∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ 𝒯 → separationOrder A B < θ
  /-- The first tangle axiom. -/
  axiom1 : GM10.TangleAxiom1 G θ 𝒯
  /-- The second tangle axiom. -/
  axiom2 : GM10.TangleAxiom2 G 𝒯

/-- Pre-radial drawing conditions for a point set, its vertices, and its regions. -/
abbrev IsPreRadialOn {S : Type u} [TopologicalSpace S] (U V : Set S) (R : Set (Set S))
    (G : Drawing S) : Prop :=
  U ∩ G.U = V ∧
  V ⊆ G.V ∧
  (∀ r ∈ R, ∃! w, w ∈ r ∧ w ∈ G.V) ∧
  (∀ w ∈ G.V \ V, ∃ r ∈ R, w ∈ r) ∧
  (∀ e ∈ G.E, ∃ v ∈ V, ∃ w ∈ G.V \ V, closure e ∩ G.V = {v, w}) ∧
  (∀ e ∈ G.E, ∀ f ∈ G.E, e ≠ f → ∀ v ∈ V, ∀ r ∈ R, ∀ w ∈ r ∩ G.V,
    closure e ∩ G.V = {v, w} → closure f ∩ G.V = {v, w} →
    ¬ ∃ Δ : Set S, IsClosedDisc Δ ∧ Δ ⊆ r ∪ {v} ∧ subBd Δ = closure e ∪ closure f)

section Main

variable {S : Type u} [TopologicalSpace S] [T1Space S]

/-! ## Section 3: paintings or drawings -/

/-- The paper's "painting or drawing" (Graph Minors XI, Sections 3–6). A drawing is not a painting
in our definitions (the closure of an edge of a drawing is a line, not a closed disc), so each
statement about "a painting or drawing" is a statement about this type. -/
inductive PaintingOrDrawing (S : Type u) [TopologicalSpace S] where
  /-- A painting. -/
  | painting (Γ : Painting S)
  /-- A drawing. -/
  | drawing (Γ : Drawing S)

namespace PaintingOrDrawing

/-- `U(Γ)`. -/
def U : PaintingOrDrawing S → Set S
  | painting Γ => Γ.U
  | drawing Γ => Γ.U

/-- `V(Γ)`. -/
def V : PaintingOrDrawing S → Set S
  | painting Γ => Γ.V
  | drawing Γ => Γ.V

/-- `E(Γ)`. -/
def E : PaintingOrDrawing S → Set (Set S)
  | painting Γ => Γ.E
  | drawing Γ => Γ.E

/-- `R(Γ)`, the components of `Σ − U(Γ)`. -/
noncomputable def R : PaintingOrDrawing S → Set (Set S)
  | painting Γ => Γ.R
  | drawing Γ => Γ.R

/-- The hypergraph defined by `V(Γ)`, `E(Γ)` and their incidence relation. -/
def toHypergraph : PaintingOrDrawing S → Hypergraph S (Set S)
  | painting Γ => Γ.toHypergraph
  | drawing Γ => Γ.toHypergraph

/-- `Γ` is *2-cell* (Graph Minors XI, Section 3, page 75): "$\Sigma$ is connected and every region
is an open disc". -/
def IsTwoCell (Γ : PaintingOrDrawing S) : Prop :=
  ConnectedSpace S ∧ ∀ r ∈ Γ.R, IsOpenDisc r

/-- `Z ⊆ Σ` is *`Γ`-normal* (Graph Minors XI, Section 4, page 78): `Z ∩ U(Γ) ⊆ V(Γ)`. -/
def IsNormal (Γ : PaintingOrDrawing S) (Z : Set S) : Prop :=
  Z ∩ Γ.U ⊆ Γ.V

/-- `Γ` is *`θ`-representative* (Graph Minors XI, Section 4, page 78): `Σ` is connected and every
`Γ`-normal `O`-arc `F` with `|F ∩ V(Γ)| < θ` is null-homotopic. -/
def IsRepresentative (Γ : PaintingOrDrawing S) (θ : ℕ) : Prop :=
  ConnectedSpace S ∧
    ∀ F : Set S, IsOArc F → Γ.IsNormal F → (F ∩ Γ.V).ncard < θ → IsNullHomotopicOArc F

omit [T1Space S] in
@[simp] theorem toHypergraph_vertexSet (Γ : PaintingOrDrawing S) :
    Γ.toHypergraph.vertexSet = Γ.V := by
  cases Γ <;> rfl

omit [T1Space S] in
@[simp] theorem toHypergraph_edgeSet (Γ : PaintingOrDrawing S) :
    Γ.toHypergraph.edgeSet = Γ.E := by
  cases Γ <;> rfl

/-- `Γ ∩ Δ` as a hypergraph (Graph Minors XI, Section 4, page 78): for closed `Δ` with `bd(Δ)`
`Γ`-normal, "$(U(\Gamma) \cap \Delta, V(\Gamma) \cap \Delta)$ is a painting or drawing
(respectively) which we denote by $\Gamma \cap \Delta$". Its
vertices are those of `Γ` in `Δ`, and its edges are those of `Γ` included in `Δ`. -/
def inter (Γ : PaintingOrDrawing S) (Δ : Set S) : Hypergraph S (Set S) where
  vertexSet := Γ.V ∩ Δ
  edgeSet := {e | e ∈ Γ.E ∧ e ⊆ Δ}
  Inc e v := Γ.toHypergraph.Inc e v ∧ e ⊆ Δ ∧ v ∈ Δ
  vertex_mem_of_inc _ _ h :=
    ⟨Γ.toHypergraph_vertexSet ▸ Γ.toHypergraph.vertex_mem_of_inc h.1, h.2.2⟩
  edge_mem_of_inc _ _ h := ⟨Γ.toHypergraph_edgeSet ▸ Γ.toHypergraph.edge_mem_of_inc h.1, h.2.1⟩
  vertexSet_finite := (Γ.toHypergraph_vertexSet ▸ Γ.toHypergraph.vertexSet_finite).subset
    inter_subset_left
  edgeSet_finite := (Γ.toHypergraph_edgeSet ▸ Γ.toHypergraph.edgeSet_finite).subset fun _ h => h.1

/-- The set `Γ ∩ closure (Σ − Δ)` of the pair `(Γ ∩ Δ, Γ ∩ closure (Σ − Δ))`. -/
def interOutside (Γ : PaintingOrDrawing S) (Δ : Set S) : Hypergraph S (Set S) :=
  Γ.inter (closure (univ \ Δ))

/-- A set `𝒯` of separations of `Γ` is *respectful* of order `θ` (Graph Minors XI, Section 4,
page 78): "$\Sigma$ is connected and for every $\Gamma$-normal $O$-arc $F$ in $\Sigma$ with
$|F \cap V(\Gamma)| < \theta$, there is a closed disc $\Delta \subseteq \Sigma$ with
$bd(\Delta) = F$ such that
$$(\Gamma \cap \Delta, \Gamma \cap \overline{\Sigma - \Delta}) \in \mathscr{T}.$$". -/
def IsRespectful (Γ : PaintingOrDrawing S) (θ : ℕ)
    (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) : Prop :=
  ConnectedSpace S ∧
    ∀ F : Set S, IsOArc F → Γ.IsNormal F → (F ∩ Γ.V).ncard < θ →
      ∃ Δ : Set S, IsClosedDisc Δ ∧ subBd Δ = F ∧ (Γ.inter Δ, Γ.interOutside Δ) ∈ 𝒯

/-- Conditions (i)–(iv) of a radial drawing `Γ'` of `Γ` (Graph Minors XI, Section 3, page 75):
(i) `U(Γ) ∩ U(Γ') = V(Γ) ⊆ V(Γ')`;
(ii) each region `r` of `Γ` contains a unique vertex `v_r` of `Γ'`;
(iii) `Γ'` is bipartite, and `(V(Γ), {v_r})` is a bipartition of `Γ'`;
(iv) if `e, f` are edges of `Γ'` with the same ends `v, v_r`, where `v ∈ V(Γ)` and `r ∈ R(Γ)`, then
`closure e ∪ closure f` does not bound a closed disc in `r ∪ {v}`. -/
def IsPreRadialDrawing (Γ : PaintingOrDrawing S) (Γ' : Drawing S) : Prop :=
  IsPreRadialOn Γ.U Γ.V Γ.R Γ'

/-- `Γ'` is a *radial drawing* of the 2-cell painting or drawing `Γ` (Graph Minors XI, Section 3,
page 75): it satisfies (i)–(iv) of `IsPreRadialDrawing`, and "(v) $\Gamma'$ is maximal subject to
(i), ..., (iv)". -/
def IsRadialDrawing (Γ : PaintingOrDrawing S) (Γ' : Drawing S) : Prop :=
  Γ.IsTwoCell ∧ Γ.IsPreRadialDrawing Γ' ∧
    ∀ Γ'' : Drawing S, Γ.IsPreRadialDrawing Γ'' → Γ'.IsSubdrawing Γ'' → Γ''.IsSubdrawing Γ'

/-- For a subhypergraph `A` of `Γ`, the point set `U(A)`: the vertices and the edges of `A`
(Graph Minors XI, (6.4), page 90). -/
def underlying (A : Hypergraph S (Set S)) : Set S :=
  A.vertexSet ∪ ⋃₀ A.edgeSet

/-- `Z(A)`, "the set of regions of $\Gamma'$ which include an edge of $A$"
(Graph Minors XI, (6.1), page 87). -/
def regionsIncludingEdge (Γ' : Drawing S) (A : Hypergraph S (Set S)) : Set (Set S) :=
  {r | r ∈ Γ'.R ∧ ∃ e ∈ A.edgeSet, e ⊆ r}

end PaintingOrDrawing

/-! ## Section 3: walks -/

/-- `Γ | W`, "the subdrawing of $\Gamma$ with vertex set $\{v_0, v_1, \dots, v_t\}$ and edge set
$\{e_1, e_2, \dots, e_t\}$"
(Graph Minors XI, Section 3, page 77). `U(W)` is `(walkDrawing Γ W).U`. -/
def walkDrawing (Γ : Drawing S) {u v : S} (W : GraphWalk Γ.toGraph u v) : Drawing S :=
  Γ.span {x | x ∈ W.support} {e | e ∈ W.edges}

/-! ## Section 4: slopes -/

/-- `ins` is a *slope* in `Γ` of order `k / 2` (Graph Minors XI, Section 4, page 78). "A *slope* in
$\Gamma$ of order $\theta$ is a function $\text{ins}$ which assigns to every
circuit $C$ of $\Gamma$ of length $< 2\theta$ a closed disc $\text{ins}(C) \subseteq
\Sigma$, bounded by $U(C)$, such that (i) if $C_1, C_2$ are circuits of $\Gamma$, both of
length $< 2\theta$, and $U(C_1) \subseteq \text{ins}(C_2)$, then $\text{ins}(C_1) \subseteq
\text{ins}(C_2)$ (ii) if $P_0, P_1, P_2$ are three paths of $\Gamma$ of length $> 0$, with
the same ends, mutually internally disjoint, and the circuits $P_1 \cup P_2$, $P_2 \cup
P_0$, $P_0 \cup P_1$ all have length $< 2\theta$, then one of $$\text{ins}(P_1 \cup P_2),
\quad \text{ins}(P_2 \cup P_0), \quad \text{ins}(P_0 \cup P_1)$$ includes the other two."
Here `k = 2θ`. The function `ins` is total; only its values on circuits of length `< k` matter. -/
structure IsSlope (Γ : Drawing S) (k : ℕ) (ins : Drawing S → Set S) : Prop where
  /-- `θ ≥ 1`. -/
  two_le : 2 ≤ k
  /-- `ins(C)` is a closed disc. -/
  isClosedDisc : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ → C.length < k →
    IsClosedDisc (ins C)
  /-- `ins(C)` is bounded by `U(C)`. -/
  subBd_eq : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ → C.length < k →
    subBd (ins C) = C.U
  /-- The first slope axiom. -/
  monotone : ∀ C₁ C₂ : Drawing S, C₁.IsCircuit → C₁.IsSubdrawing Γ → C₁.length < k →
    C₂.IsCircuit → C₂.IsSubdrawing Γ → C₂.length < k → C₁.U ⊆ ins C₂ → ins C₁ ⊆ ins C₂
  /-- The second slope axiom. -/
  three_paths : ∀ (P₀ P₁ P₂ : Drawing S) (a b : S),
    P₀.IsPathBetween a b → P₁.IsPathBetween a b → P₂.IsPathBetween a b →
    P₀.IsSubdrawing Γ → P₁.IsSubdrawing Γ → P₂.IsSubdrawing Γ →
    0 < P₀.length → 0 < P₁.length → 0 < P₂.length →
    P₀.V ∩ P₁.V = {a, b} → P₁.V ∩ P₂.V = {a, b} → P₂.V ∩ P₀.V = {a, b} →
    Disjoint P₀.E P₁.E → Disjoint P₁.E P₂.E → Disjoint P₂.E P₀.E →
    (Γ.sup P₁ P₂).length < k → (Γ.sup P₂ P₀).length < k → (Γ.sup P₀ P₁).length < k →
    (ins (Γ.sup P₂ P₀) ⊆ ins (Γ.sup P₁ P₂) ∧ ins (Γ.sup P₀ P₁) ⊆ ins (Γ.sup P₁ P₂)) ∨
    (ins (Γ.sup P₁ P₂) ⊆ ins (Γ.sup P₂ P₀) ∧ ins (Γ.sup P₀ P₁) ⊆ ins (Γ.sup P₂ P₀)) ∨
    (ins (Γ.sup P₁ P₂) ⊆ ins (Γ.sup P₀ P₁) ∧ ins (Γ.sup P₂ P₀) ⊆ ins (Γ.sup P₀ P₁))

/-- A subdrawing `Γ'` *captures* `X ⊆ Σ` (Graph Minors XI, Section 4, page 79): "there is a circuit
$C$ of $\Gamma'$ of length $< 2\theta$ with $X \subseteq \text{ins}(C)$". -/
def Captures (ins : Drawing S → Set S) (k : ℕ) (Γ' : Drawing S) (X : Set S) : Prop :=
  ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing Γ' ∧ C.length < k ∧ X ⊆ ins C

/-- A subdrawing `Γ'` is *confined* (Graph Minors XI, Section 4, page 79): "every circuit of `Γ'`
has length `< 2θ`". -/
def IsConfined (k : ℕ) (Γ' : Drawing S) : Prop :=
  ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ' → C.length < k

/-- `ins(Γ')` for a confined `Γ'` (Graph Minors XI, Section 4, page 79): "the union of $U(\Gamma')$
and $\text{ins}(C)$ for all circuits $C$ of $\Gamma'$". -/
def insOf (ins : Drawing S → Set S) (Γ' : Drawing S) : Set S :=
  Γ'.U ∪ ⋃ C ∈ {C : Drawing S | C.IsCircuit ∧ C.IsSubdrawing Γ'}, ins C

/-- `ins(W)` for a closed walk `W` with `Γ | W` confined (Graph Minors XI, Section 8, page 96). -/
def insWalk (ins : Drawing S → Set S) (Γ : Drawing S) {u : S} (W : GraphWalk Γ.toGraph u u) :
    Set S :=
  insOf ins (walkDrawing Γ W)

/-! ## Section 5: small sets -/

/-- `(Ω, ω)` is a *weighting* (Graph Minors XI, Section 5, page 81): "$\Omega \subseteq V(\Gamma)$,
$\omega \ge 1$ is an integer and $|\Omega \cap V(C)| \ge
\omega$ for every circuit $C$ of $\Gamma$ of length $\ge 2\theta$". -/
structure IsWeighting (Γ : Drawing S) (k : ℕ) (Ω : Set S) (ω : ℕ) : Prop where
  /-- `Ω ⊆ V(Γ)`. -/
  subset : Ω ⊆ Γ.V
  /-- `ω ≥ 1`. -/
  one_le : 1 ≤ ω
  /-- Every long circuit has weight at least `ω`. -/
  le_ncard : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ → k ≤ C.length →
    ω ≤ (Ω ∩ C.V).ncard

/-- `N(Z)` for `Z ⊆ R(Γ)` (Graph Minors XI, Section 5, page 81): "the subdrawing of $\Gamma$ formed
by those vertices and edges of $\Gamma$ incident both with
a member of $Z$ and with a member of $R(\Gamma) - Z$". -/
def boundaryDrawing (Γ : Drawing S) (Z : Set (Set S)) : Drawing S :=
  Γ.span {v | (∃ r ∈ Z, Γ.VertexIncident v r) ∧ ∃ r ∈ Γ.R \ Z, Γ.VertexIncident v r}
    {e | (∃ r ∈ Z, Γ.EdgeRegionIncident e r) ∧ ∃ r ∈ Γ.R \ Z, Γ.EdgeRegionIncident e r}

/-- `Z ⊆ R(Γ)` is *small* with respect to `(Ω, ω)` (Graph Minors XI, Section 5, page 81):
"$|\Omega \cap V(N(Z))| < \omega$, and $N(Z)$ captures $r$ for each $r \in Z$". -/
def IsSmall (Γ : Drawing S) (ins : Drawing S → Set S) (k : ℕ) (Ω : Set S) (ω : ℕ)
    (Z : Set (Set S)) : Prop :=
  (Ω ∩ (boundaryDrawing Γ Z).V).ncard < ω ∧ ∀ r ∈ Z, Captures ins k (boundaryDrawing Γ Z) r

/-- `Z ⊆ R(Γ)` is *little* (Graph Minors XI, Section 5, page 86): "$N(Z)$ is confined, and $N(Z)$
captures each member of $Z$". -/
def IsLittle (Γ : Drawing S) (ins : Drawing S → Set S) (k : ℕ) (Z : Set (Set S)) : Prop :=
  IsConfined k (boundaryDrawing Γ Z) ∧ ∀ r ∈ Z, Captures ins k (boundaryDrawing Γ Z) r

/-! ## Section 6: tangles and slopes -/

/-- `ins` is the slope in `Γ'` *derived* from `𝒯` (Graph Minors XI, Section 6, page 87): for each
circuit `C` of `Γ'` of length `< 2θ`, `ins(C)` is a closed disc with boundary `U(C)` and
`(Γ ∩ ins(C), Γ ∩ closure (Σ − ins(C))) ∈ 𝒯`. -/
def IsDerivedSlope (Γ : PaintingOrDrawing S) (Γ' : Drawing S) (θ : ℕ)
    (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (ins : Drawing S → Set S) : Prop :=
  ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ' → C.length < 2 * θ →
    IsClosedDisc (ins C) ∧ subBd (ins C) = C.U ∧ (Γ.inter (ins C), Γ.interOutside (ins C)) ∈ 𝒯

/-- The *pretangle induced from* `ins` (Graph Minors XI, (6.1), page 87): "the set of all
separations $(A, B)$ of $\Gamma$ of order $< \theta$ such that $Z(A)$ is
small with respect to the weighting $(V(\Gamma), \theta)$ of $\Gamma'$". -/
def inducedPretangle (Γ : PaintingOrDrawing S) (Γ' : Drawing S) (θ : ℕ)
    (ins : Drawing S → Set S) : Set (Hypergraph S (Set S) × Hypergraph S (Set S)) :=
  {p | Γ.toHypergraph.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < θ ∧
    IsSmall Γ' ins (2 * θ) Γ.V θ (PaintingOrDrawing.regionsIncludingEdge Γ' p.1)}

/-- The *perimeter* of a region `r` of `Γ` (Graph Minors XI, Section 6, page 91): "the drawing
`Γ ∩ closure r`". -/
def perimeter (Γ : Drawing S) (r : Set S) : Drawing S :=
  Γ.interSet (closure r)

/-- The *length* of the perimeter of `r` (Graph Minors XI, Section 6, page 91):
"$\sum_{e \in E(\Gamma \cap \bar{r})} n(e)$, where $n(e) = 1$ or $2$, depending whether $e$
is incident with another region or not". -/
noncomputable def perimeterLength (Γ : Drawing S) (r : Set S) : ℕ :=
  ∑ᶠ e ∈ (perimeter Γ r).E,
    open Classical in if ∃ r' ∈ Γ.R, r' ≠ r ∧ Γ.EdgeRegionIncident e r' then 1 else 2

/-- A slope is *even* (Graph Minors XI, Section 6, page 91): "for every region $r$ of $\Gamma$ with
perimeter of length $< 2\theta$, there is a circuit
$C$ of $\Gamma$ of length $< 2\theta$ with $r \subseteq ins(C)$". -/
def IsEvenSlope (Γ : Drawing S) (k : ℕ) (ins : Drawing S → Set S) : Prop :=
  ∀ r ∈ Γ.R, perimeterLength Γ r < k → Captures ins k Γ r

/-! ## Section 7: nice sets, and terms quoted from Graph Minors VII -/

/-- `X ⊆ Σ` is *`Γ`-nice* (Graph Minors XI, Section 8, page 96): "$X$ is a union of vertices, edges
and regions of $\Gamma$". -/
def IsGammaNice (Γ : Drawing S) (X : Set S) : Prop :=
  ∃ 𝒜 ⊆ Γ.A, X = ⋃₀ 𝒜

/-- `Z ⊆ Σ` is *nice* (Graph Minors XI, Section 7, page 93): "there is a drawing $\Gamma$ in
$\Sigma$ such that $Z$ is the union of certain vertices,
edges, and regions of $\Gamma$". -/
def IsNice (Z : Set S) : Prop :=
  ∃ Γ : Drawing S, IsGammaNice Γ Z

/-- `Z ⊆ Σ` is *arc-connected* (Graph Minors VII, Section 11, page 249): "for every pair $a, b \in
Z$ with $a \ne b$ there is a $[0, 1]$-arc included in $Z$ with ends
$a, b$". -/
def IsArcConnected (Z : Set S) : Prop :=
  ∀ a ∈ Z, ∀ b ∈ Z, a ≠ b → ∃ L : Set S, L ⊆ Z ∧ IsLineWithEnds L a b

/-- `Z ⊆ Σ` is *locally arc-connected* (Graph Minors VII, Section 11, page 251): "for every $z \in
Z$ and every open set $A \subseteq \Sigma$ with $z \in A$ there exists $A'
\subseteq A$ with $z \in A'$, open in $\Sigma$, such that $Z \cap A'$ is arc-connected". -/
def IsLocallyArcConnected (Z : Set S) : Prop :=
  ∀ z ∈ Z, ∀ A : Set S, IsOpen A → z ∈ A →
    ∃ A' : Set S, A' ⊆ A ∧ z ∈ A' ∧ IsOpen A' ∧ IsArcConnected (Z ∩ A')

/-- `Z ⊆ Σ` is *solid* (Graph Minors VII, Section 11, page 252): "`Z` is l.a.c. and closed". -/
def IsSolid (Z : Set S) : Prop :=
  IsLocallyArcConnected Z ∧ IsClosed Z

/-- `Z ⊆ Σ` is *flat* (Graph Minors VII, Section 11, page 249): "every continuous $\phi \colon S^1
\to Z$ is null-homotopic in $\Sigma$". -/
def IsFlat (Z : Set S) : Prop :=
  ∀ φ : C(Circle, S), range φ ⊆ Z → ClosedCurveIsNullHomotopicIn univ φ

/-- `X ⊆ Σ` is *planar* (Graph Minors VII, Section 5, page 232): "`X ⊆ Δ` for some closed disc
`Δ ⊆ Σ`". -/
def IsPlanar (X : Set S) : Prop :=
  ∃ Δ : Set S, IsClosedDisc Δ ∧ X ⊆ Δ

/-! ## Section 8: restraints -/

/-- The closed curve `t ↦ h (e^{2π i t}, 0)` of a collar `h`. -/
noncomputable def collarCurve (h : C(Circle × unitInterval, S)) : ℝ → S :=
  fun t => h (Circle.exp (2 * Real.pi * t), 0)

/-- The curve `φ`, on `[a, b]`, runs along the walk, once along each step: there are numbers
`a = x₀ ≤ x₁ ≤ … ≤ x_t = b` with `φ(x_i) = v_i`, and `φ` maps `(x_{i-1}, x_i)` bijectively to
the edge `e_i`. -/
def RunsAlongOn (Γ : Drawing S) (φ : ℝ → S) : (a b : ℝ) → {u v : S} →
    GraphWalk Γ.toGraph u v → Prop
  | a, b, u, _, .nil _ => a = b ∧ φ a = u
  | a, b, u, _, .cons (e := e) _ rest =>
      ∃ c, a < c ∧ φ a = u ∧ InjOn φ (Ioo a c) ∧ φ '' Ioo a c = e ∧ RunsAlongOn Γ φ c b rest

/-- `W` is a *perimeter walk* of `X` (Graph Minors XI, Section 8, page 96): `X` is closed,
simply-connected and `Γ`-nice with `X ≠ ∅, Σ`, and "there is a closed walk of $\Gamma$ tracing out
$bd(X)$ in the natural sense". The paper gives no further definition. We make "in the natural
sense" precise, as the view of `bd(X)` from `Σ − X`: there is a collar
`h : S¹ × [0, 1] → Σ`, injective on `S¹ × (0, 1]`, which maps `S¹ × (0, 1]` into `Σ − X` and
whose circle `h(S¹ × {0})` is `bd(X)`, running along `W`, and such that `X ∪ h(S¹ × [0, 1))` is
open,
so that the collar fills a whole neighbourhood of `X` outside `X`. -/
def IsPerimeterWalk (Γ : Drawing S) (X : Set S) {u : S} (W : GraphWalk Γ.toGraph u u) : Prop :=
  ∃ h : C(Circle × unitInterval, S),
    InjOn h {p | 0 < p.2} ∧ (∀ p : Circle × unitInterval, 0 < p.2 → h p ∉ X) ∧
    range (fun z : Circle => h (z, 0)) = subBd X ∧ IsOpen (X ∪ h '' {p | p.2 < 1}) ∧
    ((W.length = 0 ∧ ∀ z : Circle, h (z, 0) = u) ∨
      (0 < W.length ∧ RunsAlongOn Γ (collarCurve h) 0 1 W))

/-- `l(X)`, the length of a perimeter walk of `X` (Graph Minors XI, Section 8, page 96: "We denote
the length of this walk by $l(X)$"). The perimeter walks of `X` are obtained from one another by
reinitializing and reversal, and so have the same length. -/
noncomputable def perimeterWalkLength (Γ : Drawing S) (X : Set S) : ℕ :=
  sInf {t | ∃ (u : S) (W : GraphWalk Γ.toGraph u u), IsPerimeterWalk Γ X W ∧ W.length = t}

/-- `X ⊆ Σ` is a *restraint* of `Γ` with respect to `ins` (Graph Minors XI, Section 8, page 96):
"$X \ne \emptyset$ is closed, simply-connected and $\Gamma$-nice, $l(X) < 2\theta$, and
$\Sigma - X \notin \mathrm{ins}(\Gamma \cap bd(X))$" (where $\notin$ in the paper means
$\not\subseteq$).
The last condition fails for `X = Σ`, as `l(Σ)` is not defined. -/
structure IsRestraint (Γ : Drawing S) (ins : Drawing S → Set S) (k : ℕ) (X : Set S) : Prop where
  /-- `X ≠ ∅`. -/
  nonempty : X.Nonempty
  /-- `X` is closed. -/
  isClosed : IsClosed X
  /-- `X` is simply-connected. -/
  isSimplyConnected : IsSimplyConnectedSet X
  /-- `X` is `Γ`-nice. -/
  isGammaNice : IsGammaNice Γ X
  /-- `l(X) < 2θ`. -/
  length_lt : perimeterWalkLength Γ X < k
  /-- `Σ − X` is not included in `ins(Γ ∩ bd(X))`. -/
  compl_not_subset : ¬ (univ \ X ⊆ insOf ins (Γ.interSet (subBd X)))

/-- A restraint `X` is *extreme* (Graph Minors XI, Section 8, page 97): "there is no restraint $Y
\ne X$ with $X \subseteq Y$ and $l(Y) \le l(X)$". -/
def IsExtremeRestraint (Γ : Drawing S) (ins : Drawing S → Set S) (k : ℕ) (X : Set S) : Prop :=
  IsRestraint Γ ins k X ∧ ∀ Y : Set S, IsRestraint Γ ins k Y → X ⊆ Y →
    perimeterWalkLength Γ Y ≤ perimeterWalkLength Γ X → Y = X

/-- A restraint `X` is *`a, b`-optimal* (Graph Minors XI, Section 8, page 100): "$a, b \in X$, and
there is no restraint $Y$ with $a, b \in Y$ and $l(Y) < l(X)$". -/
def IsOptimalRestraint (Γ : Drawing S) (ins : Drawing S → Set S) (k : ℕ) (a b : S) (X : Set S) :
    Prop :=
  IsRestraint Γ ins k X ∧ a ∈ X ∧ b ∈ X ∧ ∀ Y : Set S, IsRestraint Γ ins k Y → a ∈ Y → b ∈ Y →
    perimeterWalkLength Γ X ≤ perimeterWalkLength Γ Y

/-- A restraint is *`a, b`-extreme* (Graph Minors XI, Section 8, page 100): "it is `a, b`-optimal
and extreme". -/
def IsPairExtremeRestraint (Γ : Drawing S) (ins : Drawing S → Set S) (k : ℕ) (a b : S) (X : Set S) :
    Prop :=
  IsOptimalRestraint Γ ins k a b X ∧ IsExtremeRestraint Γ ins k X

/-- The optimal version for atoms (Graph Minors XI, Section 8, page 100): "If $b$ is an edge or
region, we say that $X$ is *$a, b$-optimal* if it is $a, b'$-optimal
for some $b' \in b$." -/
def IsAtomOptimalRestraint (Γ : Drawing S) (ins : Drawing S → Set S) (k : ℕ) (a b X : Set S) :
    Prop :=
  ∃ a' ∈ a, ∃ b' ∈ b, IsOptimalRestraint Γ ins k a' b' X

/-- The extreme version for atoms (Graph Minors XI, Section 8, page 100). -/
def IsAtomExtremeRestraint (Γ : Drawing S) (ins : Drawing S → Set S) (k : ℕ) (a b X : Set S) :
    Prop :=
  ∃ a' ∈ a, ∃ b' ∈ b, IsPairExtremeRestraint Γ ins k a' b' X

/-! ## Section 9: the distance function -/

/-- `2 d(a, b)` for atoms `a, b` of `Γ` (Graph Minors XI, Section 9, page 104):
"(i) if $a = b$ then $d(a, b) = 0$
(ii) if $a \ne b$ and $a, b \subseteq X$ for some restraint $X$, we define $d(a, b)$ to be
$\min \frac{1}{2}l(X)$, taken over all such $X$
(iii) if (i) and (ii) do not apply then $d(a, b) = \theta$." We
record twice the distance, as `d` may be half an integer. -/
noncomputable def twiceDistance (Γ : Drawing S) (ins : Drawing S → Set S) (k : ℕ) (a b : Set S) :
    ℕ :=
  open Classical in
  if a = b then 0
  else if ∃ X, IsRestraint Γ ins k X ∧ a ⊆ X ∧ b ⊆ X then
    sInf {t | ∃ X, IsRestraint Γ ins k X ∧ a ⊆ X ∧ b ⊆ X ∧ perimeterWalkLength Γ X = t}
  else k

/-- A *tie* (Graph Minors XI, Section 9, pages 104–105): a restraint `X` such that either
(i) `|X| = 1`, or (ii) `X` is a line, or (iii) `X` is a closed disc, or
(iv) `X = D₁ ∪ D₂`, where `D₁, D₂` are closed discs with `|D₁ ∩ D₂| = 1`, or
(v) `X = D ∪ F`, where `D` is a closed disc and `F` is a line with one end in `D` and no other point
in `D`, or
(vi) `X = D₁ ∪ D₂ ∪ F`, where `D₁, D₂` are disjoint closed discs and `F` is a line with one end in
`D₁`, the other in `D₂`, and no other point in `D₁ ∪ D₂`. -/
def IsTie (Γ : Drawing S) (ins : Drawing S → Set S) (k : ℕ) (X : Set S) : Prop :=
  IsRestraint Γ ins k X ∧
    (X.ncard = 1 ∧ X.Finite ∨
      IsLine X ∨
      IsClosedDisc X ∨
      (∃ D₁ D₂ : Set S, IsClosedDisc D₁ ∧ IsClosedDisc D₂ ∧ (D₁ ∩ D₂).ncard = 1 ∧
        (D₁ ∩ D₂).Finite ∧ X = D₁ ∪ D₂) ∨
      (∃ (D F : Set S) (a b : S), IsClosedDisc D ∧ IsLineWithEnds F a b ∧ F ∩ D = {a} ∧
        X = D ∪ F) ∨
      (∃ (D₁ D₂ F : Set S) (a b : S), IsClosedDisc D₁ ∧ IsClosedDisc D₂ ∧ Disjoint D₁ D₂ ∧
        IsLineWithEnds F a b ∧ F ∩ D₁ = {a} ∧ F ∩ D₂ = {b} ∧ X = D₁ ∪ D₂ ∪ F))

end Main

end GraphMinor.GM11
