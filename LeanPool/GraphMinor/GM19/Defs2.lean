/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Defs
public import LeanPool.GraphMinor.GM11.Defs
public import LeanPool.GraphMinor.GM10.Defs2
public import LeanPool.GraphMinor.GM18.Defs
public import LeanPool.GraphMinor.Surface.TopologyStatements
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Definitions for Graph Minors XIX (Sections 2–8)

This file formalizes the definitions from Sections 2–8 (pages 327–350) of N. Robertson and
P. D. Seymour, *Graph Minors. XIX. Well-quasi-ordering on a surface*, J. Combin. Theory Ser. B 90
(2004) 325–385:

- Section 2: drawings (`Drawing`, an abbreviation for `Surface.Drawing`, with
`Drawing.IsGM19Drawing`
  for the loopless and boundary-respecting conditions of XIX), regions (`Drawing.regions`,
  `Painting.regions`), internal edges (`Painting.IsInternal`), `Γ`-normal sets (`Painting.IsNormal`,
  `Drawing.IsNormal`), and the bridge from `GM19.Painting` to `Surface.Painting` and
  `GM11.PaintingOrDrawing` (`Painting.toSurfacePainting`, `Painting.toPaintingOrDrawing`).
- Section 3: frames (`Frame`), fitting a frame (`Painting.Fits`), respecting a frame
  (`RespectsFrame`), quasi-orders and well-quasi-orders (`QuasiOrder`, `QuasiOrder.IsWQO`, and the
  bridge to `[Preorder Ω]` and `WellQuasiOrderedLE`), colour schemes (`ColourScheme`),
  `χ`-coloured paintings (`ColouredPainting`), and inflations of `χ`-coloured paintings
  (`IsColouredInflation`, `IsColouredLinearInflation`).
- Section 4: bad sequences (`IsBadSequence`, `ColourScheme.IsBad`), capped surfaces
  (`IsCappedSurface`), surface orientations and similarly oriented sequences
  (`SurfaceOrientation`, `IsOrientableSurface`, `IsSimilarlyOriented`,
  `ColourScheme.IsOrientedlyBad`), sub-ideals of quasi-orders (`QuasiOrder.IsSubIdeal`,
  `QuasiOrder.IsStrictSubIdeal`), refinements (`ColourScheme.IsRefinement`), and the induction
  hypotheses `S₁`–`S₄` (`ConditionS1`, `ConditionS2`, `ConditionS3`, `ConditionS4`).
- Section 5: `Φ`-preserving homeomorphisms (`IsFramePreservingHomeo`), features (`IsFeature`,
  `FeatureEquiv`), cutting along a feature (`IsCuttingFragment`), 2-cell paintings
  (`Painting.IsTwoCell`), radial drawings (`IsPreRadial`, `RadialDrawing`, with
  `RadialDrawing.isRadialDrawing` proving `GM11.PaintingOrDrawing.IsRadialDrawing`), `R*`, the
  poles and the atom of a vertex (`RadialDrawing.Rstar`, `RadialDrawing.poles`,
  `RadialDrawing.atomOf`), `dist(Γ)` (`Painting.dist`), and `rep(Γ)` (`Painting.rep`).
- Section 6: `rep(G)` for drawings (`Drawing.rep`), isomorphism of drawings
(`Drawing.IsIsomorphic`),
  enlargements of drawings (`IsEnlargement`), and blocks (`Drawing.IsBlock`).
- Section 7: the hypergraph of a painting (`Painting.toHypergraph`) and its restriction
  (`Painting.restrict`), using the shared `Hypergraph S (Set S)`, `Hypergraph.IsSeparation`, and
  `GM10.IsTangle`; `rep(𝒯)` (`tangleRep`), `ins(F)` and `out(F)` (`IsInsOf`, `IsOutOf`), atoms
  (`Painting.atoms`), `ins(W)` (`ClosedWalkIns`), and the tangle metric `d` (`tangleMetric`).
- Section 8: splitting an edge of `Γ*` (`RadialDrawing.Splits`), tie-breakers (`TieBreaker`), the
  `λ`-order (`TieBreaker.lambdaOrder`), `𝒯`-enclaves (`IsEnclaveAround`, `IsEnclave`), `λ`-linked
  circuits (`IsLambdaLinkedCircuit`), arms (`Arm`), rooted locations (`RootedLocation`), and
  `θ`-isolation (`RootedLocation.Isolates`). Distinctions and `λ`-linked separations are those of
  Graph Minors X and XVIII, `GM10.IsDistinction` and `GM18.IsLambdaLinkedTo`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Function Topology GraphMinor.Surface GraphMinor.Hypergraph GraphMinor.GM11

universe u w

variable {S : Type u} [TopologicalSpace S]

/-! ### Section 2: Drawings, regions, and normal subsets -/

/-- A drawing `G` in a surface `Σ` in Graph Minors XIX is a `Surface.Drawing S`. The two extra
conditions required in Graph Minors XIX, Section 2 (page 327) (no loops and each edge contained in
`bd(Σ)` or disjoint from `bd(Σ)`) are expressed by the predicate `Surface.Drawing.IsGM19Drawing`. -/
abbrev Drawing (S : Type u) [TopologicalSpace S] := Surface.Drawing S

namespace Drawing

/-- The two extra conditions on a drawing `G` in a surface `Σ` from Graph Minors XIX, Section 2
(page 327): "A *drawing* $G$ in $\Sigma$ is a pair $(U, V)$, where $U \subseteq \Sigma$ is closed
and $V \subseteq U$ is finite, such that
- $U \setminus V$ has only finitely many arc-wise connected components, called *edges*,
- for each edge $e$, $|\tilde{e}| = 2$, and $\bar{e}$ is a line with ends the two members of
  $\tilde{e}$,
- for each edge $e$, either $e \subseteq bd(\Sigma)$ or $e \cap bd(\Sigma) = \emptyset$." -/
structure IsGM19Drawing (G : Drawing S) : Prop where
  no_loops : ∀ e ∈ G.E, (tilde e).ncard = 2 ∧ (tilde e).Finite ∧
    IsLine (closure e) ∧ lineEnds (closure e) = tilde e
  border_or_disjoint : ∀ e ∈ G.E, e ⊆ bd S ∨ Disjoint e (bd S)

/-- The regions of `G` in `Σ` are the connected components of `Σ \ U(G)` (Graph Minors XIX,
Section 2, page 327: "The components of $\Sigma \setminus U(G)$ are called the *regions* of $G$ in
$\Sigma$"). -/
noncomputable def regions (G : Drawing S) : Set (Set S) := componentsIn G.Uᶜ

/-- The size of a drawing `G` is `|V(G)| + |E(G)|` (Graph Minors XIX, Section 5, page 335:
"The *size* of a drawing $G$ is $|V(G)| + |E(G)|$"). -/
noncomputable def size (G : Drawing S) : ℕ := G.V.ncard + G.E.ncard

/-- A subset `X ⊆ Σ` is `G`-normal if `X ∩ U(G) ⊆ V(G)` (Graph Minors XIX, Section 2, page 328:
"A subset $X \subseteq \Sigma$ is *$\Gamma$-normal* if $X \cap U(\Gamma) \subseteq V(\Gamma)$"). -/
def IsNormal (G : Drawing S) (X : Set S) : Prop := X ∩ G.U ⊆ G.V

/-- The 1-skeleton simple graph of a drawing `G`. -/
def adj (G : Drawing S) : SimpleGraph S where
  Adj x y := x ≠ y ∧ x ∈ G.V ∧ y ∈ G.V ∧ ∃ e ∈ G.E, x ∈ tilde e ∧ y ∈ tilde e
  symm := ⟨fun _ _ ⟨h, hx, hy, e, he, hxe, hye⟩ ↦ ⟨h.symm, hy, hx, e, he, hye, hxe⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- A drawing `C` is a circuit of `G` if `C` is a subdrawing of `G` and a circuit in the sense of
Graph Minors XI, Section 4 (page 79). -/
def IsCircuitOf (C G : Drawing S) : Prop :=
  C.IsSubdrawing G ∧ C.IsCircuit

/-- A drawing `P` is a path of `G` between `u` and `v` if `P` is a subdrawing of `G` and a path in
the sense of Graph Minors XI, Section 4 (page 79). A path may have one vertex, and then `u = v`. -/
def IsPathOf (P G : Drawing S) (u v : S) : Prop :=
  P.IsSubdrawing G ∧ P.IsPathBetween u v

end Drawing

export Drawing (IsGM19Drawing IsCircuitOf IsPathOf)

namespace Surface.Drawing

export GM19.Drawing (IsGM19Drawing regions size adj IsCircuitOf IsPathOf)

end Surface.Drawing

namespace Painting

/-- The regions of a painting `Γ` in `Σ` are the connected components of `Σ \ U(Γ)` (Graph Minors
XIX, Section 2, page 327: "the connected components of $\Sigma \setminus U$ are the *regions* of
$\Gamma$"). -/
noncomputable def regions (Γ : Painting S) : Set (Set S) := componentsIn Γ.Uᶜ

/-- An edge `e` is internal if `e ∩ bd(Σ) = ∅` (Graph Minors XIX, Section 2, page 327: "an edge $e$
is a *border edge* if $e \cap bd(\Sigma) \ne \emptyset$, and otherwise is
*internal"). -/
def IsInternal (e : Set S) : Prop := Disjoint e (bd S)

/-- A subset `X ⊆ Σ` is `Γ`-normal if `X ∩ U(Γ) ⊆ V(Γ)` (Graph Minors XIX, Section 2, page 328:
"A subset $X \subseteq \Sigma$ is *$\Gamma$-normal* if $X \cap U(\Gamma) \subseteq V(\Gamma)$"). -/
def IsNormal (Γ : Painting S) (X : Set S) : Prop := X ∩ Γ.U ⊆ Γ.V

/-- The point set `U(sk(Γ))` of the 1-skeleton drawing `sk(Γ)` (Graph Minors XIX, Section 2,
page 327). -/
def skU (Γ : Painting S) : Set S :=
  Γ.V ∪ (⋃ e ∈ {e ∈ Γ.E | (tilde e).ncard = 2}, e) ∪
    (⋃ e ∈ {e ∈ Γ.E | (tilde e).ncard = 3}, discBd (closure e))

/-- Conversion from `GM19.Painting` to `Surface.Painting` when every edge of `Γ` has closure a
closed disc with `closure e ∩ V(Γ) ⊆ subBd (closure e)` (for instance, when every edge of `Γ` has
size 3, or after 2-ended line edges are thickened into closed discs).
Note on the difference between `GM19.Painting` (Graph Minors XIX, Section 2, page 327) and
`Surface.Painting` (Graph Minors XI, Section 3, page 75): in Graph Minors XI, every cell `e` has
closure `ē` a closed disc (even when `|eTilde| = 2`), whereas in Graph Minors XIX, an edge `e` with
`|eTilde| = 2` has closure `ē` a line (`[0, 1]`-arc) and an edge `e` with `|eTilde| = 3` has closure
`ē` a
closed disc. -/
def toSurfacePainting (Γ : Painting S)
    (hdisc : ∀ e ∈ Γ.E, IsClosedDisc (closure e) ∧ closure e ∩ Γ.V ⊆ subBd (closure e)) :
    Surface.Painting S where
  U := Γ.U
  V := Γ.V
  V_subset_U := Γ.V_subset
  finite_V := Γ.finite_V
  finite_edges := Γ.finite_edges
  edge_cond := hdisc

/-- Conversion from `GM19.Painting` to `GM11.PaintingOrDrawing` via `Painting.toSurfacePainting`. -/
def toPaintingOrDrawing (Γ : Painting S)
    (hdisc : ∀ e ∈ Γ.E, IsClosedDisc (closure e) ∧ closure e ∩ Γ.V ⊆ subBd (closure e)) :
    PaintingOrDrawing S :=
  PaintingOrDrawing.painting (Γ.toSurfacePainting hdisc)

/-- The hypergraph `(V(Γ), E(Γ))` of a painting `Γ` (Graph Minors XIX, Section 7, page 344:
"If $\Gamma$ is a painting then $(V(\Gamma), E(\Gamma))$ (with the natural incidence
relation) is a hypergraph, and to avoid proliferating notation we shall also call this
hypergraph $\Gamma$"). -/
def toHypergraph (Γ : Painting S) : Hypergraph S (Set S) where
  vertexSet := Γ.V
  edgeSet := Γ.E
  Inc e v := e ∈ Γ.E ∧ v ∈ Γ.V ∧ v ∈ tilde e
  vertex_mem_of_inc _ _ h := h.2.1
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := Γ.finite_V
  edgeSet_finite := Γ.finite_edges

/-- The restriction `Γ ∩ Δ` of a painting `Γ` to a subset `Δ ⊆ Σ`, as a subhypergraph of
`Γ.toHypergraph` (Graph Minors XIX, Section 7, page 344). -/
def restrict (Γ : Painting S) (Δ : Set S) : Hypergraph S (Set S) where
  vertexSet := Γ.V ∩ Δ
  edgeSet := {e ∈ Γ.E | e ⊆ Δ ∧ tilde e ∩ Γ.V ⊆ Δ}
  Inc e v := (e ∈ Γ.E ∧ e ⊆ Δ ∧ tilde e ∩ Γ.V ⊆ Δ) ∧ v ∈ Γ.V ∧ v ∈ tilde e
  vertex_mem_of_inc _ _ h := ⟨h.2.1, h.1.2.2 ⟨h.2.2, h.2.1⟩⟩
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := Γ.finite_V.subset inter_subset_left
  edgeSet_finite := Γ.finite_edges.subset fun _ he ↦ he.1

theorem restrict_le (Γ : Painting S) (Δ : Set S) : Γ.restrict Δ ≤ Γ.toHypergraph where
  vertexSet_subset := inter_subset_left
  edgeSet_subset _ he := he.1
  ends_eq _ he := by
    ext v
    simp only [Hypergraph.ends, restrict, toHypergraph]
    exact ⟨fun h ↦ ⟨he, h.2.1, h.2.2⟩, fun h ↦ ⟨he.1, h.2.1, h.2.2⟩⟩

end Painting

/-! ### Section 3: Frames and colour schemes -/

/-- The direction of an edge `e ⊆ s` defined by `γe` agrees with the direction of `s` defined by
`γs` (Graph Minors XIX, Section 3, page 329: "the tail of $e$ precedes its head as $S$ is traversed
from its tail in $\Phi$ to its head
(that is, briefly, the direction of $e$ defined by $\gamma_\Gamma(e)$ agrees with the
direction of $S$ in $\Phi$)"). -/
def DirAgrees (s : Set S) (γs : List S) (e : Set S) (γe : List S) : Prop :=
  ∃ (f : Icc (0 : ℝ) 1 ≃ₜ closure s) (t₁ t₂ : Icc (0 : ℝ) 1),
    t₁ < t₂ ∧ e ⊆ s ∧
    γs.head? = some (f ⟨0, left_mem_Icc.mpr zero_le_one⟩).1 ∧
    γs.getLast? = some (f ⟨1, right_mem_Icc.mpr zero_le_one⟩).1 ∧
    γe.head? = some (f t₁).1 ∧
    γe.getLast? = some (f t₂).1

/-- A frame `Φ` in `Σ` (Graph Minors XIX, Section 3, page 329): "A *frame $\Phi$ in $\Sigma$*
consists of a directed drawing in $\Sigma$ (which we also
denote by $\Phi$) with $U(\Phi)=bd(\Sigma)$, together with a designation of each edge of
$\Phi$ as *long* or *short*, such that no two long edges have a common end. We call the
edges of $\Phi$ the *sides* of the frame." -/
structure Frame (S : Type u) [TopologicalSpace S] where
  /-- The vertex set `V(Φ) ⊆ bd(Σ)`. -/
  V : Set S
  /-- The direction march `γ(S)` of each side `S` of `Φ`. -/
  γ : Set S → List S
  /-- Predicate designating whether a side `S` is long (short otherwise). -/
  isLong : Set S → Prop
  V_subset : V ⊆ bd S
  finite_V : V.Finite
  finite_sides : (arcComponentsIn (bd S \ V)).Finite
  side_shape : ∀ s ∈ arcComponentsIn (bd S \ V),
    (tilde s).ncard = 2 ∧ (tilde s).Finite ∧ IsLine (closure s) ∧ lineEnds (closure s) = tilde s
  γ_nodup : ∀ s ∈ arcComponentsIn (bd S \ V), (γ s).Nodup
  γ_set : ∀ s ∈ arcComponentsIn (bd S \ V), {v | v ∈ γ s} = tilde s
  long_disjoint : ∀ s₁ ∈ arcComponentsIn (bd S \ V), ∀ s₂ ∈ arcComponentsIn (bd S \ V),
    s₁ ≠ s₂ → isLong s₁ → isLong s₂ → Disjoint (tilde s₁) (tilde s₂)

namespace Frame

/-- The set `E(Φ)` of sides of a frame `Φ` (Graph Minors XIX, Section 3, page 329). -/
def sides (Φ : Frame S) : Set (Set S) := arcComponentsIn (bd S \ Φ.V)

/-- The set of long sides of a frame `Φ` (Graph Minors XIX, Section 3, page 329). -/
def longSides (Φ : Frame S) : Set (Set S) := {s ∈ Φ.sides | Φ.isLong s}

/-- The set of short sides of a frame `Φ` (Graph Minors XIX, Section 3, page 329). -/
def shortSides (Φ : Frame S) : Set (Set S) := {s ∈ Φ.sides | ¬ Φ.isLong s}

end Frame

/-- A painting `Γ` in `Σ` fits a frame `Φ` (Graph Minors XIX, Section 3, page 329):
"A *painting $\Gamma$ in $\Sigma$* is said to *fit a frame $\Phi$* if
- $V(\Phi)\subseteq V(\Gamma)$,
- each short side of $\Phi$ is an edge of $\Gamma$,
- for every border edge $e$ of $\Gamma$, if $S$ is the side of $\Phi$ with $e\subseteq S$ then the
  tail of $e$ precedes its head as $S$ is traversed from its tail in $\Phi$ to its head (that is,
  briefly, the direction of $e$ defined by $\gamma_\Gamma(e)$ agrees with the direction of $S$ in
  $\Phi$),
- $\Gamma$ is internally 3-connected,
- if $e\in E(\Gamma)$ and $|\tilde{e}|=3$ and $r$ is a region of $\Gamma$ in $\Sigma$ with
  $|\bar{r}\cap V(\Gamma)|\ge 3$, then $\bar{f}\cap bd(\Sigma)\ne \emptyset$ for every component
  $f$ of $e\cap \bar{r}$." -/
structure Painting.Fits (Γ : Painting S) (Φ : Frame S) : Prop where
  V_subset : Φ.V ⊆ Γ.V
  short_sides : Φ.shortSides ⊆ Γ.E
  border_dir : ∀ e ∈ Γ.E, Painting.IsBorder e → ∀ s ∈ Φ.sides, e ⊆ s →
    DirAgrees s (Φ.γ s) e (Γ.γ e)
  internally_three_connected : Γ.IsInternallyThreeConnected
  size_three_region : ∀ e ∈ Γ.E, (tilde e).ncard = 3 → ∀ r ∈ Γ.regions,
    3 ≤ (closure r ∩ Γ.V).ncard → ∀ f ∈ componentsIn (e ∩ closure r),
      (closure f ∩ bd S).Nonempty

/-- A border edge `e` of `Γ` borders a side `S` of `Φ` if `e ⊆ S` (Graph Minors XIX, Section 3,
page 329: "If $e$ is a border edge of $\Gamma$ and $S$ is a side of $\Phi$ with $e\subseteq S$, we
say
that $e$ *borders $S$"). -/
def BordersSide (e s : Set S) : Prop := Painting.IsBorder e ∧ e ⊆ s

/-- An inflation `σ` of `Γ` in `Γ'` respects a frame `Φ` (Graph Minors XIX, Section 3, page 329):
"we say that $\sigma$ *respects $\Phi$* if for every border edge $e$ of $\Gamma$, $\sigma(e)$
is a border edge and $e$ and $\sigma(e)$ border the same side of $\Phi$." -/
def RespectsFrame (Φ : Frame S) (Γ : Painting S) (σe : Set S → Set S) : Prop :=
  ∀ e ∈ Γ.E, Painting.IsBorder e →
    Painting.IsBorder (σe e) ∧ ∀ s ∈ Φ.sides, e ⊆ s ↔ σe e ⊆ s

/-- A quasi-order `Ω` with element set `E(Ω)` and reflexive, transitive relation `≤` (Graph Minors
XIX, Section 2, page 328: "A *quasi-order* $\Omega$ consists of a set $E(\Omega)$ and a reflexive,
transitive relation
$\le$"). -/
structure QuasiOrder (α : Type w) where
  /-- The element set `E(Ω)`. -/
  E : Set α
  /-- The quasi-order relation `≤`. -/
  le : α → α → Prop
  refl : ∀ x ∈ E, le x x
  trans : ∀ x ∈ E, ∀ y ∈ E, ∀ z ∈ E, le x y → le y z → le x z

namespace QuasiOrder

variable {α : Type w}

/-- A quasi-order `Ω` is a well-quasi-order if for every countable sequence `ω_i` of elements of
`E(Ω)` there exist `j > i` such that `ω_i ≤ ω_j` (Graph Minors XIX, Section 2, page 328: "It is a
*well-quasi-order* if for every countable sequence $\omega_i$ ($i = 1, 2, \dots$) of
elements of $E(\Omega)$ there exist $j > i \ge 1$ such that $\omega_i \le \omega_j$"). -/
def IsWQO (Ω : QuasiOrder α) : Prop :=
  ∀ f : ℕ → α, (∀ i, f i ∈ Ω.E) → ∃ i j, i < j ∧ Ω.le (f i) (f j)

/-- The `QuasiOrder` on a type `α` equipped with a `[Preorder α]` and element set `Set.univ`. -/
def ofPreorder (α : Type w) [Preorder α] : QuasiOrder α where
  E := univ
  le := (· ≤ ·)
  refl x _ := le_refl x
  trans _ _ _ _ _ _ h₁ h₂ := le_trans h₁ h₂

/-- `ofPreorder α` is a well-quasi-order in the sense of `QuasiOrder.IsWQO` if and only if
`WellQuasiOrderedLE α` holds. -/
theorem isWQO_ofPreorder_iff (α : Type w) [Preorder α] :
    (ofPreorder α).IsWQO ↔ WellQuasiOrderedLE α := by
  constructor
  · intro h
    refine ⟨fun f ↦ h f (fun _ ↦ mem_univ _)⟩
  · intro h f _
    exact h.wqo f

/-- The `Preorder` on the subtype `↑Ω.E` induced by a `QuasiOrder α`. -/
@[instance_reducible]
def toSubtypePreorder (Ω : QuasiOrder α) : Preorder Ω.E where
  le x y := Ω.le x.1 y.1
  le_refl x := Ω.refl x.1 x.2
  le_trans x y z h₁ h₂ := Ω.trans x.1 x.2 y.1 y.2 z.1 z.2 h₁ h₂

/-- A `QuasiOrder` `Ω` satisfies `Ω.IsWQO` if and only if the induced preorder on `↑Ω.E` satisfies
`WellQuasiOrderedLE`. -/
theorem isWQO_iff_wellQuasiOrderedLE (Ω : QuasiOrder α) :
    Ω.IsWQO ↔ @WellQuasiOrderedLE Ω.E Ω.toSubtypePreorder.toLE := by
  let _ : Preorder Ω.E := Ω.toSubtypePreorder
  constructor
  · intro h
    refine ⟨fun f ↦ ?_⟩
    obtain ⟨i, j, hij, hle⟩ := h (fun n ↦ (f n).1) (fun n ↦ (f n).2)
    exact ⟨i, j, hij, hle⟩
  · intro h f hf
    obtain ⟨i, j, hij, hle⟩ := h.wqo (fun n ↦ ⟨f n, hf n⟩)
    exact ⟨i, j, hij, hle⟩

/-- `Ω' ≼ Ω` for quasi-orders `Ω, Ω'` (Graph Minors XIX, Section 4, page 332):
"If $\Omega,\Omega'$ are quasi-orders we write $\Omega'\preceq \Omega$ if
- $E(\Omega')\subseteq E(\Omega)$,
- for each $x'\in E(\Omega')$ and $x\in E(\Omega)$, if $x\le x'$ in $\Omega$ then
  $x\in E(\Omega')$, and
- for $x_1,x_2\in E(\Omega')$, $x_1\le x_2$ in $\Omega'$ if and only if $x_1\le x_2$ in
  $\Omega$." -/
structure IsSubIdeal (Ω' Ω : QuasiOrder α) : Prop where
  E_subset : Ω'.E ⊆ Ω.E
  downward_closed : ∀ x' ∈ Ω'.E, ∀ x ∈ Ω.E, Ω.le x x' → x ∈ Ω'.E
  le_iff : ∀ x₁ ∈ Ω'.E, ∀ x₂ ∈ Ω'.E, Ω'.le x₁ x₂ ↔ Ω.le x₁ x₂

/-- `Ω' ≺ Ω` if `Ω' ≼ Ω` and `Ω' ≠ Ω` (Graph Minors XIX, Section 4, page 332:
"We write $\Omega'\prec \Omega$ if $\Omega'\preceq \Omega$ and $\Omega'\ne \Omega$"). -/
def IsStrictSubIdeal (Ω' Ω : QuasiOrder α) : Prop :=
  IsSubIdeal Ω' Ω ∧ Ω'.E ≠ Ω.E

end QuasiOrder

/-- A colour scheme `χ` on a surface `S` with label carrier `α` (Graph Minors XIX, Section 3,
page 329): "A *colour scheme $\chi$* consists of a surface $\Sigma_\chi$, a frame $\Phi_\chi$ in
$\Sigma_\chi$, two well-quasi-orders $\Omega_\chi(2)$ and $\Omega_\chi(3)$, and a
well-quasi-order $\Omega_\chi(S)$ for each side $S$ of $\Phi_\chi$, such that
$E(\Omega_\chi(S))=\{S\}$ for every short side $S$." -/
structure ColourScheme (S : Type u) [TopologicalSpace S] (α : Type w) where
  isSurface : IsSurface S
  connected : ConnectedSpace S
  /-- The frame `Φ_χ` in `Σ_χ`. -/
  Φ : Frame S
  /-- The well-quasi-order `Ω_χ(2)`. -/
  Ω2 : QuasiOrder α
  /-- The well-quasi-order `Ω_χ(3)`. -/
  Ω3 : QuasiOrder α
  /-- The well-quasi-order `Ω_χ(S)` for each side `S` of `Φ_χ`. -/
  ΩS : Set S → QuasiOrder α
  /-- The representative element for each short side `S` of `Φ_χ`. -/
  shortElem : Set S → α
  isWQO_2 : Ω2.IsWQO
  isWQO_3 : Ω3.IsWQO
  isWQO_S : ∀ s ∈ Φ.sides, (ΩS s).IsWQO
  short_singleton : ∀ s ∈ Φ.shortSides, (ΩS s).E = {shortElem s}

/-- A `χ`-coloured painting `(Γ, φ)` (Graph Minors XIX, Section 3, page 329):
"If $\chi$ is a colour scheme, a *$\chi$-coloured painting* is a pair $(\Gamma,\phi)$, where
- $\Gamma$ is a painting in $\Sigma_\chi$ fitting the frame $\Phi_\chi$,
- $\phi$ is a function with domain $E(\Gamma)$, such that if $e\in E(\Gamma)$ is internal then
  $\phi(e)\in \Omega_\chi(|\tilde{e}|)$, and if $e$ borders a side $S$ then
  $\phi(e)\in \Omega_\chi(S)$." -/
structure ColouredPainting {α : Type w} (χ : ColourScheme S α) where
  /-- The underlying painting `Γ`. -/
  Γ : Painting S
  /-- The edge-labelling function `φ`. -/
  φ : Set S → α
  fits : Γ.Fits χ.Φ
  internal_2_mem : ∀ e ∈ Γ.E, Painting.IsInternal e → (tilde e).ncard = 2 → φ e ∈ χ.Ω2.E
  internal_3_mem : ∀ e ∈ Γ.E, Painting.IsInternal e → (tilde e).ncard = 3 → φ e ∈ χ.Ω3.E
  border_mem : ∀ e ∈ Γ.E, ∀ s ∈ χ.Φ.sides, BordersSide e s → φ e ∈ (χ.ΩS s).E

/-- An inflation of `(Γ, φ)` in `(Γ', φ')` for `χ`-coloured paintings (Graph Minors XIX,
Section 3, page 330): "If $(\Gamma,\phi),(\Gamma',\phi')$ are $\chi$-coloured paintings, an
*inflation of $(\Gamma,\phi)$ in $(\Gamma',\phi')$* is an inflation $\sigma$ of $\Gamma$ in
$\Gamma'$ respecting $\Phi_\chi$, such that $\phi\le \phi'\circ \sigma$ (with the natural
meaning); and *linear inflations* are defined similarly." -/
structure IsColouredInflation {α : Type w} (χ : ColourScheme S α)
    (P P' : ColouredPainting χ) (σv : S → Set S) (σe : Set S → Set S) : Prop where
  isInflation : IsInflation P.Γ P'.Γ σv σe
  respects : RespectsFrame χ.Φ P.Γ σe
  le_internal_2 : ∀ e ∈ P.Γ.E, Painting.IsInternal e → (tilde e).ncard = 2 →
    χ.Ω2.le (P.φ e) (P'.φ (σe e))
  le_internal_3 : ∀ e ∈ P.Γ.E, Painting.IsInternal e → (tilde e).ncard = 3 →
    χ.Ω3.le (P.φ e) (P'.φ (σe e))
  le_border : ∀ e ∈ P.Γ.E, ∀ s ∈ χ.Φ.sides, BordersSide e s →
    (χ.ΩS s).le (P.φ e) (P'.φ (σe e))

/-- A linear inflation of `(Γ, φ)` in `(Γ', φ')` for `χ`-coloured paintings (Graph Minors XIX,
Section 3, page 330). -/
structure IsColouredLinearInflation {α : Type w} (χ : ColourScheme S α)
    (P P' : ColouredPainting χ) (σv : S → Set S) (σe : Set S → Set S) : Prop
    extends IsColouredInflation χ P P' σv σe where
  isLinear : IsLinearInflation P.Γ P'.Γ σv σe

/-! ### Section 4: The induction -/

/-- A bad sequence for a colour scheme `χ` (Graph Minors XIX, Section 4, page 332):
"A bad sequence for a colour scheme $\chi$ is a countable sequence $(\Gamma_i,\phi_i)$
$(i=1,2,\dots)$ of $\chi$-coloured paintings, such that for all $j>i\ge 1$ there is no
linear inflation of $(\Gamma_i,\phi_i)$ in $(\Gamma_j,\phi_j)$." -/
def IsBadSequence {α : Type w} (χ : ColourScheme S α) (P : ℕ → ColouredPainting χ) : Prop :=
  ∀ i j, i < j → ¬ ∃ σv σe, IsColouredLinearInflation χ (P i) (P j) σv σe

/-- A colour scheme `χ` is bad if there is a bad sequence for it (Graph Minors XIX, Section 4,
page 332: "We say that a colour scheme is bad if there is a bad sequence for it"). -/
def ColourScheme.IsBad {α : Type w} (χ : ColourScheme S α) : Prop :=
  ∃ P : ℕ → ColouredPainting χ, IsBadSequence χ P

/-- `Shat` is the capped surface `Σ̂` obtained from `S` by pasting a closed disc onto each cuff of
`S` (Graph Minors XIX, Section 2, page 327: The surface obtained from $\Sigma$ by "pasting" a disc
onto each cuff we denote by $\hat{\Sigma}$). -/
structure IsCappedSurface (S : Type u) [TopologicalSpace S]
    (Shat : Type u) [TopologicalSpace Shat] where
  isSurface : IsSurface Shat
  connected : ConnectedSpace Shat
  bd_empty : bd Shat = ∅
  /-- The embedding of `S` into `Shat`. -/
  emb : S → Shat
  isEmbedding : Topology.IsEmbedding emb
  /-- For each cuff `Θ` of `S`, the pasted open disc `r(Θ)` in `Shat \ emb(S)`. -/
  cuffDisc : Set S → Set Shat
  cuffDisc_closedDisc : ∀ Θ ∈ cuffs S, IsClosedDisc (closure (cuffDisc Θ))
  cuffDisc_bd : ∀ Θ ∈ cuffs S, discBd (closure (cuffDisc Θ)) = emb '' Θ
  cuffDisc_disjoint : ∀ Θ₁ ∈ cuffs S, ∀ Θ₂ ∈ cuffs S, Θ₁ ≠ Θ₂ →
    Disjoint (closure (cuffDisc Θ₁)) (closure (cuffDisc Θ₂))
  compl_eq : (range emb)ᶜ = ⋃ Θ ∈ cuffs S, cuffDisc Θ

/-- The positive cyclic order of three points of the circle: going around from `a` in the positive
direction, we reach `b` before `c`, and both before coming back to `a`. -/
def CircleCyclic (a b c : Circle) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ s < t ∧ t < 2 * Real.pi ∧ b = a * Circle.exp s ∧ c = a * Circle.exp t

/-- An orientation `ω` of a surface `S` (Graph Minors XIX, Section 4, page 332). The paper uses
orientations as usual. An orientation assigns to each closed disc `Δ ⊆ S` a cyclic order of
`bd(Δ)`, that is, one of the two directions of this `O`-arc, and these must agree: if
`Δ₁ ⊆ Δ₂`, then the two cyclic orders agree on each triple of common boundary points.

A Möbius band has no orientation. To compare a closed disc `D` with a closed disc `Δ` that includes
it in its interior, thicken `D` along three disjoint arcs to `bd(Δ)`. The result is a closed disc
`D' ⊆ Δ` that has three boundary points in common with `Δ` and three with `D`. So any two closed
discs that overlap are compared, and going around the core of the band reverses the direction. -/
structure SurfaceOrientation (S : Type u) [TopologicalSpace S] where
  /-- `pos Δ a b c` says that `a, b, c ∈ bd(Δ)` occur in this cyclic order under `ω`. -/
  pos : Set S → S → S → S → Prop
  /-- The relation on `bd(Δ)` is a direction of the `O`-arc `bd(Δ)`. -/
  isDirection : ∀ Δ : Set S, IsClosedDisc Δ → ∃ φ : Circle → S,
    Continuous φ ∧ Function.Injective φ ∧ range φ = discBd Δ ∧
      ∀ a b c : Circle, a ≠ b → b ≠ c → a ≠ c → (pos Δ (φ a) (φ b) (φ c) ↔ CircleCyclic a b c)
  /-- Nested discs have the same direction on common boundary points. -/
  agree : ∀ Δ₁ Δ₂ : Set S, IsClosedDisc Δ₁ → IsClosedDisc Δ₂ → Δ₁ ⊆ Δ₂ → ∀ a b c : S,
    a ∈ discBd Δ₁ ∩ discBd Δ₂ → b ∈ discBd Δ₁ ∩ discBd Δ₂ → c ∈ discBd Δ₁ ∩ discBd Δ₂ →
    a ≠ b → b ≠ c → a ≠ c → (pos Δ₁ a b c ↔ pos Δ₂ a b c)

/-- `f` preserves the orientation `ω`: it carries the cyclic order of each closed disc to the cyclic
order of its image. -/
def SurfaceOrientation.IsPreservedBy (ω : SurfaceOrientation S) (f : S ≃ₜ S) : Prop :=
  ∀ Δ : Set S, IsClosedDisc Δ → ∀ a b c : S, a ∈ discBd Δ → b ∈ discBd Δ → c ∈ discBd Δ →
    a ≠ b → b ≠ c → a ≠ c → (ω.pos (f '' Δ) (f a) (f b) (f c) ↔ ω.pos Δ a b c)

/-- A surface `S` is orientable if it has an orientation (Graph Minors XIX, Section 4, page 332). -/
def IsOrientableSurface (S : Type u) [TopologicalSpace S] : Prop :=
  Nonempty (SurfaceOrientation S)

/-- A family of `χ`-coloured paintings is similarly oriented (Graph Minors XIX, Section 4,
page 332): "A set $\{(\Gamma_i,\phi_i):i\in I\}$ of $\chi$-coloured paintings is said to be
*similarly oriented* if either $\Sigma_\chi$ is not orientable, or there is an orientation $\omega$
of $\Sigma_\chi$ such that for all $i\in I$ and every $e\in E(\Gamma_i)$ with $|\tilde{e}|=3$, the
orientations of $e$ given by $\omega$ and given by the cyclic order of the terms of
$\gamma_{\Gamma_i}(e)$ coincide." The orientation of `e` given by `ω` is
the cyclic order of `bd(ē)`. -/
def IsSimilarlyOriented {α : Type w} (χ : ColourScheme S α)
    (P : ℕ → ColouredPainting χ) : Prop :=
  ¬ IsOrientableSurface S ∨
    ∃ ω : SurfaceOrientation S,
      ∀ i, ∀ e ∈ (P i).Γ.E, (tilde e).ncard = 3 → ∀ a b c : S, (P i).Γ.γ e = [a, b, c] →
        ω.pos (closure e) a b c

/-- A colour scheme `χ` is orientedly bad if there is a similarly oriented bad sequence for it
(Graph Minors XIX, Section 4, page 332: "A colour scheme $\chi$ is *orientedly bad* if there is a
similarly oriented bad sequence for
it"). -/
def ColourScheme.IsOrientedlyBad {α : Type w} (χ : ColourScheme S α) : Prop :=
  ∃ P : ℕ → ColouredPainting χ, IsBadSequence χ P ∧ IsSimilarlyOriented χ P

/-- The number of cuffs `c(Σ)` of a surface `Σ` (Graph Minors XIX, Section 4, page 332:
"We denote the number of cuffs of a surface $\Sigma$ by $c(\Sigma)$"). -/
noncomputable def numCuffs (S : Type u) [TopologicalSpace S] : ℕ := (cuffs S).ncard

/-- `χ'` is a refinement of `χ` via embedding `f` (Graph Minors XIX, Section 4, page 332):
"We say that $\chi'$ is a *refinement* of $\chi$ if $\Sigma_{\chi'}\cong \Sigma_\chi$,
$\Omega_{\chi'}(k) = \Omega_\chi(k)$ $(k = 2,3)$, and there is a function $f$ from the set of long
sides of $\Phi_{\chi'}$ to the set of long sides of $\Phi_\chi$, such that
- $\Omega_{\chi'}(R)\preceq \Omega_\chi(f(R))$ for each long side $R$ of $\Phi_{\chi'}$,
- if $R_1,R_2$ are distinct long sides of $\Phi_{\chi'}$ with $f(R_1) = f(R_2)$ then
  $\Omega_{\chi'}(R_1)\prec \Omega_\chi(f(R_1))$,
- if for each long side $S$ of $\Phi_\chi$ there is a long side $R$ of $\Phi_{\chi'}$ with
  $f(R) = S$ and $\Omega_{\chi'}(R) = \Omega_\chi(S)$, then $\Phi_{\chi'}$ has fewer short sides
  then $\Phi_\chi$.
In this case, we call $f$ an *embedding* of $\chi'$ in $\chi$." -/
def ColourScheme.IsRefinement {S₁ S₂ : Type u} [TopologicalSpace S₁] [TopologicalSpace S₂]
    {α : Type w} (χ' : ColourScheme S₁ α) (χ : ColourScheme S₂ α) : Prop :=
  Nonempty (S₁ ≃ₜ S₂) ∧ χ'.Ω2 = χ.Ω2 ∧ χ'.Ω3 = χ.Ω3 ∧
    ∃ f : Set S₁ → Set S₂,
      MapsTo f χ'.Φ.longSides χ.Φ.longSides ∧
      (∀ R ∈ χ'.Φ.longSides, (χ'.ΩS R).IsSubIdeal (χ.ΩS (f R))) ∧
      (∀ R₁ ∈ χ'.Φ.longSides, ∀ R₂ ∈ χ'.Φ.longSides, R₁ ≠ R₂ → f R₁ = f R₂ →
        (χ'.ΩS R₁).IsStrictSubIdeal (χ.ΩS (f R₁))) ∧
      ((∀ s ∈ χ.Φ.longSides, ∃ R ∈ χ'.Φ.longSides, f R = s ∧ (χ'.ΩS R).E = (χ.ΩS s).E) →
        χ'.Φ.shortSides.ncard < χ.Φ.shortSides.ncard)

/-- Statement `S₁` (Graph Minors XIX, Section 4, page 332):
"$\mathbf{S}_1$ *There is no bad colour scheme $\chi'$ with $\hat{\Sigma}_{\chi'}$ simpler than
$\hat{\Sigma}_\chi$.*"
`Shat` is `Σ̂_χ`. "Simpler" is `Surface.IsSimplerThan` for surfaces without boundary (Graph Minors
XVII, Section 1, page 164). With no cuffs it reads as follows: the Euler genus `2a + b` grows, and
an orientable surface comes only from an orientable one. These are the surfaces obtained "by adding
at least one handle or crosscap". The surface `Σ_{χ'}` and its labels are quantified over all
types, since the paper puts no bound on them. -/
def ConditionS1 (Shat : Type u) [TopologicalSpace Shat] : Prop :=
  ∀ (S' Shat' : Type u) [TopologicalSpace S'] [TopologicalSpace Shat'] (β : Type w)
    (χ' : ColourScheme S' β), Nonempty (IsCappedSurface S' Shat') →
    IsSimplerThan Shat' Shat → ¬ χ'.IsBad

/-- Statement `S₂` (Graph Minors XIX, Section 4, page 332):
"$\mathbf{S}_2$ *There is no orientedly bad colour scheme $\chi'$ with
$\hat{\Sigma}_{\chi'}\cong \hat{\Sigma}_\chi$ such that
$\Omega_{\chi'}(3)\preceq \Omega_\chi(3)$ and $\Omega_{\chi'}(2)\preceq \Omega_\chi(2)$ where at
least one of the inclusions is strict.*" -/
def ConditionS2 {Shat : Type u} [TopologicalSpace Shat] {α : Type w} (χ : ColourScheme S α)
    (_ : IsCappedSurface S Shat) : Prop :=
  ∀ (S' Shat' : Type u) [TopologicalSpace S'] [TopologicalSpace Shat']
    (χ' : ColourScheme S' α), Nonempty (IsCappedSurface S' Shat') → Nonempty (Shat' ≃ₜ Shat) →
    χ'.Ω3.IsSubIdeal χ.Ω3 → χ'.Ω2.IsSubIdeal χ.Ω2 →
    (χ'.Ω3.IsStrictSubIdeal χ.Ω3 ∨ χ'.Ω2.IsStrictSubIdeal χ.Ω2) →
    ¬ χ'.IsOrientedlyBad

/-- Statement `S₃` (Graph Minors XIX, Section 4, page 332):
"$\mathbf{S}_3$ *There is no orientedly bad colour scheme $\chi'$ with
$\hat{\Sigma}_{\chi'}\cong \hat{\Sigma}_\chi$, $\Omega_{\chi'}(k) = \Omega_\chi(k)$
$(k = 2,3)$, and $c(\Sigma_{\chi'}) < c(\Sigma_\chi)$.*" -/
def ConditionS3 {Shat : Type u} [TopologicalSpace Shat] {α : Type w} (χ : ColourScheme S α)
    (_ : IsCappedSurface S Shat) : Prop :=
  ∀ (S' Shat' : Type u) [TopologicalSpace S'] [TopologicalSpace Shat']
    (χ' : ColourScheme S' α), Nonempty (IsCappedSurface S' Shat') → Nonempty (Shat' ≃ₜ Shat) →
    χ'.Ω2 = χ.Ω2 → χ'.Ω3 = χ.Ω3 → numCuffs S' < numCuffs S →
    ¬ χ'.IsOrientedlyBad

/-- Statement `S₄` (Graph Minors XIX, Section 4, page 332):
"{S}_4$ *There is no orientedly bad colour scheme which is a refinement of $\chi$." -/
def ConditionS4 {α : Type w} (χ : ColourScheme S α) : Prop :=
  ∀ (S' : Type u) [TopologicalSpace S'] (χ' : ColourScheme S' α),
    χ'.IsRefinement χ → ¬ χ'.IsOrientedlyBad

/-! ### Section 5: Surface homeomorphisms, features, fragments, and radial drawings -/

/-- A homeomorphism `α : Σ ≃ₜ Σ` is `Φ`-preserving (Graph Minors XIX, Section 5, page 335):
"A homeomorphism $\alpha \colon \Sigma \to \Sigma$ is $\Phi$-*preserving* if * $\alpha(v) =
v$ for all $v \in V(\Phi)$, and $\alpha(S) = S$ for all $S \in E(\Phi)$ (and hence $\alpha$
preserves the direction of each side, and maps each cuff onto itself in an
orientation-preserving way) * if $\Sigma$ is orientable then $\alpha$ preserves the
orientation of $\Sigma$." -/
structure IsFramePreservingHomeo (Φ : Frame S) (f : S ≃ₜ S) : Prop where
  fix_V : ∀ v ∈ Φ.V, f v = v
  preserve_sides : ∀ s ∈ Φ.sides, f '' s = s
  preserves_orientation : ∀ ω : SurfaceOrientation S, ω.IsPreservedBy f

/-- A drawing `K` in `Σ` is a feature in `Φ` (Graph Minors XIX, Section 5, page 335):
"A drawing $K$ in $\Sigma$ is a *feature* (in $\Phi$) if $K$ has no border edges and no
isolated vertices, and $U(K) \cap S = \emptyset$ for every short side $S$ of $\Phi$." -/
structure IsFeature (Φ : Frame S) (K : Drawing S) : Prop where
  no_border_edges : ∀ e ∈ K.E, Disjoint e (bd S)
  no_isolated_vertices : ∀ v ∈ K.V, ∃ e ∈ K.E, v ∈ tilde e
  disjoint_short_sides : ∀ s ∈ Φ.shortSides, Disjoint K.U s

/-- Two features `K₁, K₂` in `Φ` are equivalent if there is a `Φ`-preserving homeomorphism mapping
`K₁` to `K₂` (Graph Minors XIX, Section 5, page 335: "Two features $K_1, K_2$ are *equivalent* if
there is a $\Phi$-preserving homeomorphism
$\alpha$ of $\Sigma$ such that $\alpha$ maps $K_1$ to $K_2$"). -/
def FeatureEquiv (Φ : Frame S) (K₁ K₂ : Drawing S) : Prop :=
  ∃ f : S ≃ₜ S, IsFramePreservingHomeo Φ f ∧ f '' K₁.U = K₂.U ∧ f '' K₁.V = K₂.V

/-- A fragment `Σ₁` of `Σ` after cutting along `U(K)` with associated surjection `ψ : Σ₁ → Σ`
(Graph Minors XIX, Section 5, page 335): "If we cut $\Sigma$ along $U(K)$ we obtain one or several
components $\Sigma_1, \dots,
\Sigma_k$ say, which we call *fragments* of $\Sigma$ after cutting along $U(K)$. There is a
natural surjection of $\psi \colon \Sigma_1 \cup \cdots \cup \Sigma_k \to \Sigma$, which we
shall call the *associated surjection*." The interior of `Σ₁` is a component of `Σ \ (bd(Σ) ∪
U(K))`, and `ψ` runs each point of
`bd(Σ₁)` along `bd(Σ) ∪ U(K)`. Finite fibres stop `ψ` from collapsing an arc of `bd(Σ₁)` to a point,
which would give a surface that is not the result of cutting. -/
structure IsCuttingFragment (S : Type u) [TopologicalSpace S] (K : Drawing S)
    (S₁ : Type u) [TopologicalSpace S₁] (ψ : S₁ → S) : Prop where
  isSurface : IsSurface S₁
  connected : ConnectedSpace S₁
  continuous_ψ : Continuous ψ
  injOn_interior : InjOn ψ (bd S₁)ᶜ
  finite_fibres : ∀ x : S, (ψ ⁻¹' {x}).Finite
  maps_interior_disjoint : Disjoint (ψ '' (bd S₁)ᶜ) (bd S ∪ K.U)
  maps_bd : ψ '' (bd S₁) ⊆ bd S ∪ K.U
  interior_component : ψ '' (bd S₁)ᶜ ∈ componentsIn (bd S ∪ K.U)ᶜ

/-- A painting `Γ` in `Σ` is 2-cell if every region of `Γ` in `Σ` is homeomorphic to an open disc
(Graph Minors XIX, Section 5, page 337: "A painting $\Gamma$ in a surface $\Sigma$ is 2-cell if
every region of $\Gamma$ in $\Sigma$
is homeomorphic to an open disc"). -/
def Painting.IsTwoCell (Γ : Painting S) : Prop :=
  ∀ r ∈ Γ.regions, Nonempty (r ≃ₜ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)

/-- The set `U(Γ)` as a subset of `Σ̂`. -/
def Painting.hatU {Shat : Type u} [TopologicalSpace Shat] (cap : IsCappedSurface S Shat)
    (Γ : Painting S) : Set Shat :=
  cap.emb '' Γ.U

/-- The set `V(Γ)` as a subset of `Σ̂`. -/
def Painting.hatV {Shat : Type u} [TopologicalSpace Shat] (cap : IsCappedSurface S Shat)
    (Γ : Painting S) : Set Shat :=
  cap.emb '' Γ.V

/-- The regions of `Γ` in `Σ̂`: the components of `Σ̂ \ U(Γ)` (Graph Minors XIX, Section 5,
page 337). -/
noncomputable def Painting.hatRegions {Shat : Type u} [TopologicalSpace Shat]
  (cap : IsCappedSurface S Shat)
    (Γ : Painting S) : Set (Set Shat) :=
  componentsIn (Γ.hatU cap)ᶜ

/-- Conditions (i)–(iv) of the definition of a radial drawing in Graph Minors XI, Section 3
(page 75), for the point set `U` and the vertex set `V`. For a painting or a drawing `P` of
Graph Minors XI with `U(P) = U` and `V(P) = V` this is `PaintingOrDrawing.IsPreRadialDrawing`
(`isPreRadial_iff`). The definition never looks at the shape of an edge. -/
def IsPreRadial {Shat : Type u} [TopologicalSpace Shat] (U V : Set Shat) (G : Drawing Shat) :
    Prop :=
  U ∩ G.U = V ∧
  V ⊆ G.V ∧
  (∀ r ∈ componentsIn Uᶜ, ∃! w, w ∈ r ∧ w ∈ G.V) ∧
  (∀ w ∈ G.V \ V, ∃ r ∈ componentsIn Uᶜ, w ∈ r) ∧
  (∀ e ∈ G.E, ∃ v ∈ V, ∃ w ∈ G.V \ V, closure e ∩ G.V = {v, w}) ∧
  (∀ e ∈ G.E, ∀ f ∈ G.E, e ≠ f → ∀ v ∈ V, ∀ r ∈ componentsIn Uᶜ, ∀ w ∈ r ∩ G.V,
    closure e ∩ G.V = {v, w} → closure f ∩ G.V = {v, w} →
    ¬ ∃ Δ : Set Shat, IsClosedDisc Δ ∧ Δ ⊆ r ∪ {v} ∧ subBd Δ = closure e ∪ closure f)

/-- A radial drawing `Γ*` in `Σ̂` of a painting `Γ` (Graph Minors XIX, Section 5, page 337):
"A drawing $\Gamma^*$ in $\hat{\Sigma}$ is a *radial drawing* of $\Gamma$ if it satisfies the four
conditions following, where $R^*$ denotes the set of vertices of $\Gamma^*$ that are not in
$V(\Gamma)$:
- $U(\Gamma) \cap U(\Gamma^*) = V(\Gamma) \subseteq V(\Gamma^*)$,
- every region of $\Gamma$ in $\hat{\Sigma}$ contains a unique vertex of $\Gamma^*$,
- $\Gamma^*$ is bipartite, and $(V(\Gamma), R^*)$ is a bipartition of it,
- for every $v \in V(\Gamma)$, the edges of $\Gamma$ and of $\Gamma^*$ incident with $v$ alternate
  in their cyclic order around $v$."

We use the wording of Graph Minors XI, Section 3 (page 75), where the last condition is given
without a cyclic order. Two edges of `Γ*` at `v` that lie in the same corner of a region `r` at `v`
go to the same vertex `r*`, and they bound a disc in `r ∪ {v}`, so `IsPreRadial` allows at most one
edge of `Γ*` in each corner. Maximality gives at least one. Together this is "alternate".

A painting of Graph Minors XIX may have both line edges and disc edges, and such a painting is
neither a `Surface.Painting` (all closures are discs) nor a `Surface.Drawing` (no closure is a
disc), so `PaintingOrDrawing.IsRadialDrawing` cannot be applied to it directly. We therefore state
XI's conditions for the sets `U(Γ), V(Γ)`, and `RadialDrawing.isRadialDrawing` shows that this is
`PaintingOrDrawing.IsRadialDrawing` for every painting or drawing of XI with these sets. -/
structure RadialDrawing {Shat : Type u} [TopologicalSpace Shat]
    (cap : IsCappedSurface S Shat) (Γ : Painting S) where
  /-- The drawing `Γ*` in `Σ̂`. -/
  G : Drawing Shat
  /-- The first four conditions. -/
  isPreRadial : IsPreRadial (Γ.hatU cap) (Γ.hatV cap) G
  /-- `Γ*` is maximal subject to the first four conditions. -/
  maximal : ∀ G' : Drawing Shat, IsPreRadial (Γ.hatU cap) (Γ.hatV cap) G' →
    G.IsSubdrawing G' → G'.IsSubdrawing G

namespace RadialDrawing

variable {Shat : Type u} [TopologicalSpace Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S}

/-- `R*`, the set of vertices of `Γ*` that are not in `V(Γ)` (Graph Minors XIX, Section 5,
page 337). -/
def Rstar (rad : RadialDrawing cap Γ) : Set Shat := rad.G.V \ Γ.hatV cap

/-- The region of `Γ` in `Σ̂` that contains the point `x`, so that `regionOf r*` is `r`. -/
noncomputable def regionOf (_ : RadialDrawing cap Γ) (x : Shat) : Set Shat :=
  connectedComponentIn (Γ.hatU cap)ᶜ x

/-- The poles (Graph Minors XIX, Section 5, page 337): "if $r \nsubseteq \Sigma$ (and hence $r$ is
a component of $\hat{\Sigma} \setminus \Sigma$) we call $r^*$ a *pole*." -/
def poles (rad : RadialDrawing cap Γ) : Set Shat :=
  {w ∈ rad.Rstar | ¬ rad.regionOf w ⊆ range cap.emb}

/-- The atom of `Γ` belonging to a vertex `x` of `Γ*`: `{x}` for `x ∈ V(Γ)`, and the region `r` for
`x = r*`. Graph Minors XIX, Section 7, page 344, writes `d(r₁*, r₂*)` for the distance between
the atoms `r₁, r₂`, since `r*` lies in `r` and atoms are disjoint. -/
noncomputable def atomOf (rad : RadialDrawing cap Γ) (x : Shat) : Set Shat :=
  open Classical in if x ∈ Γ.hatV cap then {x} else rad.regionOf x

/-- `Γ*` is a radial drawing of each painting or drawing of Graph Minors XI with the same sets. -/
theorem isRadialDrawing (rad : RadialDrawing cap Γ) {P : PaintingOrDrawing Shat}
    (hU : P.U = Γ.hatU cap) (hV : P.V = Γ.hatV cap) (h2 : P.IsTwoCell) :
    P.IsRadialDrawing rad.G := by
  have hR : P.R = componentsIn (Γ.hatU cap)ᶜ := by
    rw [← hU, compl_eq_univ_sdiff]
    cases P <;> rfl
  have key : ∀ G' : Drawing Shat, P.IsPreRadialDrawing G' ↔
      IsPreRadial (Γ.hatU cap) (Γ.hatV cap) G' := by
    intro G'
    simp only [PaintingOrDrawing.IsPreRadialDrawing, IsPreRadial, hU, hV, hR]
  exact ⟨h2, (key _).2 rad.isPreRadial, fun G' hG' h ↦ rad.maximal G' ((key _).1 hG') h⟩

end RadialDrawing

/-- `dist(Γ)` for an internally 3-connected painting `Γ` with radial drawing `Γ*` (Graph Minors XIX,
Section 5, page 337: "we define $dist(\Gamma)$ to be the minimum of $\frac{1}{2}|E(F)|$, taken over
all paths $F$
of $\Gamma^*$ with ends distinct poles. (If $c(\Sigma) \le 1$ we set $dist(\Gamma) =
\infty$.)"). The infimum of the empty
set in `ℕ∞` is `∞`. Such a path has even length because `Γ*` is bipartite. -/
noncomputable def Painting.dist {Shat : Type u} [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat} {Γ : Painting S} (rad : RadialDrawing cap Γ) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ (F : Drawing Shat) (p₁ p₂ : Shat),
    p₁ ∈ rad.poles ∧ p₂ ∈ rad.poles ∧ p₁ ≠ p₂ ∧
    F.IsPathOf rad.G p₁ p₂ ∧ n = (F.E.ncard / 2 : ℕ)}

/-- `rep(Γ)` for a 2-cell painting `Γ` with radial drawing `Γ*` (Graph Minors XIX, Section 5,
page 338: "If $\hat{\Sigma}$ is not a sphere, we define $rep(\Gamma)$ to be the minimum of
$\frac{1}{2}|E(F)|$ over all non-null-homotopic circuits $F$ of $\Gamma^*$. (This exists, by
Theorem 11.10 of [2].) If $\hat{\Sigma}$ is a sphere we set $rep(\Gamma) = \infty$."). On a sphere
every `O`-arc is null-homotopic, so the set below is empty and its infimum in `ℕ∞` is `∞`. -/
noncomputable def Painting.rep {Shat : Type u} [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat} {Γ : Painting S} (rad : RadialDrawing cap Γ) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ F : Drawing Shat,
    F.IsCircuitOf rad.G ∧ ¬ IsNullHomotopicOArc F.U ∧ n = (F.E.ncard / 2 : ℕ)}

/-! ### Section 6: Inflations and linear inflations -/

/-- `rep(G)` for a drawing `G` in a surface `Σ` (Graph Minors XIX, Section 6, page 340:
"If $G$ is a drawing in a surface $\Sigma$, not a sphere, we define $rep(G)$ to be the
minimum of $|F \cap V(G)|$, taken over all non-null-homotopic $G$-normal $O$-arcs $F$ in
$\Sigma$. If $\Sigma$ is a sphere, we set $rep(G) = \infty$."). -/
noncomputable def Drawing.rep (G : Drawing S) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ F : Set S,
    IsOArc F ∧ G.IsNormal F ∧ ¬ IsNullHomotopicOArc F ∧ n = ((F ∩ G.V).ncard : ℕ)}

/-- Two drawings `G, G'` are isomorphic (Graph Minors XIX, Section 6, page 340:
"If $G, G'$ are drawings in $\Sigma, \Sigma'$ respectively we say that $G, G'$ are
*isomorphic* if there is a bijection $\beta : V(G) \cup E(G) \to V(G') \cup E(G')$, mapping
vertices to vertices and edges to edges and preserving incidence"). -/
def Drawing.IsIsomorphic {S₁ S₂ : Type u} [TopologicalSpace S₁] [TopologicalSpace S₂]
    (G : Drawing S₁) (G' : Drawing S₂) : Prop :=
  ∃ (βv : S₁ → S₂) (βe : Set S₁ → Set S₂),
    BijOn βv G.V G'.V ∧ BijOn βe G.E G'.E ∧
    ∀ v ∈ G.V, ∀ e ∈ G.E, v ∈ tilde e ↔ βv v ∈ tilde (βe e)

/-- An enlargement of a drawing `G` in a drawing `G'` (Graph Minors XIX, Section 6, page 340):
"An *enlargement* of $G$ in $G'$ is a function $\sigma$ with domain $V(G) \cup E(G)$, such
that - for each $e \in E(G)$, $\sigma(e) \in E(G')$, and if $e_1, e_2 \in E(G)$ are distinct
then $\sigma(e_1) \ne \sigma(e_2)$, - for each $v \in V(G)$, $\sigma(v)$ is a non-null
connected subdrawing of $G'$, and if $v_1, v_2 \in V(G)$ are distinct then $\sigma(v_1),
\sigma(v_2)$ are disjoint, - for each $e \in E(G)$ and $v \in V(G)$, $\sigma(v)$ contains an
end of $\sigma(e)$ if and only if $v$ is an end of $e$." -/
structure IsEnlargement {S₁ S₂ : Type u} [TopologicalSpace S₁] [TopologicalSpace S₂]
    (G : Drawing S₁) (G' : Drawing S₂) (σv : S₁ → Drawing S₂) (σe : Set S₁ → Set S₂) : Prop where
  edge_mem : ∀ e ∈ G.E, σe e ∈ G'.E
  edge_injOn : InjOn σe G.E
  vertex_subdrawing : ∀ v ∈ G.V, (σv v).IsSubdrawing G'
  vertex_nonempty : ∀ v ∈ G.V, ((σv v).V).Nonempty
  vertex_connected : ∀ v ∈ G.V, ((σv v).adj.induce (σv v).V).Preconnected
  vertex_disjoint : ∀ v₁ ∈ G.V, ∀ v₂ ∈ G.V, v₁ ≠ v₂ → Disjoint (σv v₁).V (σv v₂).V
  ends_iff : ∀ e ∈ G.E, ∀ v ∈ G.V, ((σv v).V ∩ tilde (σe e)).Nonempty ↔ v ∈ tilde e

/-- A drawing `G` in `Σ` is a block if `G` is non-null and connected, and `G \ v` is connected for
every vertex `v ∈ V(G)` (Graph Minors XIX, Section 6, page 341: "A drawing $G$ in $\Sigma$ is a
*block* if $G$ is non-null and connected, and $G\setminus v$
is connected for every vertex $v\in V(G)$"). -/
structure Drawing.IsBlock (G : Drawing S) : Prop where
  nonempty_V : G.V.Nonempty
  connected : (G.adj.induce G.V).Preconnected
  biconnected : ∀ v ∈ G.V, (G.adj.induce (G.V \ {v})).Preconnected

export Drawing (IsBlock)

namespace Surface.Drawing

export GM19.Drawing (rep IsIsomorphic IsBlock)

end Surface.Drawing

/-! ### Section 7: Tangles -/

/-- `rep(𝒯)` for a tangle `𝒯` of order `ord` in `Γ.toHypergraph` (Graph Minors XIX, Section 7,
page 344:
"We define $rep(\mathscr{T})$ to be the maximum $k\le ord(\mathscr{T})$ such that for every circuit
$F$ of $\Gamma^*$ with $\frac{1}{2}|E(F)|<k$ there is a disc $\Delta\subseteq \hat{\Sigma}$ bounded
by $U(F)$, such that $(\Gamma\cap \Delta, \Gamma\cap \Delta')\in \mathscr{T}$, where $\Delta'$ is
the closure of $\hat{\Sigma}\setminus \Delta$."). -/
noncomputable def tangleRep {Shat : Type u} [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat} {Γ : Painting S} (rad : RadialDrawing cap Γ) (ord : ℕ)
    (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) : ℕ :=
  sSup {k : ℕ | k ≤ ord ∧ ∀ F : Drawing Shat, F.IsCircuitOf rad.G → F.E.ncard < 2 * k →
    ∃ Δ : Set Shat, IsClosedDisc Δ ∧ discBd Δ = F.U ∧
      (Γ.restrict (cap.emb ⁻¹' Δ), Γ.restrict (cap.emb ⁻¹' closure Δᶜ)) ∈ 𝒯}

/-- `Δ` is the inside `ins(F)` of a circuit `F` of `Γ*` with respect to `𝒯` (Graph Minors XIX,
Section 7, page 344). -/
def IsInsOf {Shat : Type u} [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat} {Γ : Painting S} (rad : RadialDrawing cap Γ) (ord : ℕ)
    (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (F : Drawing Shat) (Δ : Set Shat) : Prop :=
  F.IsCircuitOf rad.G ∧ F.E.ncard < 2 * tangleRep rad ord 𝒯 ∧ IsClosedDisc Δ ∧ discBd Δ = F.U ∧
    (Γ.restrict (cap.emb ⁻¹' Δ), Γ.restrict (cap.emb ⁻¹' closure Δᶜ)) ∈ 𝒯

/-- `Δ'` is the outside `out(F)` of a circuit `F` of `Γ*` with respect to `𝒯` (Graph Minors XIX,
Section 7, page 344: "`Δ' = out(F)`" where `Δ'` is the closure of `Σ̂ \ Δ`). -/
def IsOutOf {Shat : Type u} [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat} {Γ : Painting S} (rad : RadialDrawing cap Γ) (ord : ℕ)
    (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (F : Drawing Shat) (Δ' : Set Shat) : Prop :=
  ∃ Δ : Set Shat, IsInsOf rad ord 𝒯 F Δ ∧ Δ' = closure Δᶜ

/-- The atoms `A(Γ)` of a 2-cell painting `Γ` (Graph Minors XIX, Section 7, page 344:
"The *atoms* of $\Gamma$ are the sets $\{v\} (v\in V(\Gamma))$, the edges of $\Gamma$, and the
regions of $\Gamma$ in $\hat{\Sigma}$; and the set of atoms is denoted by $A(\Gamma)$"). -/
noncomputable def Painting.atoms {Shat : Type u} [TopologicalSpace Shat]
    (cap : IsCappedSurface S Shat) (Γ : Painting S) : Set (Set Shat) :=
  ((fun v ↦ {cap.emb v}) '' Γ.V) ∪ ((fun e ↦ cap.emb '' e) '' Γ.E) ∪
    componentsIn (cap.emb '' Γ.U)ᶜ

/-- A closed walk `W` of length `< 2 rep(𝒯)` in `Γ*` and its inside `ins(W)` (Graph Minors XIX,
Section 7, page 344: "If $W$ is a closed walk in $\Gamma^*$, we define $\Gamma^*|W$ to be the
subdrawing of
$\Gamma^*$ consisting of all vertices and edges in $W$. If $W$ has length
$<2\,rep(\mathscr{T})$, we define $ins(W)$ to be the union of $U(\Gamma^*|W)$ and all the
closed discs $ins(F)$ where $F$ is a circuit of $\Gamma^*|W$"). -/
structure ClosedWalkIns {Shat : Type u} [TopologicalSpace Shat] [T2Space Shat]
    {cap : IsCappedSurface S Shat} {Γ : Painting S} (rad : RadialDrawing cap Γ) (ord : ℕ)
    (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) where
  /-- Base vertex of the closed walk `W` in `Γ*`. -/
  base : Shat
  /-- The closed walk `W` in `Γ*`. -/
  walk : GraphWalk rad.G.toGraph base base
  /-- The subdrawing `Γ*|W` of `Γ*`. -/
  sub : Drawing Shat
  /-- Half the length of the closed walk `W`. -/
  halfLen : ℕ
  /-- The set `ins(W) ⊆ Σ̂`. -/
  ins : Set Shat
  sub_eq : sub = walkDrawing rad.G walk
  walk_len : walk.length = 2 * halfLen
  halfLen_lt : halfLen < tangleRep rad ord 𝒯
  ins_eq : ins = sub.U ∪ ⋃ (F : Drawing Shat) (_ : F.IsSubdrawing sub)
    (Δ : Set Shat) (_ : IsInsOf rad ord 𝒯 F Δ), Δ

/-- The metric `d(a, b)` of a tangle `𝒯` on the set of atoms `A(Γ)` (Graph Minors XIX, Section 7,
page 344:
"- if $a = b$ then $d(a, b) = 0$, - if $a\ne b$ and there is a closed walk $W$ of $\Gamma^*$
with length $<2\,rep(\mathscr{T})$ and with $a\cap ins(W), b\cap ins(W)\ne \emptyset$, we
define $d(a, b)$ to be half the minimum length of such a walk, - if neither of the above
applies then $d(a, b) = rep(\mathscr{T})$"). -/
noncomputable def tangleMetric {Shat : Type u} [TopologicalSpace Shat] [T2Space Shat]
    {cap : IsCappedSurface S Shat} {Γ : Painting S} (rad : RadialDrawing cap Γ) (ord : ℕ)
    (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (a b : Set Shat) : ℕ :=
  open Classical in
  if a = b then 0
  else if ∃ W : ClosedWalkIns rad ord 𝒯, (a ∩ W.ins).Nonempty ∧ (b ∩ W.ins).Nonempty then
    sInf {k : ℕ | ∃ W : ClosedWalkIns rad ord 𝒯,
      (a ∩ W.ins).Nonempty ∧ (b ∩ W.ins).Nonempty ∧ W.halfLen = k}
  else tangleRep rad ord 𝒯

/-! ### Section 8: Tie-breakers, enclaves, arms, and rooted locations -/

/-- `f` is an edge of `sk(Γ)` included in the edge `c` of `Γ` (Graph Minors XIX, Section 2,
page 327): the edge `c` itself if `|cTilde| = 2`, and one of the three arcs of `bd(cBar) \ cTilde`
if
`|cTilde| = 3`. -/
def Painting.IsSkEdgeIn (Γ : Painting S) (f c : Set S) : Prop :=
  c ∈ Γ.E ∧ (((tilde c).ncard = 2 ∧ f = c) ∨
    ((tilde c).ncard = 3 ∧ f ∈ arcComponentsIn (discBd (closure c) \ tilde c)))

/-- A separation `(A, B)` of `Γ` splits an edge `e ∈ E(Γ*)` (Graph Minors XIX, Section 8, page 346:
"Let $e \in E(\Gamma^*)$ with ends $v \in V(\Gamma)$ and $r^* \in R^*(\Gamma)$, and let $C$
be the circuit of $sk(\Gamma)$ with $U(C)$ bounding $r$. (We assume for the moment that $C$
exists.) Let $f_1, f_2$ be the two edges of $C$ incident with $v$, and let $c_1, c_2$ be the
two edges of $\Gamma$ with $f_1 \subseteq c_1, f_2 \subseteq c_2$. Now if $(A, B)$ is a
separation of $\Gamma$, we say that $(A, B)$ splits $e$ if $c_1 \in E(A)$ and $c_2 \in E(B)$
or vice versa. (If the circuit $C$ does not exist, then ... $|V(\Gamma)| = 2$ and
$|E(\Gamma)| = 1$. In this case we say that $(A, B)$ does not split $e$.)"). The edges of `C` are
the edges of `sk(Γ)` in the
frontier of `r`, so `f₁, f₂` are the two distinct edges of `sk(Γ)` at `v` in that frontier. In the
exceptional case `Γ` has one edge, so `c₁ = c₂`, and a separation has no common edge. -/
def RadialDrawing.Splits {Shat : Type u} [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat} {Γ : Painting S} (rad : RadialDrawing cap Γ)
    (A B : Hypergraph S (Set S)) (e : Set Shat) : Prop :=
  ∃ (v : S) (w : Shat), v ∈ Γ.V ∧ w ∈ rad.Rstar ∧ closure e ∩ rad.G.V = {cap.emb v, w} ∧
    ∃ f₁ f₂ c₁ c₂ : Set S, f₁ ≠ f₂ ∧ Γ.IsSkEdgeIn f₁ c₁ ∧ Γ.IsSkEdgeIn f₂ c₂ ∧
      v ∈ tilde f₁ ∧ v ∈ tilde f₂ ∧
      cap.emb '' f₁ ⊆ frontier (rad.regionOf w) ∧ cap.emb '' f₂ ⊆ frontier (rad.regionOf w) ∧
      ((c₁ ∈ A.edgeSet ∧ c₂ ∈ B.edgeSet) ∨ (c₁ ∈ B.edgeSet ∧ c₂ ∈ A.edgeSet))

/-- A tie-breaker `λ` in an internally 3-connected painting `Γ` (Graph Minors XIX, Section 8,
pages 346–347): "for each $e \in E(\Gamma^*)$ let $\lambda(e) > 0$ be some real number, and for each
$v \in V(\Gamma)$ let $\lambda(v) > 0$ be some real number, such that all the $\lambda(e)$’s and
$\lambda(v)$’s are ... rationally independent; that is,
$$\sum (\alpha(e)\lambda(e) : e \in E(\Gamma^*)) = \sum (\beta(v)\lambda(v) : v \in V(\Gamma))$$
for rationals $\alpha(e), \beta(v)$ only if each $\alpha(e) = 0$ and each $\beta(v) = 0$. Moreover,
let $\lambda(e) < \lambda(f)$ for all $e, f \in E(\Gamma^*)$ such that
$e \subseteq \hat{\Sigma} \setminus \Sigma$ and $f \subseteq \Sigma$. We call $\lambda$ a
tie-breaker in $\Gamma$." -/
structure TieBreaker {Shat : Type u} [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat} {Γ : Painting S} (rad : RadialDrawing cap Γ) where
  /-- Weight `λ(e) > 0` for `e ∈ E(Γ*)`. -/
  wtE : Set Shat → ℝ
  /-- Weight `λ(v) > 0` for `v ∈ V(Γ)`. -/
  wtV : S → ℝ
  wtE_pos : ∀ e ∈ rad.G.E, 0 < wtE e
  wtV_pos : ∀ v ∈ Γ.V, 0 < wtV v
  rationally_independent : ∀ (α : Set Shat → ℚ) (β : S → ℚ),
    ∑ᶠ e ∈ rad.G.E, (α e : ℝ) * wtE e = ∑ᶠ v ∈ Γ.V, (β v : ℝ) * wtV v →
    (∀ e ∈ rad.G.E, α e = 0) ∧ (∀ v ∈ Γ.V, β v = 0)
  cuff_lt_internal : ∀ e ∈ rad.G.E, ∀ f ∈ rad.G.E,
    Disjoint e (range cap.emb) → f ⊆ range cap.emb → wtE e < wtE f

namespace TieBreaker

variable {Shat : Type u} [TopologicalSpace Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S} {rad : RadialDrawing cap Γ}

/-- The first component `N₁ = |V(A ∩ B)|` of the `λ`-order of a separation `(A, B)`. -/
noncomputable def N1 (_ : TieBreaker rad) (sep : Hypergraph S (Set S) × Hypergraph S (Set S)) :
    ℕ :=
  separationOrder sep.1 sep.2

/-- The second component `N₂ = ∑ (λ(e) : e is split by (A, B))` of the `λ`-order. -/
noncomputable def N2 (tb : TieBreaker rad) (sep : Hypergraph S (Set S) × Hypergraph S (Set S)) :
    ℝ :=
  ∑ᶠ e ∈ {e ∈ rad.G.E | rad.Splits sep.1 sep.2 e}, tb.wtE e

/-- The third component `N₃ = ∑ (λ(v) : v ∈ V(A ∩ B))` of the `λ`-order. -/
noncomputable def N3 (tb : TieBreaker rad) (sep : Hypergraph S (Set S) × Hypergraph S (Set S)) :
    ℝ :=
  ∑ᶠ v ∈ (sep.1 ∩ sep.2).vertexSet, tb.wtV v

/-- The `λ`-order `(N₁, N₂, N₃)` of a separation `(A, B)`, in the lexicographic order (Graph Minors
XIX, Section 8, page 347: "we say that $(A, B)$ has smaller $\lambda$-order than $(A', B')$ if
either $N_1 < N_1'$, or
$N_1 = N_1'$ and $N_2 < N_2'$, or $N_1 = N_1'$ and $N_2 = N_2'$ and $N_3 < N_3'$"). Its values
lie in a linear order, so `GM10.IsTieBreaker`, `GM10.IsDistinction`, `GM18.IsLambdaLinkedTo`, and
`GM18.Isolates` apply to it directly. -/
noncomputable def lambdaOrder (tb : TieBreaker rad)
    (sep : Hypergraph S (Set S) × Hypergraph S (Set S)) : ℕ ×ₗ ℝ ×ₗ ℝ :=
  toLex (tb.N1 sep, toLex (tb.N2 sep, tb.N3 sep))

/-- `λ(K) = ∑_{e ∈ E(K)} λ(e)` for a subdrawing `K` of `Γ*` (Graph Minors XIX, Section 8,
page 348: "If $K$ is a subgraph of $\Gamma^*$, $\lambda(K)$ denotes $\sum_{e \in E(K)}
\lambda(e)$"). -/
noncomputable def weightSub (tb : TieBreaker rad) (K : Drawing Shat) : ℝ :=
  ∑ᶠ e ∈ K.E, tb.wtE e

end TieBreaker

/-- A circuit `F` of `Γ*` is a `𝒯`-enclave around `𝒯'` (Graph Minors XIX, Section 8, page 348:
"Given a tangle $\mathscr{T}$ in $\Gamma$, a circuit $F$ of $\Gamma^*$ is a
$\mathscr{T}$-enclave if $\frac{1}{2}|E(F)| < rep(\mathscr{T})$, and there is a tangle
$\mathscr{T}'$ in $\Gamma$ for which $(\Gamma \cap ins(F), \Gamma \cap out(F))$ is the
$(\mathscr{T}, \mathscr{T}')$-distinction. We also call $F$ a $\mathscr{T}$-enclave around
$\mathscr{T}'$"). The distinction is that of Graph Minors X,
`GM10.IsDistinction`, for the `λ`-order of `TieBreaker.lambdaOrder`. -/
def IsEnclaveAround {Shat : Type u} [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat} {Γ : Painting S} {rad : RadialDrawing cap Γ}
    (tb : TieBreaker rad) (ord ord' : ℕ)
    (𝒯 𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (F : Drawing Shat) : Prop :=
  GM10.IsTangle Γ.toHypergraph ord' 𝒯' ∧
  F.IsCircuitOf rad.G ∧ F.E.ncard < 2 * tangleRep rad ord 𝒯 ∧
    ∃ Δ : Set Shat,
      IsInsOf rad ord 𝒯 F Δ ∧
      GM10.IsDistinction tb.lambdaOrder 𝒯 𝒯'
        (Γ.restrict (cap.emb ⁻¹' Δ)) (Γ.restrict (cap.emb ⁻¹' closure Δᶜ))

/-- A circuit `F` of `Γ*` is a `𝒯`-enclave if it is a `𝒯`-enclave around some tangle `𝒯'`
(Graph Minors XIX, Section 8, page 348). -/
def IsEnclave {Shat : Type u} [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat} {Γ : Painting S} {rad : RadialDrawing cap Γ}
    (tb : TieBreaker rad) (ord : ℕ)
    (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (F : Drawing Shat) : Prop :=
  ∃ (ord' : ℕ) (𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
    IsEnclaveAround tb ord ord' 𝒯 𝒯' F

/-- `Σ₁, Σ₂` are the closures of the two components of `Σ̂ \ U(F)` (Graph Minors XIX, Section 8,
page 349, and Section 10, page 353). A subset whose complement is not exactly two components has no
such pair. -/
def IsSidesOf {Shat : Type u} [TopologicalSpace Shat] (F : Drawing Shat) (S₁ S₂ : Set Shat) : Prop
  :=
  ∃ C₁ C₂ : Set Shat, C₁ ≠ C₂ ∧ componentsIn F.Uᶜ = {C₁, C₂} ∧
    S₁ = closure C₁ ∧ S₂ = closure C₂

/-- A circuit `F` of `Γ*` is `λ`-linked to `𝒯` (Graph Minors XIX, Section 8, page 349:
"If $F$ is a circuit of $\Gamma^*$ with $\frac{1}{2} |E(F)| < \min(ord(\mathscr{T}), rep(\Gamma))$,
let $\Sigma_1, \Sigma_2$ be the closures of the two components of $\hat{\Sigma} \setminus U(F)$;
then $\mathscr{T}$ contains one of $(\Gamma \cap \Sigma_1, \Gamma \cap \Sigma_2)$,
$(\Gamma \cap \Sigma_2, \Gamma \cap \Sigma_1)$, and if that separation is $\lambda$-linked to
$\mathscr{T}$ we say that $F$ is $\lambda$-*linked (to* $\mathscr{T}$*)*"). The separation is
`λ`-linked in the sense of Graph Minors XVIII,
`GM18.IsLambdaLinkedTo`, which the paper repeats word for word. -/
def IsLambdaLinkedCircuit {Shat : Type u} [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat} {Γ : Painting S} {rad : RadialDrawing cap Γ}
    (tb : TieBreaker rad) (ord : ℕ)
    (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (F : Drawing Shat) : Prop :=
  F.IsCircuitOf rad.G ∧ (F.E.ncard : ℕ∞) < 2 * min (ord : ℕ∞) (Painting.rep rad) ∧
    ∃ S₁ S₂ : Set Shat, IsSidesOf F S₁ S₂ ∧
      GM18.IsLambdaLinkedTo tb.lambdaOrder 𝒯
        (Γ.restrict (cap.emb ⁻¹' S₁)) (Γ.restrict (cap.emb ⁻¹' S₂))

/-- An arm `A` of a painting `Γ` (Graph Minors XIX, Section 8, page 350:
"An *arm* $A$ of a painting $\Gamma$ is a pair $(A^-, \pi(A))$, where $A^-$ is a
subhypergraph of $\Gamma$ and $\pi(A)$ is a march in $V(A^-)$, with the property that there
exists $B \subseteq \Gamma$ such that $(A^-, B)$ is a separation of $\Gamma$ and $V(A^- \cap
B) = \bar{\pi}(A)$"). -/
structure Arm (Γ : Painting S) where
  /-- The subhypergraph `A⁻` of `Γ`. -/
  minus : Hypergraph S (Set S)
  /-- The complement `Aᶜ` of `A`. -/
  compl : Hypergraph S (Set S)
  /-- `(A⁻, Aᶜ)` is a separation of `Γ.toHypergraph`. -/
  isSeparation : Γ.toHypergraph.IsSeparation minus compl
  /-- The boundary march `π(A)`. -/
  π : List S
  π_nodup : π.Nodup
  π_set : {v | v ∈ π} = (minus ∩ compl).vertexSet

namespace Arm

variable {Γ : Painting S}

/-- The underlying separation `(A⁻, Aᶜ)` of `Γ.toHypergraph`. -/
def sep (A : Arm Γ) : Hypergraph S (Set S) × Hypergraph S (Set S) := (A.minus, A.compl)

/-- The vertex set `V(A) = V(A⁻)` of an arm `A`. -/
def V (A : Arm Γ) : Set S := A.minus.vertexSet

/-- The edge set `E(A) = E(A⁻)` of an arm `A`. -/
def E (A : Arm Γ) : Set (Set S) := A.minus.edgeSet

/-- The order `|πBar(A)|` of an arm `A` (Graph Minors XIX, Section 8, page 350). -/
noncomputable def order (A : Arm Γ) : ℕ := separationOrder A.minus A.compl

/-- The arm `A = (A⁻, π(A))` viewed as a shared `RootedHypergraph S (Set S)`. -/
def toRootedHypergraph (A : Arm Γ) : RootedHypergraph S (Set S) where
  toHypergraph := A.minus
  roots := A.π
  roots_nodup := A.π_nodup
  roots_subset v hv := by
    have hmem : v ∈ (A.minus ∩ A.compl).vertexSet := by
      rw [← A.π_set]
      exact hv
    exact hmem.1

/-- An arm `A` is `λ`-linked to `𝒯` if `(A⁻, Aᶜ)` is `λ`-linked to `𝒯` (Graph Minors XIX,
Section 8, page 350). -/
def IsLambdaLinked {Shat : Type u} [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat} {rad : RadialDrawing cap Γ}
    (tb : TieBreaker rad) (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (A : Arm Γ) : Prop :=
  GM18.IsLambdaLinkedTo tb.lambdaOrder 𝒯 A.minus A.compl

end Arm

/-- A rooted location `ℒ` in a painting `Γ` (Graph Minors XIX, Section 8, page 350:
"A *rooted location* in $\Gamma$ is a set $\mathscr{L}$ of arms, such that that if
$A_1, A_2 \in \mathscr{L}$ with $A^-_1 \ne A^-_2$ then $A^-_1 \subseteq A^c_2$"). The condition
here is for distinct arms, as in Graph Minors XVIII, Section 5,
page 93, whose theorems (9.2) applies: two arms with the same `A⁻` and different marches do not give
a rooted location there. -/
structure RootedLocation (Γ : Painting S) where
  /-- The set of arms in `ℒ`. -/
  arms : Set (Arm Γ)
  finite_arms : arms.Finite
  disjoint_arms : ∀ A₁ ∈ arms, ∀ A₂ ∈ arms, A₁ ≠ A₂ → A₁.minus ≤ A₂.compl

namespace RootedLocation

variable {Γ : Painting S}

/-- The order `ord(ℒ)` of a rooted location `ℒ` (Graph Minors XIX, Section 8, page 350:
"Its *order* $ord(\mathscr{L})$ is the maximum order of its members (or zero, if $\mathscr{L}
= \emptyset$)"). -/
noncomputable def ord (L : RootedLocation Γ) : ℕ :=
  sSup (Arm.order '' L.arms)

/-- The set of separations `ℒ⁻ = {(A⁻, Aᶜ) : A ∈ ℒ}` (Graph Minors XIX, Section 8, page 350). -/
def seps (L : RootedLocation Γ) : Set (Hypergraph S (Set S) × Hypergraph S (Set S)) :=
  Arm.sep '' L.arms

/-- A rooted location `ℒ` with `ℒ⁻ ⊆ 𝒯` is `λ`-linked to `𝒯` if each of its members is `λ`-linked
to `𝒯` (Graph Minors XIX, Section 8, page 350). -/
def IsLambdaLinked {Shat : Type u} [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat} {rad : RadialDrawing cap Γ}
    (tb : TieBreaker rad) (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (L : RootedLocation Γ) : Prop :=
  L.seps ⊆ 𝒯 ∧ ∀ A ∈ L.arms, A.IsLambdaLinked tb 𝒯

/-- A rooted location `ℒ` `θ`-isolates a tangle `𝒯` (Graph Minors XIX, Section 8, page 350:
"A rooted location $\mathscr{L}$ *$\theta$-isolates* a tangle $\mathscr{T}$ if $\mathscr{L}^-
\subseteq \mathscr{T}, ord(\mathscr{L}) < \theta \le ord(\mathscr{T})$, and for every $A \in
\mathscr{L}$ and for every tangle $\mathscr{T}'$ of order $\ge \theta$ with $(A^c, A^-) \in
\mathscr{T}'$, the $(\mathscr{T}, \mathscr{T}')$-distinction $(C, D)$ satisfies $C \subseteq
A^-$ and $A^c \subseteq D$"). -/
structure Isolates {Shat : Type u} [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat} {rad : RadialDrawing cap Γ}
    (tb : TieBreaker rad) (L : RootedLocation Γ) (θ ord : ℕ)
    (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) : Prop where
  seps_subset : L.seps ⊆ 𝒯
  ord_lt : L.ord < θ
  le_ord : θ ≤ ord
  distinction_le : ∀ A ∈ L.arms, ∀ (ord' : ℕ)
    (𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
    GM10.IsTangle Γ.toHypergraph ord' 𝒯' → θ ≤ ord' → A.sep.swap ∈ 𝒯' →
    ∀ C D : Hypergraph S (Set S),
      GM10.IsDistinction tb.lambdaOrder 𝒯 𝒯' C D → C ≤ A.minus ∧ A.compl ≤ D

end RootedLocation

end GraphMinor.GM19
