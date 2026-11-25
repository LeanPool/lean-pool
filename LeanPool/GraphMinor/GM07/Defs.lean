/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.TopologyStatements
public import LeanPool.GraphMinor.GM11.Defs
public import LeanPool.GraphMinor.GM14.Defs

/-!
# Definitions of Graph Minors VII

This file formalizes the definitions of N. Robertson and P. D. Seymour,
*Graph Minors. VII. Disjoint paths on a surface*, J. Combin. Theory Ser. B 45 (1988) 212–254.

## Match with `Surface.Drawing`

In Section 2 (page 214), Graph Minors VII defines a "graph" in a surface `Σ` as a pair
`G = (U(G), V(G))` where `U(G) ⊆ Σ`, `V(G) ⊆ U(G)` is finite, `U(G) - V(G)` has only finitely
many components (called *edges*), and for each edge `e`, `(e, closure e)` is homeomorphic either to
`((0, 1), [0, 1])` or to `(S¹ - {x}, S¹)`.

This matches `GraphMinor.Surface.Drawing S` from `GraphMinor/Surface/Defs.lean`:
- A `Drawing S` is given by `(U, V)` with `U` closed, `V ⊆ U` finite, and `E = componentsIn (U \ V)`
  finite.
- Each edge `e ∈ G.E` has `tilde e = closure e \ e ⊆ V` of size `1` (a loop, where `closure e` is an
  `O`-arc, so `(e, closure e) ≃ (S¹ - {x}, S¹)`) or size `2` (a non-loop, where `closure e` is a
  line with `lineEnds (closure e) = tilde e`, so `(e, closure e) ≃ ((0, 1), [0, 1])`).
- Because `V` is finite and each of the finitely many edges has compact closure `e ∪ tilde e ⊆ U`,
  `U = V ∪ ⋃ e ∈ E, closure e` is automatically closed in `Σ`.
- A subset `X ⊆ Σ` is `G`-normal in VII's sense (`X ∩ e = ∅` for each edge `e` of `G`) if and only
  if `X ∩ G.U ⊆ G.V`, which is `G.IsNormal X` (`isNormal_iff_disjoint_edges`).
- A graph `G` in `Σ` is proper in VII's sense (`bd(Σ)` is `G`-normal) if and only if
  `bd S ∩ G.U ⊆ G.V`, which is `G.IsProper` (`isProper_iff_isNormal_bd`).
- A region of `G` is a component of `Σ - U(G)`, which is `r ∈ G.R`.

## Sections covered

- **Section 2 (Surfaces and Nets, pages 213–218):** `deleteBd` (`J - bd(Σ)`), `IsBoundaryIArc`,
  `AreInternallyDisjointLines`, `IsIsolatedVertex`, `HasNoIsolatedVertices`, `pullbackDrawing`
  (`φ⁻¹(G)`), `imageDrawing` (`φ(H)`), `Net`, `Net.seamU`, `Net.seamV`, `Net.IsSeamGraphFor`,
  `IsSeamGraph`, `Net.IsNormalFor`, `Net.IsMinimalFor`, and the four edge types of `J'`.
- **Section 3 (Matchings and Forests, pages 218–221):** `AreSimilarIArcs`, `AreParallelIArcs`,
  `IsMatching`, `IsXMatching`, `AreCongruentMatchings`, `IsSurfaceForest`, `IsYForest`,
  `Drawing.mapHomeo`, `ForestsHomoplastic`, `MatchingSurroundsForest`, `IsW36Bound`, `wSurface`
  (`w(Σ, k, n)`).
- **Section 4 (The Main Result, First Version, pages 221–230):** `IsGFeasible`, `IsCappedCuff`
  (`Σ + Ĉ`), `IsNullHomotopicOArcInCappedCuff`, `IsPlanarInCappedCuff`, `wMaxModel`, `muModel`,
  `vModel`, `vSurface` (`v(Σ, k)`).
- **Section 5 (The Main Result, Second Version, pages 230–237):** `IsNearPlanar`, `SurroundsCuff`,
  `IsAlphaCandidate`, `alpha` (`α(G)`), `scriptA` (`𝒜_r(C)`), `distPoint` (`d(x, y)`),
  `distSet` (`d(x, A)`), `nearSet` (`Y_t(A)`), `IsPointInsideNullOArc`,
  `IsPointInsideSurroundingOArc`, `IsPointInsideOArc`, `IsInsideOArc`, `IsBoundaryLinked`.
- **Section 7 (Adding New Cuffs, pages 238–241):** `IsScriptASet`, `IsInnerHole`,
  `cuffInsideSet` (`Δ_r(C)`), `allCuffsInsideSet` (`Δ_r`).
- **Section 8 (Schisms, pages 241–242):** `IsX1Arc`, `IsX2Arc`, `IsX3Arc`, `IsX4ArcWithEnd`,
  `IsX4Arc`, `IsSchismatic`, `IsSchism`, `omega` (`ω(G)`).
- **Section 9 (Minors, pages 242–246):** `SurfaceDigraph` (`(G, G⁺, G⁻)`),
  `SurfaceDigraph.IsProper`, `IsBoundaryRootedMinor`, `IsDigraphMinor`,
  `numInternalIsolatedVertices`, `GM07Theorem91Statement`, `GM07Theorem92Statement`,
  `HasDisjointPathsBetween`, `maxDisjointPaths` (`k(X, Y)`).
- **Section 11 (Appendix, pages 248–254):** `IsArcComponentOf` and the topological predicates
  `IsFlat`, `IsArcConnected`, `IsLocallyArcConnected`, `IsSolid`, `IsPlanar`,
  `IsArcSimplyConnected`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14

universe u v

variable {S : Type u} [TopologicalSpace S]

/-! ## Section 2: Surfaces and Nets (pages 213–218) -/

/-- Every point `x ∈ F` belongs to `pathComponentIn F x ∈ arcComponentsIn F`. -/
theorem pathComponentIn_mem_arcComponentsIn {F : Set S} {x : S} (hx : x ∈ F) :
    pathComponentIn F x ∈ arcComponentsIn F := by
  refine ⟨⟨x, mem_pathComponentIn_self hx⟩, pathComponentIn_subset,
    isPathConnected_pathComponentIn hx, ?_⟩
  intro D hDF hD hxD
  exact Subset.antisymm (hD.subset_pathComponentIn (hxD (mem_pathComponentIn_self hx)) hDF) hxD

/-- Equivalence between `Drawing.IsNormal` (`X ∩ G.U ⊆ G.V`) and Graph Minors VII's definition
(Section 2, page 214): "If $G$ is a graph in $\Sigma$, a subset $X \subseteq \Sigma$ is *$G$-normal*
if $X \cap e =
\emptyset$ for each edge $e$ of $G$." -/
theorem isNormal_iff_disjoint_edges (G : Drawing S) (X : Set S) :
    G.IsNormal X ↔ ∀ e ∈ G.E, X ∩ e = ∅ := by
  constructor
  · intro h e he
    rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hxX, hxe⟩
    have hxU : x ∈ G.U \ G.V := he.2.1 hxe
    exact hxU.2 (h ⟨hxX, hxU.1⟩)
  · intro h x ⟨hxX, hxU⟩
    by_contra hxV
    have hxUV : x ∈ G.U \ G.V := ⟨hxU, hxV⟩
    have heE : pathComponentIn (G.U \ G.V) x ∈ G.E :=
      pathComponentIn_mem_arcComponentsIn hxUV
    have hempty := h _ heE
    exact hempty.subset ⟨hxX, mem_pathComponentIn_self hxUV⟩

/-- Equivalence between `Drawing.IsProper` (`bd S ∩ G.U ⊆ G.V`) and Graph Minors VII's definition
(Section 2, page 214): "A graph $G$ in $\Sigma$ is *proper* if $bd(\Sigma)$ is $G$-normal." -/
theorem isProper_iff_isNormal_bd (G : Drawing S) :
    G.IsProper ↔ G.IsNormal (bd S) :=
  Iff.rfl

/-- "If $J$ is a graph in $\Sigma$ with $bd(\Sigma) \subseteq U(J)$, then for every edge $e$ of
$J$, either $e \subseteq bd(\Sigma)$ or $e \cap bd(\Sigma) = \emptyset$." (Graph Minors VII, Section
2, page 214). -/
def HasBoundaryEdgesOrDisjoint (J : Drawing S) : Prop :=
  bd S ⊆ J.U ∧ ∀ e ∈ J.E, e ⊆ bd S ∨ e ∩ bd S = ∅

/-- "We denote by $J - bd(\Sigma)$ the subgraph $(V(J) \cup (U(J) - bd(\Sigma)), V(J))$ of such a
graph $J$."
(Graph Minors VII, Section 2, page 214). Here `J - bd(Σ)` is the subdrawing of `J` obtained by
retaining all vertices of `J` and those edges of `J` that are disjoint from `bd(Σ)`. -/
noncomputable def deleteBd [T1Space S] (J : Drawing S) : Drawing S :=
  J.span J.V {e ∈ J.E | e ∩ bd S = ∅}

/-- "An $I$-arc $F$ is a *boundary $I$-arc* if $F \subseteq bd(\Sigma)$."
(Graph Minors VII, Section 2, page 214). -/
def IsBoundaryIArc (F : Set S) : Prop :=
  IsIArc F ∧ F ⊆ bd S

/-- "Two $I$-arcs $F_1, F_2$ are *internally disjoint* if every point in $F_1 \cap F_2$ is an end
of both of them." (Graph Minors VII, Section 2, page 214). -/
def AreInternallyDisjointLines (F₁ F₂ : Set S) : Prop :=
  ∀ x ∈ F₁ ∩ F₂, x ∈ lineEnds F₁ ∧ x ∈ lineEnds F₂

/-- A vertex `v ∈ V(G)` is an *isolated vertex* of `G` if no edge of `G` is incident with `v`. -/
def IsIsolatedVertex (G : Drawing S) (v : S) : Prop :=
  v ∈ G.V ∧ ∀ e ∈ G.E, ¬ G.VertexIncident v e

/-- A graph `G` in `Σ` has *no isolated vertices* if every vertex of `G` is incident with at least
one edge of `G` (Graph Minors VII, Section 2, page 215). -/
def HasNoIsolatedVertices (G : Drawing S) : Prop :=
  ∀ v ∈ G.V, ∃ e ∈ G.E, G.VertexIncident v e

/-- The predicate that a pair `(U, V)` of subsets of `S` forms a valid `Drawing S`. -/
def IsDrawingPair (U V : Set S) : Prop :=
  ∃ G : Drawing S, G.U = U ∧ G.V = V

/-- "If $G$ is a proper graph in $\Sigma$ and $U(J)$ is $G$-normal, then $(\phi^{-1}(U(G)),
\phi^{-1}(V(G)))$ is a proper graph in $\Sigma'$, which we denote by $\phi^{-1}(G)$." (Graph Minors
VII, Section 2, page 215). -/
def IsPullbackDrawing {S' : Type v} [TopologicalSpace S'] (φ : S' → S) (G : Drawing S)
    (G' : Drawing S') : Prop :=
  G'.U = φ ⁻¹' G.U ∧ G'.V = φ ⁻¹' G.V

open Classical in
/-- Construct `φ⁻¹(G)` as a `Drawing S'` when `(φ⁻¹(U(G)), φ⁻¹(V(G)))` is a drawing pair, or return
a default drawing otherwise. -/
noncomputable def pullbackDrawing {S' : Type v} [TopologicalSpace S'] (φ : S' → S)
    (G : Drawing S) (fallback : Drawing S') : Drawing S' :=
  if h : ∃ G' : Drawing S', IsPullbackDrawing φ G G' then Classical.choose h else fallback

/-- "$\phi(H)$ denotes the graph $(\phi(U(H)), \phi(V(H)))$." (Graph Minors VII, Section 4, page
223). -/
def IsImageDrawing {S' : Type v} [TopologicalSpace S'] (φ : S' → S) (H' : Drawing S')
    (H : Drawing S) : Prop :=
  H.U = φ '' H'.U ∧ H.V = φ '' H'.V

open Classical in
/-- Construct `φ(H')` as a `Drawing S` when `(φ(U(H')), φ(V(H')))` is a drawing pair, or return a
default drawing otherwise. -/
noncomputable def imageDrawing {S' : Type v} [TopologicalSpace S'] (φ : S' → S)
    (H' : Drawing S') (fallback : Drawing S) : Drawing S :=
  if h : ∃ H : Drawing S, IsImageDrawing φ H' H then Classical.choose h else fallback

/-- "A *net* $(\Delta, \Pi)$ for a connected surface $\Sigma$ is a closed disc $\Delta$ together
with a set $$\Pi = \{\{f_1, g_1\}, \dots, \{f_r, g_r\}\},$$ where $f_1, g_1, \dots, f_r,
g_r$ are arc-maps of pairwise internally disjoint boundary $I$-arcs in $\Delta$, such that
$\Sigma$ can be obtained by pasting $f_1 = g_1$, $f_2 = g_2$, \dots, $f_r = g_r$. Let $\phi
\colon \Delta \to \Sigma$ be the associated surjection."
(Graph Minors VII, Section 2, page 215).
We represent `Δ` as a subspace `Δ : Set S` or a space `D : Type u` homeomorphic to the closed unit
disc, with `r` pairs `(f i, g i)` of embeddings of `unitInterval` into `bd D` whose images are
pairwise internally disjoint boundary `I`-arcs in `D`, and the associated quotient surjection
`φ : D → S`. -/
structure Net (S : Type u) [TopologicalSpace S] where
  /-- The closed disc `Δ`. -/
  D : Type u
  [topD : TopologicalSpace D]
  /-- `Δ` is a surface homeomorphic to the closed unit disc. -/
  isSurface_D : IsSurface D
  isClosedDisc_D : IsClosedDisc (univ : Set D)
  /-- The number `r` of pasted pairs in `Π = {{f₁, g₁}, …, {f_r, g_r}}`. -/
  r : ℕ
  /-- The first arc-map `f_i : [0, 1] → Δ` of the `i`-th pair in `Π`. -/
  f : Fin r → Curve D
  /-- The second arc-map `g_i : [0, 1] → Δ` of the `i`-th pair in `Π`. -/
  g : Fin r → Curve D
  /-- The associated surjection `φ : Δ → Σ`. -/
  φ : D → S
  /-- Each `f_i` is an injective arc-map into `bd(Δ)`. -/
  injective_f : ∀ i : Fin r, Function.Injective (f i)
  range_f_subset_bd : ∀ i : Fin r, range (f i) ⊆ bd D
  /-- Each `g_i` is an injective arc-map into `bd(Δ)`. -/
  injective_g : ∀ i : Fin r, Function.Injective (g i)
  range_g_subset_bd : ∀ i : Fin r, range (g i) ⊆ bd D
  /-- The `2r` boundary `I`-arcs `range (f_i)` and `range (g_i)` are pairwise internally disjoint:
  any point in the open interior `(0, 1)` of one arc does not lie on any other arc. -/
  internally_disjoint_ff : ∀ i j : Fin r, i ≠ j →
    ∀ x ∈ Ioo (0 : unitInterval) 1, f i x ∉ range (f j)
  internally_disjoint_gg : ∀ i j : Fin r, i ≠ j →
    ∀ x ∈ Ioo (0 : unitInterval) 1, g i x ∉ range (g j)
  internally_disjoint_fg : ∀ i j : Fin r,
    ∀ x ∈ Ioo (0 : unitInterval) 1, f i x ∉ range (g j)
  internally_disjoint_gf : ∀ i j : Fin r,
    ∀ x ∈ Ioo (0 : unitInterval) 1, g i x ∉ range (f j)
  /-- `φ` is a quotient map obtained by pasting `f_i(x) = g_i(x)` for `0 ≤ x ≤ 1`. -/
  quotientMap_φ : Topology.IsQuotientMap φ
  pasting_eq : ∀ (i : Fin r) (x : unitInterval), φ (f i x) = φ (g i x)
  /-- On `Δ - bd(Δ)`, `φ` makes no identifications with any other point of `Δ`. -/
  interior_inj : ∀ x ∈ (bd D)ᶜ, ∀ y : D, φ x = φ y → x = y
  /-- Two points of `bd(Δ)` have the same image under `φ` if and only if they are identified by the
  equivalence relation generated by `f_i(x) = g_i(x)` (`0 ≤ x ≤ 1`). -/
  bd_eq_iff : ∀ x y : D, φ x = φ y ↔
    Relation.EqvGen (fun a b : D => ∃ (i : Fin r) (t : unitInterval),
      a = f i t ∧ b = g i t) x y

attribute [instance] Net.topD

namespace Net

/-- The point set `U = {φ(x) : x ∈ bd(Δ)}` of the seam graph of a net `(Δ, Π)`
(Graph Minors VII, Section 2, page 215). -/
def seamU (N : Net S) : Set S :=
  N.φ '' bd N.D

/-- The vertex set `V = {z ∈ Σ : for some {f, g} ∈ Π, f has an end in φ⁻¹(z)}` of the seam graph
of a net `(Δ, Π)` (Graph Minors VII, Section 2, page 215). Since `φ(f_i(0)) = φ(g_i(0))` and
`φ(f_i(1)) = φ(g_i(1))`, these are the images under `φ` of the ends `f_i(0), f_i(1)`. -/
def seamV (N : Net S) : Set S :=
  {z : S | ∃ i : Fin N.r, N.φ (N.f i 0) = z ∨ N.φ (N.f i 1) = z}

/-- "Let $J = (U, V)$, where $U = \{\phi(x) \colon x \in bd(\Delta)\}$ and $$V = \{z \in \Sigma
\colon \text{for some } \{f, g\} \in \Pi\text{, } f \text{ has an end in } \phi^{-1}(z)\}.$$
Then, provided that $\Pi \ne \emptyset$, $J$ is a graph which we call the *seam graph* for
the net $(\Delta, \Pi)$."
(Graph Minors VII, Section 2, page 215). -/
def IsSeamGraphFor (N : Net S) (J : Drawing S) : Prop :=
  0 < N.r ∧ J.U = N.seamU ∧ J.V = N.seamV

/-- "Let $(\Delta, \Pi)$ be a net for $\Sigma$, and let $G$ be a proper graph in $\Sigma$. We say
that $(\Delta, \Pi)$ is *$G$-normal* if $U(J)$ is $G$-normal, where $J$ is the seam graph
for $(\Delta, \Pi)$."
(Graph Minors VII, Section 2, page 216). -/
def IsNormalFor (N : Net S) (G : Drawing S) : Prop :=
  ∃ J : Drawing S, N.IsSeamGraphFor J ∧ G.IsNormal J.U

/-- The quantity `|φ⁻¹(V(G)) ∩ bd(Δ)|` minimized in condition (ii) of a minimal net
(Graph Minors VII, Section 2, page 216). -/
noncomputable def bdVertexPreimageCard (N : Net S) (G : Drawing S) : ℕ :=
  (N.φ ⁻¹' G.V ∩ bd N.D).ncard

/-- "Let $G$ be a proper graph in a connected surface $\Sigma$. A net $(\Delta, \Pi)$ with
associated surjection $\phi \colon \Delta \to \Sigma$ is *minimal* (with respect to $G$) if
(i) it is $G$-normal, (ii) among all $G$-normal nets, $(\Delta, \Pi)$ has $|\phi^{-1}(V(G))
\cap bd(\Delta)|$ minimum, and (iii) among all $G$-normal nets satisfying (ii), $(\Delta,
\Pi)$ has $|\Pi|$ minimum."
(Graph Minors VII, Section 2, page 216). -/
def IsMinimalFor (N : Net S) (G : Drawing S) : Prop :=
  N.IsNormalFor G ∧
  (∀ N' : Net S, N'.IsNormalFor G → N.bdVertexPreimageCard G ≤ N'.bdVertexPreimageCard G) ∧
  (∀ N' : Net S, N'.IsNormalFor G → N'.bdVertexPreimageCard G ≤ N.bdVertexPreimageCard G →
    N.r ≤ N'.r)

end Net

/-- `J` is a *seam graph for some net* for `Σ` (Graph Minors VII, Section 2, (2.1), page 215). -/
def IsSeamGraph (J : Drawing S) : Prop :=
  ∃ N : Net S, N.IsSeamGraphFor J

/-- Type (i) edge of `J' = (U(J), V(J) ∪ {φ(s), φ(t)})` (Graph Minors VII, Section 2, page 217):
"edges `e` with `e ⊆ bd(Σ)`". -/
def IsNetEdgeType1 (e : Set S) : Prop :=
  e ⊆ bd S

/-- Type (ii) edge of `J'` (Graph Minors VII, Section 2, page 217):
"edges $e$ such that for all $z \in e$, $\phi^{-1}(z) \cap C_i \ne \emptyset$ $(i = 1, 2)$". -/
def IsNetEdgeType2 (N : Net S) (C₁ C₂ : Set N.D) (e : Set S) : Prop :=
  ∀ z ∈ e, (N.φ ⁻¹' {z} ∩ C₁).Nonempty ∧ (N.φ ⁻¹' {z} ∩ C₂).Nonempty

/-- Type (iii) edge of `J'` (Graph Minors VII, Section 2, page 217):
"edges $e$ such that $e \cap bd(\Sigma) = \emptyset$ and for all $z \in e$, $\phi^{-1}(z)
\subseteq C_1$". -/
def IsNetEdgeType3 (N : Net S) (C₁ : Set N.D) (e : Set S) : Prop :=
  e ∩ bd S = ∅ ∧ ∀ z ∈ e, N.φ ⁻¹' {z} ⊆ C₁

/-- Type (iv) edge of `J'` (Graph Minors VII, Section 2, page 217):
"edges $e$ such that $e \cap bd(\Sigma) = \emptyset$ and for all $z \in e$, $\phi^{-1}(z)
\subseteq C_2$". -/
def IsNetEdgeType4 (N : Net S) (C₂ : Set N.D) (e : Set S) : Prop :=
  e ∩ bd S = ∅ ∧ ∀ z ∈ e, N.φ ⁻¹' {z} ⊆ C₂

/-! ## Section 3: Matchings and Forests (pages 218–221) -/

/-- "Let $\Sigma$ be a surface and let $F, F'$ be proper $I$-arcs in $\Sigma$. We say that $F$ is
*similar* to $F'$ if there is a homeomorphism $\alpha \colon \Sigma \to \Sigma$ such that
$\alpha(F) = F'$."
(Graph Minors VII, Section 3, page 218). -/
def AreSimilarIArcs (F F' : Set S) : Prop :=
  ∃ α : S ≃ₜ S, α '' F = F'

/-- "Two proper $I$-arcs $F, F'$, are *parallel* if there is a homeomorphism $\alpha \colon
\Sigma \to \Sigma$ such that $\alpha(F) = F'$ and $\alpha(x) = x$ for all $x \in
bd(\Sigma)$."
(Graph Minors VII, Section 3, page 219). -/
def AreParallelIArcs (F F' : Set S) : Prop :=
  ∃ α : S ≃ₜ S, α '' F = F' ∧ ∀ x ∈ bd S, α x = x

/-- The valency of a vertex `v` in a drawing `G`, counting non-loop incident edges once and loop
edges (`(tilde e).ncard = 1`) twice (Graph Minors VII, Section 2, page 216, and Section 4,
page 225: "where $d(z)$ is the valency of $z$ in $J$, counting loops twice"). -/
noncomputable def vertexValency (G : Drawing S) (v : S) : ℕ :=
  {e ∈ G.E | G.VertexIncident v e ∧ (tilde e).ncard = 2}.ncard +
    2 * {e ∈ G.E | G.VertexIncident v e ∧ (tilde e).ncard = 1}.ncard

/-- "A *matching* in a surface $\Sigma$ is a proper graph $G$ in $\Sigma$ with $V(G) \subseteq
bd(\Sigma)$, in which every vertex has valency $1$." (Graph Minors VII, Section 3, page 219). -/
def IsMatching (G : Drawing S) : Prop :=
  G.IsProper ∧ G.V ⊆ bd S ∧ ∀ v ∈ G.V, vertexValency G v = 1

/-- "For $X \subseteq bd(\Sigma)$, an *$X$-matching* is a matching $G$ with $V(G) = X$."
(Graph Minors VII, Section 3, page 219). -/
def IsXMatching (X : Set S) (G : Drawing S) : Prop :=
  IsMatching G ∧ G.V = X

/-- "Two $X$-matchings $G, G'$ in $\Sigma$ are said to be *congruent* if there is a homeomorphism
$\alpha \colon \Sigma \to \Sigma$ such that $\alpha(U(G)) = U(G')$ and $\alpha(x) = x$ for
all $x \in bd(\Sigma)$."
(Graph Minors VII, Section 3, page 219). -/
def AreCongruentMatchings (G G' : Drawing S) : Prop :=
  ∃ α : S ≃ₜ S, α '' G.U = G'.U ∧ ∀ x ∈ bd S, α x = x

/-- "A *forest* in a surface $\Sigma$ is a proper graph in $\Sigma$ with no circuits."
(Graph Minors VII, Section 3, page 220). In `Surface/Defs.lean`, `IsGraphForest G.toGraph` states
that `G.toGraph` has no circuits (every non-empty walk from a vertex to itself repeats an edge). -/
def IsSurfaceForest (H : Drawing S) : Prop :=
  H.IsProper ∧ IsGraphForest H.toGraph

/-- "For $Y \subseteq bd(\Sigma)$, a $Y$-*forest* is a forest $H$ with $V(H) \cap bd(\Sigma) = Y$."
(Graph Minors VII, Section 3, page 220). -/
def IsYForest (Y : Set S) (H : Drawing S) : Prop :=
  IsSurfaceForest H ∧ H.V ∩ bd S = Y

/-- The image of the arc-components of `F` under a homeomorphism `α`. -/
theorem arcComponentsIn_image_homeo {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S')
    (F : Set S) : arcComponentsIn (α '' F) = (image α) '' arcComponentsIn F := by
  ext C'
  simp only [arcComponentsIn, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨hne', hsub', hpc', hmax'⟩
    refine ⟨α.symm '' C', ⟨hne'.image α.symm, ?_, hpc'.image α.symm.continuous, ?_⟩, ?_⟩
    · rintro x ⟨y, hy, rfl⟩
      rcases hsub' hy with ⟨z, hz, rfl⟩
      simpa using hz
    · intro D hDF hDpc hsubD
      have hD' : α '' D = C' := by
        refine hmax' (α '' D) (image_mono hDF) (hDpc.image α.continuous) ?_
        rintro y hy
        have : α.symm y ∈ D := hsubD ⟨y, hy, rfl⟩
        exact ⟨α.symm y, this, α.apply_symm_apply y⟩
      calc
        D = α.symm '' (α '' D) := by ext z; simp
        _ = α.symm '' C' := by rw [hD']
    · ext y
      simp
  · rintro ⟨C, ⟨hne, hsub, hpc, hmax⟩, rfl⟩
    refine ⟨hne.image α, image_mono hsub, hpc.image α.continuous, ?_⟩
    intro D' hD'F hD'pc hsubD'
    have hD : α.symm '' D' = C := by
      refine hmax (α.symm '' D') ?_ (hD'pc.image α.symm.continuous) ?_
      · rintro x ⟨y, hy, rfl⟩
        rcases hD'F hy with ⟨z, hz, rfl⟩
        simpa using hz
      · rintro x hx
        exact ⟨α x, hsubD' ⟨x, hx, rfl⟩, α.symm_apply_apply x⟩
    calc
      D' = α '' (α.symm '' D') := by ext y; simp
      _ = α '' C := by rw [hD]

/-- The image `α(H)` of a drawing `H` under a homeomorphism `α : Σ ≃ₜ Σ'`
(Graph Minors VII, Section 3, page 220). -/
def mapDrawingHomeo {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S') (H : Drawing S) :
    Drawing S' where
  U := α '' H.U
  V := α '' H.V
  V_subset_U := image_mono H.V_subset_U
  isClosed_U := (α.isClosed_image).mpr H.isClosed_U
  finite_V := H.finite_V.image α
  finite_edges := by
    have hdiff : α '' H.U \ α '' H.V = α '' (H.U \ H.V) :=
      (image_sdiff α.injective H.U H.V).symm
    rw [hdiff, arcComponentsIn_image_homeo]
    exact H.finite_edges.image (image α)
  edge_cond := by
    have hdiff : α '' H.U \ α '' H.V = α '' (H.U \ H.V) :=
      (image_sdiff α.injective H.U H.V).symm
    intro e' he'
    rw [hdiff, arcComponentsIn_image_homeo] at he'
    rcases he' with ⟨e, he, rfl⟩
    have hcap : closure (α '' e) ∩ α '' H.V = α '' (closure e ∩ H.V) := by
      rw [← α.image_closure, ← Set.image_inter α.injective]
    rcases H.edge_cond e he with ⟨u, v, huv, hcap_e, hL⟩ | ⟨u, hcap_e, hO⟩
    · left
      refine ⟨α u, α v, fun h => huv (α.injective h), ?_, ?_⟩
      · rw [hcap, hcap_e, image_pair]
      · rw [← α.image_closure]
        rcases hL with ⟨f, hf0, hf1⟩
        refine ⟨f.trans (α.image (closure e)), ?_, ?_⟩
        · change α (f 0).1 = α u
          rw [hf0]
        · change α (f 1).1 = α v
          rw [hf1]
    · right
      refine ⟨α u, ?_, ?_⟩
      · rw [hcap, hcap_e, image_singleton]
      · rw [← α.image_closure]
        rcases hO with ⟨f⟩
        exact ⟨f.trans (α.image (closure e))⟩

/-- "We say that forests $H_1, H_2$ in $\Sigma$ are *homoplastic* if there is a homeomorphism
$\alpha \colon \Sigma \to \Sigma$ such that (i) $\alpha(x) = x$ for all $x \in bd(\Sigma)$,
and (ii) the forest $\alpha(H_1)$ is homotopic in $\Sigma$ to $H_2$."
(Graph Minors VII, Section 3, page 220). -/
def ForestsHomoplastic (H₁ H₂ : Drawing S) : Prop :=
  ∃ α : S ≃ₜ S, (∀ x ∈ bd S, α x = x) ∧ ForestsHomotopic (mapDrawingHomeo α H₁) H₂

/-- "We say $Z \subseteq \Sigma$ is *simply connected* if $Z$ is arc-connected and every $O$-arc $F
\subseteq Z$ bounds a closed disc $\Delta \subseteq Z$." (Graph Minors VII, Section 11, page 253;
Section 2, page 214: "there is a closed disc $\Delta \subseteq \Sigma$ with $bd(\Delta) = F$"). -/
def IsSimplyConnectedSubset (Z : Set S) : Prop :=
  IsArcConnected Z ∧
    ∀ F : Set S, IsOArc F → F ⊆ Z → ∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F ∧ Δ ⊆ Z

/-- "An $X$-matching $G$ surrounds a $Y$-forest $H$ if $U(G) \cap U(H) = \emptyset$ and for each
component $H'$ of $H$ with $V(H') \cap bd(\Sigma) \ne \emptyset$ there is a simply connected region
of $G$ including $U(H')$."
(Graph Minors VII, Section 3, proof of (3.4), page 220). -/
def MatchingSurroundsForest (G H : Drawing S) : Prop :=
  G.U ∩ H.U = ∅ ∧
  ∀ H' : Drawing S, H'.IsSubdrawing H → H'.IsConnected → (H'.V ∩ bd S).Nonempty →
    ∃ r ∈ G.R, IsSimplyConnectedSubset r ∧ H'.U ⊆ r

/-- The property of an integer `w` satisfying Graph Minors VII, (3.6) (page 221) for `(Σ, k, n)`:
"for every matching $G$ in $\Sigma$ with $|V(G)| \le 2n$ and every forest $H$ in $\Sigma$
with $|V(H) \cap bd(\Sigma)| \le k$, there is a forest $H'$ homoplastic to $H$ with
$|U(G) \cap U(H')| \le w(\Sigma, k, n)$." -/
def IsW36Bound (S : Type u) [TopologicalSpace S] (k n w : ℕ) : Prop :=
  ∀ G H : Drawing S, IsMatching G → G.V.ncard ≤ 2 * n →
    IsSurfaceForest H → (H.V ∩ bd S).ncard ≤ k →
    ∃ H' : Drawing S, IsSurfaceForest H' ∧ ForestsHomoplastic H H' ∧
      (G.U ∩ H'.U).Finite ∧ (G.U ∩ H'.U).ncard ≤ w

/-- The integer `w(Σ, k, n)` of Graph Minors VII, (3.6) (page 221): the least `w : ℕ` satisfying
`IsW36Bound S k n w`. -/
noncomputable def wSurface (S : Type u) [TopologicalSpace S] (k n : ℕ) : ℕ :=
  sInf {w : ℕ | IsW36Bound S k n w}

/-! ## Section 4: The Main Result, First Version (pages 221–230) -/

/-- "Let $G$ be a graph in $\Sigma$, and let $H$ be a forest in $\Sigma$. If there exists a
forest $H'$ homoplastic to $H$ which is a subgraph of $G$, we say that $H$ is
*$G$-feasible*."
(Graph Minors VII, Section 4, page 221). -/
def IsGFeasible (G H : Drawing S) : Prop :=
  ∃ H' : Drawing S, IsSurfaceForest H' ∧ ForestsHomoplastic H H' ∧ H'.IsSubdrawing G

/-- "If $C$ is a cuff of a surface $\Sigma$, we denote by $\Sigma + \hat{C}$ the surface obtained
by pasting a closed disc onto $C$." (Graph Minors VII, Section 4, page 224).
Using `PasteDiscStatement` from `GraphMinor/Surface/TopologyStatements.lean`, `IsCappedCuff C S' j
D`
states that `S'` is a surface, `j : S → S'` is a topological embedding, `D ⊆ S'` is a closed disc
with `discBd D = j '' C`, and `range j ∪ D = univ` with `range j ∩ D = j '' C`. -/
structure IsCappedCuff (C : Set S) (S' : Type u) [TopologicalSpace S'] (j : S → S')
    (D : Set S') : Prop where
  cuff : IsCuff C
  isSurface : IsSurface S'
  isEmbedding : IsEmbedding j
  isClosedDisc : IsClosedDisc D
  discBd_eq : discBd D = j '' C
  union_eq : range j ∪ D = univ
  inter_eq : range j ∩ D = j '' C

/-- An `O`-arc `B ⊆ Σ` is *null-homotopic in `Σ + Ĉ`* (Graph Minors VII, Section 4, (4.6)(ii),
page 224): for every capped surface `Σ + Ĉ` obtained by pasting a closed disc onto the cuff `C`,
the
image of `B` in `Σ + Ĉ` is a null-homotopic `O`-arc. -/
def IsNullHomotopicOArcInCappedCuff (C B : Set S) : Prop :=
  IsCuff C ∧ IsOArc B ∧
    ∀ (S' : Type u) [TopologicalSpace S'] (j : S → S') (D : Set S'),
      IsCappedCuff C S' j D → IsNullHomotopicOArc (j '' B)

/-- A subset `X ⊆ Σ` is *planar in `Σ + Ĉ`* (Graph Minors VII, Section 5, page 230): for some
(equivalently, every) capped surface `Σ + Ĉ` obtained by pasting a closed disc onto the cuff `C`,
the image `j '' X` is included in a closed disc `Δ ⊆ Σ + Ĉ`. -/
def IsPlanarInCappedCuff (C X : Set S) : Prop :=
  IsCuff C ∧
    (∃ (S' : Type u) (_ : TopologicalSpace S') (j : S → S') (D : Set S'),
      IsCappedCuff C S' j D ∧ IsPlanar (j '' X)) ∧
    (∀ (S' : Type u) [TopologicalSpace S'] (j : S → S') (D : Set S'),
      IsCappedCuff C S' j D → IsPlanar (j '' X))

/-- "Let $w$ be the maximum of $$w(\Sigma', 2k, 3(2a + b + c - 1))$$ (as in (3.6)), taken over
all surfaces $\Sigma' \cong \Sigma(a, b, c')$, where $c' \le 2(2a + b + c - 1)$."
(Graph Minors VII, Section 4, page 224). Since `w(Σ', k, n)` is invariant under homeomorphism, we
take the maximum over `c' ≤ 2(2a + b + c - 1)` using the canonical surface model
`SurfaceModel a b c'`. -/
noncomputable def wMaxModel (a b c k : ℕ) : ℕ :=
  (Finset.range (2 * (2 * a + b + c - 1) + 1)).sup fun c' =>
    wSurface (SurfaceModel a b c') (2 * k) (3 * (2 * a + b + c - 1))

/-- "`μ = 2(2a + b + c)(k + w) + 2k`" (Graph Minors VII, Section 4, page 224). -/
noncomputable def muModel (a b c k : ℕ) : ℕ :=
  2 * (2 * a + b + c) * (k + wMaxModel a b c k) + 2 * k

/-- "v &= 6(2a + b + c - 1)(w + 2\mu + 1) + 2k. \end{aligned}$$ We define $v(\Sigma, k) = v$."
(Graph Minors VII, Section 4, page 224). -/
noncomputable def vModel (a b c k : ℕ) : ℕ :=
  6 * (2 * a + b + c - 1) * (wMaxModel a b c k + 2 * muModel a b c k + 1) + 2 * k

/-- The function `v(Σ, k)` of Graph Minors VII, Section 4 (page 224): for a surface `Σ ≅ Σ(a, b,
c)`,
`v(Σ, k) = vModel a b c k`. -/
noncomputable def vSurface (S : Type u) [TopologicalSpace S] (k : ℕ) : ℕ :=
  sInf {v : ℕ | ∃ a b c : ℕ, Nonempty (S ≃ₜ SurfaceModel a b c) ∧ v = vModel a b c k}

/-! ## Section 5: The Main Result, Second Version (pages 230–237) -/

/-- "We say that $X \subseteq \Sigma$ is *near-planar* if either $X$ is planar, or $X$ is planar in
$\Sigma + \hat{C}$, for some cuff $C$." (Graph Minors VII, Section 5, page 230). -/
def IsNearPlanar (X : Set S) : Prop :=
  IsPlanar X ∨ ∃ C ∈ cuffs S, IsPlanarInCappedCuff C X

/-- "We say that $X$ *surrounds* cuff $C$ (in $\Sigma$) if $X$ is planar in $\Sigma + \hat{C}$ but
not in $\Sigma$."
(Graph Minors VII, Section 5, page 230). -/
def SurroundsCuff (X C : Set S) : Prop :=
  C ∈ cuffs S ∧ IsPlanarInCappedCuff C X ∧ ¬ IsPlanar X

/-- A candidate set `X ⊆ Σ` in the definition of `α(G)` (Graph Minors VII, Section 5, page 230):
`X` is solid, connected, `G`-normal, and not near-planar. -/
def IsAlphaCandidate (G : Drawing S) (X : Set S) : Prop :=
  IsSolid X ∧ IsConnected X ∧ G.IsNormal X ∧ ¬ IsNearPlanar X

/-- "Let $G$ be a proper graph in $\Sigma$. We define $\alpha(G)$ to be the minimum of $|X \cap
V(G)|$, taken over all solid connected $G$-normal sets $X \subseteq \Sigma$ which are not
near-planar."
(Graph Minors VII, Section 5, page 230). -/
noncomputable def alpha (G : Drawing S) : ℕ :=
  sInf {n : ℕ | ∃ X : Set S, IsAlphaCandidate G X ∧ (X ∩ G.V).ncard = n}

/-- "If $G$ is proper in $\Sigma$, $C$ is a cuff of $\Sigma$, and $r \ge 0$ is an integer, we
define ... $\mathscr{A}_r(C)$ to be the union of all solid connected $G$-normal sets $X
\subseteq \Sigma$ which surround $C$ and for which $|V(G) \cap X| \le r$. If there is no
such $X$, $\mathscr{A}_r(C)$ is defined to be $\emptyset$."
(Graph Minors VII, Section 5, pages 230–231). -/
def scriptA (G : Drawing S) (r : ℕ) (C : Set S) : Set S :=
  ⋃₀ {X : Set S | IsSolid X ∧ IsConnected X ∧ G.IsNormal X ∧ SurroundsCuff X C ∧
    (G.V ∩ X).ncard ≤ r}

open Classical in
/-- "Let $G$ be a proper graph in $\Sigma$. If $x, y \in \Sigma$ are distinct, we define $d(x, y)$
to be $\min |U(G) \cap X|$, the minimum being taken over all $[0, 1]$-arcs $X$ with ends $x, y$. ...
If $x = y$, we ... define $d(x, y) = 0$ if $x \notin U(G)$, and $d(x, y) = 1$ if $x \in U(G)$."
(Graph Minors VII, Section 5, page 231). -/
noncomputable def distPoint (G : Drawing S) (x y : S) : ℕ :=
  if x = y then
    if x ∈ G.U then 1 else 0
  else
    sInf {n : ℕ | ∃ X : Set S, IsLineWithEnds X x y ∧ (G.U ∩ X).Finite ∧ (G.U ∩ X).ncard = n}

/-- "If ... $x \in \Sigma$ and $A \subseteq \Sigma$ is non-empty, we define $d(x, A)$ to be
$\min d(x, y)$, taken over all $y \in A$" (Graph Minors VII, Section 5, pages 231–232). -/
noncomputable def distSet (G : Drawing S) (x : S) (A : Set S) : ℕ :=
  sInf (distPoint G x '' A)

/-- "and for any integer $t \ge 0$ we define $$ Y_t(A) = \{x \in \Sigma : d(x, A) \le t\}. $$"
(Graph Minors VII, Section 5, page 232). -/
def nearSet (G : Drawing S) (t : ℕ) (A : Set S) : Set S :=
  {x : S | ∃ y ∈ A, distPoint G x y ≤ t}

/-- "If $\Sigma \cong \Sigma(a, b, c)$ where $3a + 3b + c \ge 3$, and $F$ is a null-homotopic
$O$-arc, then there is a unique closed disc $\Delta \subseteq \Sigma$ with boundary $F$. If
$x \in \Delta - F$ we say that $x$ is *inside* $F$ (in $\Sigma$)." (Graph Minors VII, Section 5,
page 232). -/
def IsPointInsideNullOArc (F : Set S) (x : S) : Prop :=
  IsNullHomotopicOArc F ∧ ∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F ∧ x ∈ Δ \ F

/-- "If $F$ is an $O$-arc surrounding a cuff $C$ and $x \in \Sigma$, we say that $x$ is *inside* $F$
in $\Sigma$ if it is inside $F$ in $\Sigma + \hat{C}$." (Graph Minors VII, Section 5, page 232). -/
def IsPointInsideSurroundingOArc (C F : Set S) (x : S) : Prop :=
  IsOArc F ∧ SurroundsCuff F C ∧
    (∃ (S' : Type u) (_ : TopologicalSpace S') (j : S → S') (D : Set S'),
      IsCappedCuff C S' j D ∧ IsPointInsideNullOArc (j '' F) (j x)) ∧
    (∀ (S' : Type u) [TopologicalSpace S'] (j : S → S') (D : Set S'),
      IsCappedCuff C S' j D → IsPointInsideNullOArc (j '' F) (j x))

/-- A point `x ∈ Σ` is *inside* an `O`-arc `F` in `Σ` (either `F` is null-homotopic or `F` surrounds
some cuff `C` of `Σ`; Graph Minors VII, Section 5, page 232). -/
def IsPointInsideOArc (F : Set S) (x : S) : Prop :=
  IsPointInsideNullOArc F x ∨ ∃ C ∈ cuffs S, IsPointInsideSurroundingOArc C F x

/-- "If $X \subseteq \Sigma$, we say that $X$ is *inside* $F$ if every $x \in X$ is inside $F$."
(Graph Minors VII, Section 5, page 232). -/
def IsInsideOArc (X F : Set S) : Prop :=
  ∀ x ∈ X, IsPointInsideOArc F x

/-- "Let $G$ be a proper graph in $\Sigma$. We say that $G$ is *boundary-linked* if for every
cuff $C$ of $\Sigma$ and every $G$-normal $O$-arc $F$ surrounding $C$, $|V(G) \cap F| \ge
|V(G) \cap C|$."
(Graph Minors VII, Section 5, page 233). -/
def IsBoundaryLinked (G : Drawing S) : Prop :=
  G.IsProper ∧
    ∀ C ∈ cuffs S, ∀ F : Set S, G.IsNormal F → IsOArc F → SurroundsCuff F C →
      (G.V ∩ C).ncard ≤ (G.V ∩ F).ncard

/-! ## Section 7: Adding New Cuffs (pages 238–241) -/

/-- The sets whose union is `𝒜_r(C)` (Graph Minors VII, Section 5, pages 230–231): solid, connected,
`G`-normal, surrounding
`C`, with at most `r` vertices of `G`. -/
def IsScriptASet (G : Drawing S) (r : ℕ) (C X : Set S) : Prop :=
  IsSolid X ∧ IsConnected X ∧ G.IsNormal X ∧ SurroundsCuff X C ∧ (G.V ∩ X).ncard ≤ r

/-- A *hole* of `X` around `C`: a component `K` of `Σ - X` that lies in a closed disc of `Σ + CHat`
with boundary in `X`. -/
def IsInnerHole (C X K : Set S) : Prop :=
  K ∈ componentsIn (univ \ X) ∧
    ∃ (S' : Type u) (_ : TopologicalSpace S') (j : S → S') (D Δ : Set S'),
      IsCappedCuff C S' j D ∧ IsClosedDisc Δ ∧ discBd Δ ⊆ j '' X ∧ j '' K ⊆ Δ

/-- The set `Δ_r(C)` of Graph Minors VII, Section 7 (page 238), which the paper calls the set of
points inside an `O`-arc
`A_r(C) ⊆ bd(Σ) ∪ U(G)` with `A_r(C) ⊆ 𝒜_{r+1}(C)` and `𝒜_r(C)` inside `A_r(C)`.

No such `O`-arc exists as printed. A point of `𝒜_{r+1}(C)` lies in a `G`-normal set, so it is not on
an edge. Thus `A_r(C)` would
lie in `bd(Σ)`, and it would be `C`, which has no points inside it. We take what the proofs of (7.1)
and (7.3) use: `Δ_r(C)` is
the set of points of the sets `X` of `𝒜_r(C)` and of their holes around `C`. So it is `𝒜_r(C)` with
its holes filled in, the
set bounded by the `O`-arc of the paper. See the correction on page 238 in `corrections/GM07.md`. -/
def cuffInsideSet (G : Drawing S) (r : ℕ) (C : Set S) : Set S :=
  ⋃₀ {Y : Set S | ∃ X : Set S, IsScriptASet G r C X ∧ (Y = X ∨ IsInnerHole C X Y)}

/-- "We define $\Delta_r$ to be the union of $\Delta_r(C)$ taken over all cuffs $C$ with
$\mathcal{A}_r(C) \ne \emptyset$."
(Graph Minors VII, Section 7, page 238). -/
def allCuffsInsideSet (G : Drawing S) (r : ℕ) : Set S :=
  ⋃ C ∈ {C ∈ cuffs S | (scriptA G r C).Nonempty}, cuffInsideSet G r C

/-! ## Section 8: Schisms (pages 241–242) -/

/-- An `X₁`-arc in `Σ` (Graph Minors VII, Section 8, page 241):
"$G_1$ has exactly two vertices ($u$, $v$ say) and three edges, one a loop on $u$, one a loop
on $v$, and the other joining $u$, $v$". Thus `X` is the union of two disjoint `O`-arcs `A₁, A₂` and
a
`[0, 1]`-arc `P` with ends `u ∈ A₁` and `v ∈ A₂` meeting `A₁ ∪ A₂` only at `{u, v}`. -/
def IsX1Arc (X : Set S) : Prop :=
  ∃ A₁ A₂ P : Set S, ∃ u v : S,
    IsOArc A₁ ∧ IsOArc A₂ ∧ Disjoint A₁ A₂ ∧
    IsLineWithEnds P u v ∧ u ∈ A₁ ∧ v ∈ A₂ ∧
    P ∩ A₁ = {u} ∧ P ∩ A₂ = {v} ∧ X = A₁ ∪ A₂ ∪ P

/-- An `X₂`-arc in `Σ` (Graph Minors VII, Section 8, page 241):
"$G_2$ has exactly one vertex and two edges". Thus `X` is the union of two `O`-arcs `A₁, A₂`
intersecting at a single point `u`. -/
def IsX2Arc (X : Set S) : Prop :=
  ∃ A₁ A₂ : Set S, ∃ u : S,
    IsOArc A₁ ∧ IsOArc A₂ ∧ A₁ ∩ A₂ = {u} ∧ X = A₁ ∪ A₂

/-- An `X₃`-arc in `Σ` (Graph Minors VII, Section 8, page 241):
"$G_3$ has two vertices and three edges, mutually parallel". Thus `X` is the union of three
`[0, 1]`-arcs `P₁, P₂, P₃` with common distinct ends `u, v`, pairwise intersecting only at
`{u, v}`. -/
def IsX3Arc (X : Set S) : Prop :=
  ∃ P₁ P₂ P₃ : Set S, ∃ u v : S,
    u ≠ v ∧ IsLineWithEnds P₁ u v ∧ IsLineWithEnds P₂ u v ∧ IsLineWithEnds P₃ u v ∧
    P₁ ∩ P₂ = {u, v} ∧ P₁ ∩ P₃ = {u, v} ∧ P₂ ∩ P₃ = {u, v} ∧ X = P₁ ∪ P₂ ∪ P₃

/-- An `X₄`-arc in `Σ` with end `w` (Graph Minors VII, Section 8, page 241):
"Let $X_4$ be the topological space of the graph $G_4$ consisting of two vertices and two
edges, with exactly one loop. The *end* of an $X_4$-arc is defined to be the point
representing the monovalent vertex of $G_4$." Thus `X` is the union of an `O`-arc `A` and a `[0,
1]`-arc `P` with ends `u, w`
such that `P ∩ A = {u}` and `w ∉ A`. -/
def IsX4ArcWithEnd (X : Set S) (w : S) : Prop :=
  ∃ A P : Set S, ∃ u : S,
    IsOArc A ∧ IsLineWithEnds P u w ∧ u ≠ w ∧ P ∩ A = {u} ∧ X = A ∪ P

/-- `X` is an `X₄`-arc in `Σ` (Graph Minors VII, Section 8, page 241). -/
def IsX4Arc (X : Set S) : Prop :=
  ∃ w : S, IsX4ArcWithEnd X w

/-- "We say that $X \subseteq \Sigma$ is *schismatic* if $X$ is either an $O$-arc or an $X_i$-arc
for some $i$, and $X$ is not near-planar, and every proper subset of $X$ which is an $O$-arc
is near-planar."
(Graph Minors VII, Section 8, page 241). Here `i ∈ {1, 2, 3}`. -/
def IsSchismatic (X : Set S) : Prop :=
  (IsOArc X ∨ IsX1Arc X ∨ IsX2Arc X ∨ IsX3Arc X) ∧
  ¬ IsNearPlanar X ∧
  ∀ F : Set S, IsOArc F → F ⊂ X → IsNearPlanar F

/-- "By a *schism* in a surface $\Sigma \cong \Sigma(a, b, c)$ where $3a + 3b + c \ge 3$ we mean
a subset of $\Sigma$ which is one of the following: (i) An $O$-arc $F$ which is not
near-planar, with $|F \cap bd(\Sigma)| \le 1$, (ii) a proper $I$-arc with its ends in
distinct cuffs, (iii) a proper $I$-arc $F$ with its ends in the same cuff $C$, such that $F
\cup C$ is not near-planar, ... (iv) an $X_1$-arc or $X_2$-arc such that both its $O$-arcs
surround distinct cuffs of $\Sigma$, and which contains no point of $bd(\Sigma)$, (v) an
$X_3$-arc such that all three of its $O$-arcs surround distinct cuffs, and which contains no
point of $bd(\Sigma)$, (vi) an $X_4$-arc with its end in one cuff and its $O$-arc
surrounding another cuff, containing only one point of $bd(\Sigma)$."
(Graph Minors VII, Section 8, pages 241–242). -/
def IsSchism (X : Set S) : Prop :=
  -- (i) An O-arc F which is not near-planar, with |F ∩ bd(Σ)| ≤ 1
  (IsOArc X ∧ ¬ IsNearPlanar X ∧ (X ∩ bd S).Finite ∧ (X ∩ bd S).ncard ≤ 1) ∨
  -- (ii) a proper I-arc with its ends in distinct cuffs
  (IsProperIArc X ∧ ∃ C₁ ∈ cuffs S, ∃ C₂ ∈ cuffs S, C₁ ≠ C₂ ∧
    (lineEnds X ∩ C₁).Nonempty ∧ (lineEnds X ∩ C₂).Nonempty) ∨
  -- (iii) a proper I-arc F with its ends in the same cuff C, such that F ∪ C is not near-planar
  (IsProperIArc X ∧ ∃ C ∈ cuffs S, lineEnds X ⊆ C ∧ ¬ IsNearPlanar (X ∪ C)) ∨
  -- (iv) an X₁-arc or X₂-arc such that both its O-arcs surround distinct cuffs of Σ, and which
  -- contains no point of bd(Σ)
  ((IsX1Arc X ∨ IsX2Arc X) ∧ X ∩ bd S = ∅ ∧
    ∃ A₁ A₂ C₁ C₂ : Set S, IsOArc A₁ ∧ IsOArc A₂ ∧ A₁ ⊆ X ∧ A₂ ⊆ X ∧
      C₁ ∈ cuffs S ∧ C₂ ∈ cuffs S ∧ C₁ ≠ C₂ ∧
      SurroundsCuff A₁ C₁ ∧ SurroundsCuff A₂ C₂) ∨
  -- (v) an X₃-arc such that all three of its O-arcs surround distinct cuffs, and which contains no
  -- point of bd(Σ)
  (IsX3Arc X ∧ X ∩ bd S = ∅ ∧
    ∃ A₁ A₂ A₃ C₁ C₂ C₃ : Set S,
      IsOArc A₁ ∧ IsOArc A₂ ∧ IsOArc A₃ ∧ A₁ ⊆ X ∧ A₂ ⊆ X ∧ A₃ ⊆ X ∧
      C₁ ∈ cuffs S ∧ C₂ ∈ cuffs S ∧ C₃ ∈ cuffs S ∧
      C₁ ≠ C₂ ∧ C₁ ≠ C₃ ∧ C₂ ≠ C₃ ∧
      SurroundsCuff A₁ C₁ ∧ SurroundsCuff A₂ C₂ ∧ SurroundsCuff A₃ C₃) ∨
  -- (vi) an X₄-arc with its end in one cuff and its O-arc surrounding another cuff, containing only
  -- one point of bd(Σ)
  (∃ w : S, ∃ A P C₁ C₂ : Set S, ∃ u : S,
    IsOArc A ∧ IsLineWithEnds P u w ∧ u ≠ w ∧ P ∩ A = {u} ∧ X = A ∪ P ∧
    C₁ ∈ cuffs S ∧ C₂ ∈ cuffs S ∧ C₁ ≠ C₂ ∧
    w ∈ C₁ ∧ SurroundsCuff A C₂ ∧ X ∩ bd S = {w})

/-- "If $G$ is a proper graph in $\Sigma$, let us define $\omega(G)$ to be the minimum of $|V(G)
\cap X|$ taken over all $G$-normal schisms $X$ in $\Sigma$."
(Graph Minors VII, Section 8, page 242). -/
noncomputable def omega (G : Drawing S) : ℕ :=
  sInf {n : ℕ | ∃ X : Set S, G.IsNormal X ∧ IsSchism X ∧ (G.V ∩ X).ncard = n}

/-! ## Section 9: Minors (pages 242–246) -/

/-- "A digraph $(G, G^+, G^-)$ in a surface $\Sigma$ consists of a graph $G$ in $\Sigma$ and two
functions $G^+, G^- \colon E(G) \to V(G)$ such that for every edge $e$ of $G$, $\{G^+(e),
G^-(e)\} = \bar{e} - e$."
(Graph Minors VII, Section 9, page 242). -/
structure SurfaceDigraph (S : Type u) [TopologicalSpace S] where
  /-- The underlying graph `G` in `Σ`. -/
  G : Drawing S
  /-- The head function `G⁺ : E(G) → V(G)`. -/
  plus : Set S → S
  /-- The tail function `G⁻ : E(G) → V(G)`. -/
  minus : Set S → S
  /-- For every edge `e` of `G`, `G⁺(e) ∈ V(G)`. -/
  plus_mem : ∀ e ∈ G.E, plus e ∈ G.V
  /-- For every edge `e` of `G`, `G⁻(e) ∈ V(G)`. -/
  minus_mem : ∀ e ∈ G.E, minus e ∈ G.V
  /-- For every edge `e` of `G`, `{G⁺(e), G⁻(e)} = eBar - e`. -/
  ends_eq : ∀ e ∈ G.E, ({plus e, minus e} : Set S) = tilde e

namespace SurfaceDigraph

/-- "The digraph is proper if `G` is proper." (Graph Minors VII, Section 9, page 242). -/
def IsProper (D : SurfaceDigraph S) : Prop :=
  D.G.IsProper

end SurfaceDigraph

/-- "Let $(G, G^+, G^-)$, $(H, H^+, H^-)$ be proper digraphs in $\Sigma$. We say that $(H, H^+,
H^-)$ is a *boundary-rooted minor* of $(G, G^+, G^-)$ if $V(H) \cap bd(\Sigma) = V(G) \cap
bd(\Sigma)$ and if for each vertex $v$ of $H$ there is a non-null connected subgraph
$\phi(v)$ of $G$, and for each edge $e$ of $H$ there is an edge $\phi(e)$ of $G$, such that
(i) for distinct $v, v' \in V(H)$, $\phi(v)$ and $\phi(v')$ are vertex-disjoint, (ii) for
distinct $e, e' \in E(H)$, $\phi(e)$ and $\phi(e')$ are distinct, (iii) for $v \in V(H)$ and
$e \in E(H)$, $\phi(e)$ is not an edge of $\phi(v)$, (iv) for $e \in E(H)$, $G^+(\phi(e))$
is a vertex of $\phi(H^+(e))$, and $G^-(\phi(e))$ is a vertex of $\phi(H^-(e))$, and (v) for
$v \in V(H) \cap bd(\Sigma)$, $v$ is a vertex of $\phi(v)$."
(Graph Minors VII, Section 9, page 242). -/
def IsBoundaryRootedMinor (H G : SurfaceDigraph S) : Prop :=
  H.G.V ∩ bd S = G.G.V ∩ bd S ∧
  ∃ (φv : S → Drawing S) (φe : Set S → Set S),
    (∀ v ∈ H.G.V, (φv v).IsSubdrawing G.G ∧ (φv v).V.Nonempty ∧ (φv v).IsConnected) ∧
    (∀ e ∈ H.G.E, φe e ∈ G.G.E) ∧
    -- (i) for distinct v, v' ∈ V(H), φ(v) and φ(v') are vertex-disjoint
    (∀ v ∈ H.G.V, ∀ v' ∈ H.G.V, v ≠ v' → Disjoint (φv v).V (φv v').V) ∧
    -- (ii) for distinct e, e' ∈ E(H), φ(e) and φ(e') are distinct
    (∀ e ∈ H.G.E, ∀ e' ∈ H.G.E, e ≠ e' → φe e ≠ φe e') ∧
    -- (iii) for v ∈ V(H) and e ∈ E(H), φ(e) is not an edge of φ(v)
    (∀ v ∈ H.G.V, ∀ e ∈ H.G.E, φe e ∉ (φv v).E) ∧
    -- (iv) for e ∈ E(H), G⁺(φ(e)) is a vertex of φ(H⁺(e)), and G⁻(φ(e)) is a vertex of φ(H⁻(e))
    (∀ e ∈ H.G.E, G.plus (φe e) ∈ (φv (H.plus e)).V ∧ G.minus (φe e) ∈ (φv (H.minus e)).V) ∧
    -- (v) for v ∈ V(H) ∩ bd(Σ), v is a vertex of φ(v)
    (∀ v ∈ H.G.V ∩ bd S, v ∈ (φv v).V)

/-- "If $bd(\Sigma) = \emptyset$ and $(H, H^+, H^-)$, $(G, G^+, G^-)$ are digraphs in $\Sigma$,
and the first is a boundary-rooted minor of the second, we say that it is a *minor* of the
second."
(Graph Minors VII, Section 9, page 243). -/
def IsDigraphMinor (H G : SurfaceDigraph S) : Prop :=
  bd S = ∅ ∧ IsBoundaryRootedMinor H G

/-- The number `g` of isolated vertices of `H` which are not in `bd(Σ)`
(Graph Minors VII, Section 9, (9.1), page 242). -/
noncomputable def numInternalIsolatedVertices (H : Drawing S) : ℕ :=
  {v ∈ H.V \ bd S | IsIsolatedVertex H v}.ncard

/-- Statement of Graph Minors VII, (9.1) (pages 242–243):
"Let $\Sigma \cong \Sigma(a, b, c)$ where $3a + 3b + c \ge 3$. Let $(H, H^+, H^-)$ be a
proper digraph in $\Sigma$. Let $g$ be the number of isolated vertices of $H$ which are not
in $bd(\Sigma)$. Let $k$ be an integer with* $$2k \ge 4|E(H)| + 4g + |V(H) \cap bd(\Sigma)|
+ 2c + 2$$ *and let $c_0$ be an integer with $c_0 \ge c + |E(H)| + g + 1$. Let $(G, G^+,
G^-)$ be a proper digraph in $\Sigma$ such that* ... (i) $V(G) \cap bd(\Sigma) = V(H) \cap
bd(\Sigma)$, (ii) $G$ *is boundary-linked, and* (iii) $\alpha(G) \ge 42k 5^{(g+|E(H)|)}
v(\Sigma(a, b, c_0), k)$. *Then $(H, H^+, H^-)$ is a boundary-rooted minor of $(G, G^+,
G^-)$." -/
def GM07Theorem91Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T1Space S],
    IsSurface S →
    ∀ a b c : ℕ, 3 * a + 3 * b + c ≥ 3 → Nonempty (S ≃ₜ SurfaceModel a b c) →
    ∀ H : SurfaceDigraph S, H.IsProper →
    ∀ k c₀ : ℕ,
      let g := numInternalIsolatedVertices H.G
      2 * k ≥ 4 * H.G.E.ncard + 4 * g + (H.G.V ∩ bd S).ncard + 2 * c + 2 →
      c₀ ≥ c + H.G.E.ncard + g + 1 →
      ∀ G : SurfaceDigraph S, G.IsProper →
        G.G.V ∩ bd S = H.G.V ∩ bd S →
        IsBoundaryLinked G.G →
        alpha G.G ≥ 42 * k * 5 ^ (g + H.G.E.ncard) * vModel a b c₀ k →
        IsBoundaryRootedMinor H G

/-- Statement of Graph Minors VII, (9.2) (page 244):
"Let $\Sigma \cong \Sigma(a, b, 0)$ where $a + b \ge 1$, and let $(H, H^+, H^-)$ be a digraph
in $\Sigma$. Then there is a number $N$ such that $(H, H^+, H^-)$ is a minor of every
digraph $(G, G^+, G^-)$ in $\Sigma$ with $\alpha(G) \ge N$." -/
def GM07Theorem92Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T1Space S],
    IsSurface S →
    ∀ a b : ℕ, a + b ≥ 1 → Nonempty (S ≃ₜ SurfaceModel a b 0) →
    ∀ H : SurfaceDigraph S,
      ∃ N : ℕ, ∀ G : SurfaceDigraph S, alpha G.G ≥ N → IsDigraphMinor H G

/-- There exist `k` mutually vertex-disjoint paths `P₁, …, P_k` of `G`, each with initial vertex in
`X` and terminal vertex in `Y` (Graph Minors VII, Section 9, page 244). -/
def HasDisjointPathsBetween (G : Drawing S) (X Y : Set S) (k : ℕ) : Prop :=
  ∃ (P : Fin k → Drawing S) (s t : Fin k → S),
    (∀ i : Fin k, (P i).IsSubdrawing G ∧ s i ∈ X ∧ t i ∈ Y ∧ (P i).IsPathBetween (s i) (t i)) ∧
    ∀ i j : Fin k, i ≠ j → Disjoint (P i).V (P j).V

/-- "If $G$ is a proper graph in a surface $\Sigma$, and $X, Y \subseteq \Sigma$ are disjoint, we
define $k(X, Y)$ to be the maximum value of $k$ such that there are paths $P_1, \dots, P_k$
of $G$, mutually disjoint, and each with initial vertex in $X$ and terminal vertex in $Y$."
(Graph Minors VII, Section 9, page 244). -/
noncomputable def maxDisjointPaths (G : Drawing S) (X Y : Set S) : ℕ :=
  sSup {k : ℕ | HasDisjointPathsBetween G X Y k}

/-- `84(t + 2) v(Σ(0, 0, t + 4), 2t + 4)` where `t = |V(H)| + |E(H)|`. Graph Minors VII,
(9.3)–(9.5) (pages 244–246), takes `r = 84(t + 2) 5^t v(Σ(0, 0, t + 4), 2t + 4)`, which is this
number times `5 ^ t`. -/
noncomputable def rCylinderBound (H : Drawing S) : ℕ :=
  let t := H.V.ncard + H.E.ncard
  84 * (t + 2) * vModel 0 0 (t + 4) (2 * t + 4)

/-- In a cylinder `Σ` with cuffs `C₁, C₂`, disjoint non-null-homotopic `O`-arcs `F₁, F₂` occur on
`Σ` in the order `C₁, F₂, F₁, C₂` (Graph Minors VII, Section 9, (9.3)(i), page 244): `F₂` separates
`C₁` from `F₁ ∪ C₂`, and `F₁` separates `C₁ ∪ F₂` from `C₂` (equivalently, in `Σ + Ĉ₁`, `C₁` is
inside `F₂` and `F₂` is inside `F₁`). -/
def CylinderOArcsInOrder (C₁ F₂ F₁ C₂ : Set S) : Prop :=
  C₁ ∈ cuffs S ∧ C₂ ∈ cuffs S ∧ C₁ ≠ C₂ ∧
  IsOArc F₁ ∧ IsOArc F₂ ∧ Disjoint F₁ F₂ ∧
  ¬ IsNullHomotopicOArc F₁ ∧ ¬ IsNullHomotopicOArc F₂ ∧
  SurroundsCuff F₂ C₁ ∧ SurroundsCuff F₁ C₁ ∧
  IsInsideOArc F₂ F₁

/-! ## Section 11: Appendix (pages 248–254) -/

/-- "The arc-components of $Z \subseteq \Sigma$ are the maximal arc-connected subsets of $Z$;
they partition $Z$." (Graph Minors VII, Section 11, page 251). -/
def IsArcComponentOf (A Z : Set S) : Prop :=
  Maximal (fun B : Set S => B ⊆ Z ∧ IsArcConnected B) A

/-! ### Small structural checks -/

/-- The empty drawing in any space `S` has no vertices and no edges, and is proper and a forest. -/
def emptyDrawing (S : Type u) [TopologicalSpace S] : Drawing S where
  U := ∅
  V := ∅
  V_subset_U := Subset.rfl
  isClosed_U := isClosed_empty
  finite_V := finite_empty
  finite_edges := by
    have : arcComponentsIn ((∅ : Set S) \ ∅) = ∅ := by
      ext C
      constructor
      · intro h
        exfalso
        exact h.1.ne_empty (subset_empty_iff.mp (h.2.1.trans sdiff_subset))
      · intro h
        exact False.elim h
    rw [this]
    exact finite_empty
  edge_cond := by
    intro e he
    exfalso
    exact he.1.ne_empty (subset_empty_iff.mp (he.2.1.trans sdiff_subset))

/-- The empty digraph `(∅, _, _)` in a nonempty space `S` is proper and is a boundary-rooted minor
of itself. -/
noncomputable def emptySurfaceDigraph (S : Type u) [TopologicalSpace S] [Nonempty S] :
    SurfaceDigraph S where
  G := emptyDrawing S
  plus := fun _ => Classical.arbitrary S
  minus := fun _ => Classical.arbitrary S
  plus_mem := fun _ he => False.elim (he.1.ne_empty (subset_empty_iff.mp
    (he.2.1.trans sdiff_subset)))
  minus_mem := fun _ he => False.elim (he.1.ne_empty (subset_empty_iff.mp
    (he.2.1.trans sdiff_subset)))
  ends_eq := fun _ he => False.elim (he.1.ne_empty (subset_empty_iff.mp
    (he.2.1.trans sdiff_subset)))

/-- Every proper digraph is a boundary-rooted minor of itself when each vertex `v ∈ V(H)` is mapped
to the single-vertex subdrawing `({v}, {v})` and each edge to itself. -/
theorem isBoundaryRootedMinor_refl [T1Space S] (H : SurfaceDigraph S) :
    IsBoundaryRootedMinor H H := by
  have hspanV : ∀ {v : S}, v ∈ H.G.V → (H.G.span {v} ∅).V = {v} := by
    intro v hv
    simp [Drawing.span_V, Drawing.spanV, hv]
  refine ⟨rfl, fun v => H.G.span {v} ∅, id, ?_, fun _ h => h, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    refine ⟨⟨H.G.spanV_subset {v} ∅, ?_⟩, ?_, ?_⟩
    · rw [H.G.span_E]
      exact inter_subset_right
    · rw [hspanV hv]
      exact singleton_nonempty v
    · refine ⟨by rw [hspanV hv]; exact singleton_nonempty v, ?_⟩
      intro u hu w hw
      have huV : u ∈ ((H.G.span {v} ∅).toGraph).vertexSet := hu
      rw [hspanV hv] at hu hw
      rcases mem_singleton_iff.mp hu with rfl
      rcases mem_singleton_iff.mp hw with rfl
      exact ⟨.nil huV⟩
  · intro v hv v' hv' hne
    rw [hspanV hv, hspanV hv']
    exact disjoint_singleton.mpr hne
  · intro _ _ _ _ hne
    exact hne
  · intro v _ e _
    rw [H.G.span_E, empty_inter]
    exact notMem_empty e
  · intro e he
    rw [hspanV (H.plus_mem e he), hspanV (H.minus_mem e he)]
    exact ⟨mem_singleton _, mem_singleton _⟩
  · intro v hv
    rw [hspanV hv.1]
    exact mem_singleton v

/-- Strengthened surrounding relation for Graph Minors VII, (3.4) (page 220). The paper's definition
omits that distinct components of `H` meeting `bd(Σ)` lie in distinct regions of `G`. Here, in
addition to
`MatchingSurroundsForest G H`, distinct components of `H` meeting `bd(Σ)` lie in distinct regions
of `G` (so any two boundary vertices of `H` lying in the same region of `G` are joined by a simple
walk in `H`). Without this condition, Claim (2) of (3.4) fails on a closed disc when a single region
of `G` contains two boundary vertices `y₁, y₂ ∈ Y`. -/
def MatchingStrictlySurroundsForest (G H : Drawing S) : Prop :=
  MatchingSurroundsForest G H ∧
  ∀ s ∈ H.V ∩ bd S, ∀ t ∈ H.V ∩ bd S, s ≠ t →
    ∀ r ∈ G.R, s ∈ r → t ∈ r → ∃ P : GraphWalk H.toGraph s t, P.IsSimple

/-- Graph Minors VII, (3.4), Claim (1) (page 220):
For any surface `Σ` and finite `Y ⊆ bd(Σ)`, choosing pairwise disjoint boundary `I`-arcs `F_y`
(`y ∈ Y`) with `y ∈ F_y \ lineEnds F_y` and letting `X` be the set of ends of all the `F_y`
(`|X| = 2|Y|`), every `Y`-forest `H` in `Σ` is surrounded by some `X`-matching `G` in `Σ`
(obtained by thickening each component of `H` into a closed disc meeting `bd(Σ)` in the
corresponding `F_y`). The surrounding here is the strict one. The statement is proved as
`forestSurroundingMatching` in `GM07/CuffSlide.lean`. -/
def ForestSurroundingMatchingStatement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S], IsSurface S →
    ∀ {Y : Set S}, Y ⊆ bd S → Y.Finite →
    ∃ X : Set S, X ⊆ bd S ∧ X.Finite ∧ X.ncard = 2 * Y.ncard ∧
      ∀ H : Drawing S, IsYForest Y H →
        ∃ G : Drawing S, IsXMatching X G ∧ MatchingStrictlySurroundsForest G H

/-- Graph Minors VII, (3.5) (page 221):
"(3.5) *For every matching $G$ in $\Sigma$ and every homoplasty class $\mathscr{B}$ there exists
$H \in \mathscr{B}$ with $U(G) \cap U(H)$ finite.*" The statement is proved as
`forestMatchingFiniteIntersection` in `GM07/Section35.lean`. -/
def ForestMatchingFiniteIntersectionStatement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S], IsSurface S →
    ∀ G H₀ : Drawing S, IsMatching G → IsSurfaceForest H₀ →
      ∃ H : Drawing S, IsSurfaceForest H ∧ ForestsHomoplastic H₀ H ∧ (G.U ∩ H.U).Finite

/-- Graph Minors VII, (4.1) (page 221):
Translation on a closed disc `Δ` between Theorem (3.6) of Graph Minors VI (`GM06.Statement36`,
stated in terms of divisions and `(x, y)`-chains) and Graph Minors VII, (4.1) (stated in terms of
`IsGFeasible G H` and `G`-normal proper `I`-arcs `F` separating components of `H`). The statement
is proved as `discFeasibilityArcTranslation` in `GM07/Section41.lean`. -/
def DiscFeasibilityArcTranslationStatement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T1Space S],
    IsSurface S → IsClosedDisc (univ : Set S) →
    ∀ G H : Drawing S, G.IsProper → IsSurfaceForest H →
      H.V ∩ bd S = G.V ∩ bd S →
      (IsGFeasible G H ↔
        ∀ (F : Set S) (s t : S) (C₁ C₂ : Set S),
          G.IsNormal F → IsProperIArc F → IsLineWithEnds F s t →
          componentsIn (bd S \ {s, t}) = {C₁, C₂} → C₁ ≠ C₂ →
          {V₀ : Set S | ∃ H' : Drawing S,
            GM06.IsGraphComponent H'.toGraph H.toGraph ∧ V₀ = H'.V ∧
            (V₀ ∩ C₁).Nonempty ∧ (V₀ ∩ C₂).Nonempty ∧ s ∉ V₀ ∧ t ∉ V₀}.ncard ≤
            (G.V ∩ (F \ {s, t})).ncard)

/-- Corrected conclusion of Graph Minors VII, (4.3) (pages 222–223). The indexed paths may
repeat when a path has no internal vertex. The printed statement reads:
"(4.3) *Let $\Sigma$ be a connected surface with at least two cuffs, and let $G$ be a proper graph
in $\Sigma$. Let $v \ge 0$ be an integer, and suppose that every $G$-normal $O$-arc $F$ with
$F \cap bd(\Sigma) = \emptyset$ and $|V(G) \cap F| \le v$ is null-homotopic. Let $C$ be a cuff.
Then there are at least $v + 1$ paths of $G$, each with one end in $C$ and the other in
$bd(\Sigma) - C$, mutually vertex-disjoint except for their ends.*" -/
def CuffToRestDisjointPathsStatement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T1Space S],
    IsSurface S → ConnectedSpace S → 2 ≤ (cuffs S).ncard →
    ∀ (G : Drawing S) (v : ℕ), G.IsProper →
      (∀ F : Set S, G.IsNormal F → IsOArc F → F ∩ bd S = ∅ → (G.V ∩ F).ncard ≤ v →
        IsNullHomotopicOArc F) →
      ∀ C ∈ cuffs S,
        ∃ (P : Fin (v + 1) → Drawing S) (s t : Fin (v + 1) → S),
          (∀ i : Fin (v + 1), (P i).IsSubdrawing G ∧ s i ∈ C ∧ t i ∈ bd S \ C ∧
            (P i).IsPathBetween (s i) (t i)) ∧
          (∀ i j : Fin (v + 1), i ≠ j →
            Disjoint ((P i).V \ {s i, t i}) ((P j).V \ {s j, t j}))

end GraphMinor.GM07
