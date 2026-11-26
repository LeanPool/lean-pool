/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.Defs2
public import LeanPool.GraphMinor.GM19.Defs
public import LeanPool.GraphMinor.Surface.TopologyStatements

/-!
# Definitions for Graph Minors XVII: Taming a vortex

This file formalizes the definitions behind the statements of N. Robertson and P. D. Seymour,
*Graph Minors. XVII. Taming a vortex*, J. Combin. Theory Ser. B 77 (1999) 162–210, that Graph
Minors XX cites: paintings without marches (`Painting`, Section 1), portrayals
(`Portrayal`, Section 2), warp (Section 3), central portrayals and small subhypergraphs (Section 4),
simpler and resembling portrayals (Section 5), `z`-redundancy (Section 6), truth and true portrayals
(Section 8), and tangles controlling a minor (Section 13). The surfaces `Σ(a, b, c)` and the
relation
"simpler" of Section 1 are `Surface.SurfaceModel` and `Surface.IsSimplerThan`.

The surfaces of a portrayal live in `Type`. This loses nothing, since every compact surface is
homeomorphic to a space in `Type`.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface GraphMinor.GM10

universe u v

/-! ### Paintings (Section 1, pages 164–165) -/

/-- A painting (Graph Minors XVII, Section 1, page 164): "A *painting* $\Gamma$ in a surface
$\Sigma$ is a pair $(U, N)$, where $U \subseteq \Sigma$ is closed and $N \subseteq U$ is finite,
such that
(i) $U - N$ has only finitely many arc-wise connected components (which we call *cells* of
$\Gamma$);
(ii) for each cell $c$, its closure $\bar{c}$ is a disc and $\tilde{c}$ is a subset of the boundary
of this disc, and $|\tilde{c}| \le 3$;
(iii) $bd(\Sigma) \subseteq U$;
(iv) for each cell $c$, if $c \cap bd(\Sigma) \ne \emptyset$ then $|\tilde{c}| = 2$ and $\bar{c}
\cap bd(\Sigma)$ is a $[0, 1]$-arc with ends the two members of $\tilde{c}$." -/
structure Painting (S : Type) [TopologicalSpace S] where
  /-- The set `U(Γ)`. -/
  U : Set S
  /-- The set `N(Γ)` of nodes. -/
  N : Set S
  isClosed_U : IsClosed U
  N_subset : N ⊆ U
  finite_N : N.Finite
  finite_cells : (arcComponentsIn (U \ N)).Finite
  cell_disc : ∀ c ∈ arcComponentsIn (U \ N),
    IsClosedDisc (closure c) ∧ tilde c ⊆ discBd (closure c) ∧ (tilde c).Finite ∧
      (tilde c).ncard ≤ 3
  bd_subset : bd S ⊆ U
  border_cell : ∀ c ∈ arcComponentsIn (U \ N), (c ∩ bd S).Nonempty →
    (tilde c).ncard = 2 ∧ (tilde c).Finite ∧ IsLine (closure c ∩ bd S) ∧
      lineEnds (closure c ∩ bd S) = tilde c

namespace Painting

variable {S : Type} [TopologicalSpace S]

/-- The set `C(Γ)` of cells. -/
def C (Γ : Painting S) : Set (Set S) := arcComponentsIn (Γ.U \ Γ.N)

end Painting

/-! ### Portrayals (Section 2, pages 165–166) -/

/-- A portrayal `π = (Σ, Γ, α, β, γ)` of a hypergraph `G` (Graph Minors XVII, Section 2, pages
165–166), with its axioms (P1)–(P7). Here `dom(γ)` is `domγ`, and `α`, `β`, `γ` are written
`cellGraph`,
`borderSet`, `nodeVertex`. -/
structure Portrayal {α : Type u} {β : Type v} (G : Hypergraph α β) where
  /-- The surface `Σ`. -/
  S : Type
  /-- The topology of `Σ`. -/
  [top : TopologicalSpace S]
  /-- (i) `Σ` is a surface. -/
  isSurface : IsSurface S
  /-- (i) `Σ` is connected. -/
  connected : ConnectedSpace S
  /-- (ii) The painting `Γ`. -/
  Γ : Painting S
  /-- (iii) The subhypergraph `α(c)` of a cell `c`. -/
  cellGraph : Set S → Hypergraph α β
  /-- (iv) The set `β(n)` of a border node `n`. -/
  borderSet : S → Set α
  /-- (v) The domain of `γ`. -/
  domγ : Set S
  /-- (v) The function `γ`. -/
  nodeVertex : S → α
  cellGraph_le : ∀ c ∈ Γ.C, cellGraph c ≤ G
  borderSet_subset : ∀ n ∈ Γ.N ∩ bd S, borderSet n ⊆ G.vertexSet
  domγ_subset : domγ ⊆ Γ.N
  nodeVertex_mem : ∀ n ∈ domγ, nodeVertex n ∈ G.vertexSet
  nodeVertex_injOn : InjOn nodeVertex domγ
  /-- (P1) `G = ∪ (α(c) : c ∈ C(Γ))`: every vertex of `G` lies in some `α(c)`. -/
  p1_vertex : ∀ v ∈ G.vertexSet, ∃ c ∈ Γ.C, v ∈ (cellGraph c).vertexSet
  /-- (P1) `G = ∪ (α(c) : c ∈ C(Γ))`: every edge of `G` lies in some `α(c)`. -/
  p1_edge : ∀ e ∈ G.edgeSet, ∃ c ∈ Γ.C, e ∈ (cellGraph c).edgeSet
  /-- (P1) `E(α(c) ∩ α(c')) = ∅` for distinct cells `c, c'`. -/
  p1_disjoint : ∀ c ∈ Γ.C, ∀ c' ∈ Γ.C, c ≠ c' →
    Disjoint (cellGraph c).edgeSet (cellGraph c').edgeSet
  /-- (P2) `γ(cTilde) ⊆ V(α(c))` for each cell `c`. -/
  p2 : ∀ c ∈ Γ.C, ∀ n ∈ tilde c ∩ domγ, nodeVertex n ∈ (cellGraph c).vertexSet
  /-- (P3) `γ(n) ∉ β(n)` for each `n ∈ dom(γ) ∩ bd(Σ)`. -/
  p3_notMem : ∀ n ∈ domγ ∩ bd S, nodeVertex n ∉ borderSet n
  /-- (P3) `β(n) ⊆ V(α(c))` for each border cell `c` and each `n ∈ cTilde`. -/
  p3_subset : ∀ c ∈ Γ.C, (c ∩ bd S).Nonempty → ∀ n ∈ tilde c,
    borderSet n ⊆ (cellGraph c).vertexSet
  /-- (P4) If `n₁, n₂` are nodes bordering different cuffs, then `β(n₁) ∩ β(n₂) = ∅`. -/
  p4_disjoint : ∀ Θ₁ ∈ cuffs S, ∀ Θ₂ ∈ cuffs S, Θ₁ ≠ Θ₂ → ∀ n₁ ∈ Γ.N ∩ Θ₁, ∀ n₂ ∈ Γ.N ∩ Θ₂,
    Disjoint (borderSet n₁) (borderSet n₂)
  /-- (P4) If `n₁` borders a cuff `Θ` and `n₂ ∈ dom(γ)` does not border `Θ`, then
  `γ(n₂) ∉ β(n₁)`. -/
  p4_notMem : ∀ Θ ∈ cuffs S, ∀ n₁ ∈ Γ.N ∩ Θ, ∀ n₂ ∈ domγ, n₂ ∉ Θ → nodeVertex n₂ ∉ borderSet n₁
  /-- (P5) If `c` is an internal cell then `V(α(c) ∩ α(-c)) ⊆ γ(cTilde)`. -/
  p5 : ∀ c ∈ Γ.C, ¬ (c ∩ bd S).Nonempty → ∀ v ∈ (cellGraph c).vertexSet,
    (∃ c' ∈ Γ.C, c' ≠ c ∧ v ∈ (cellGraph c').vertexSet) → v ∈ nodeVertex '' (tilde c ∩ domγ)
  /-- (P6) If `c` is a border cell with ends `n₁, n₂`, then
  `V(α(c) ∩ α(-c)) ⊆ β(n₁+) ∪ β(n₂+)`. -/
  p6 : ∀ c ∈ Γ.C, (c ∩ bd S).Nonempty → ∀ v ∈ (cellGraph c).vertexSet,
    (∃ c' ∈ Γ.C, c' ≠ c ∧ v ∈ (cellGraph c').vertexSet) →
    ∃ n ∈ tilde c, v ∈ borderSet n ∨ (n ∈ domγ ∧ v = nodeVertex n)
  /-- (P7) If `n₁, n₂, n₃, n₄` are nodes bordering the same cuff of `Σ` and in order, then
  `β(n₁+) ∩ β(n₃+) ⊆ β(n₂+) ∪ β(n₄+)`. -/
  p7 : ∀ Θ ∈ cuffs S, ∀ n₁ ∈ Γ.N ∩ Θ, ∀ n₂ ∈ Γ.N ∩ Θ, ∀ n₃ ∈ Γ.N ∩ Θ, ∀ n₄ ∈ Γ.N ∩ Θ,
    GM19.InOrderOn Θ n₁ n₂ n₃ n₄ → ∀ v : α,
    (v ∈ borderSet n₁ ∨ (n₁ ∈ domγ ∧ v = nodeVertex n₁)) →
    (v ∈ borderSet n₃ ∨ (n₃ ∈ domγ ∧ v = nodeVertex n₃)) →
    (v ∈ borderSet n₂ ∨ (n₂ ∈ domγ ∧ v = nodeVertex n₂)) ∨
      (v ∈ borderSet n₄ ∨ (n₄ ∈ domγ ∧ v = nodeVertex n₄))

attribute [instance] Portrayal.top

namespace Portrayal

variable {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G)

/-- `α(-c₀) = ∪ (α(c) : c ∈ C(Γ) - {c₀})` (Graph Minors XVII, Section 2, page 165): its vertices. -/
def otherVertices (c₀ : Set π.S) : Set α :=
  {v | ∃ c ∈ π.Γ.C, c ≠ c₀ ∧ v ∈ (π.cellGraph c).vertexSet}

/-- `β(n+)` (Graph Minors XVII, Section 2, page 165). -/
def borderPlus (n : π.S) : Set α :=
  {v | v ∈ π.borderSet n ∨ (n ∈ π.domγ ∧ v = π.nodeVertex n)}

/-- A linkage in `A⋆` from `X` to `Y` of `k` paths that pairs `x` with `y`: the path from `x` ends
at
`y` (Graph Minors XVII, Section 3, page 168). -/
def LinkagePairs {α : Type u} (K : SimpleGraph α) (X Y : Set α) (k : ℕ) (x y : α) : Prop :=
  ∀ P : Fin k → PathFromTo K X Y,
    (Pairwise fun i j ↦ Disjoint {z | z ∈ (P i).walk.support} {z | z ∈ (P j).walk.support}) →
    ∃ i, (P i).first = x ∧ (P i).last = y

/-- A cell `c` with ends `n₁, n₂` has warp `≤ p` (Graph Minors XVII, Section 3, page 168): "(i)
$|\beta(n_1)|, |\beta(n_2)| \le p$, and (ii) if $|\beta(n_1 +)| = |\beta(n_2 +)| = p + 1$, then
every linkage in $\alpha(c)^*$ from $\beta(n_1 +)$ to $\beta(n_2 +)$ pairs $\gamma(n_1)$ with
$\gamma(n_2)$." A linkage from `β(n₁+)` to `β(n₂+)` here has `p + 1` paths, one from each member. -/
def CellWarpLE (c : Set π.S) (p : ℕ) : Prop :=
  ∀ n₁ ∈ tilde c, ∀ n₂ ∈ tilde c, n₁ ≠ n₂ →
    (π.borderSet n₁).ncard ≤ p ∧ (π.borderSet n₂).ncard ≤ p ∧
    ((π.borderPlus n₁).ncard = p + 1 → (π.borderPlus n₂).ncard = p + 1 →
      LinkagePairs (π.cellGraph c).skeleton (π.borderPlus n₁) (π.borderPlus n₂) (p + 1)
        (π.nodeVertex n₁) (π.nodeVertex n₂))

/-- The warp of a cell: "the minimum $p \ge 0$ such that $c$ has warp $\le p$". -/
noncomputable def cellWarp (c : Set π.S) : ℕ := sInf {p | π.CellWarpLE c p}

/-- `π` has warp at `Θ` the maximum warp of the cells bordering `Θ` (Graph Minors XVII, Section 3,
page 168). -/
noncomputable def warpAt (Θ : Set π.S) : ℕ :=
  sSup {p | ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ p = π.cellWarp c}

/-- The warp of `π`: "the maximum of the warp of $\pi$ at $\Theta$, over all cuffs $\Theta$ (or 1 if
$bd(\Sigma) =
\emptyset$)" (Graph Minors XVII, Section 3, page 168). We take `max 1` even when `bd(Σ) ≠ ∅`
so that "every 0-redundant $\mathscr{T}$-central portrayal has warp $\ge 1$" (Section 5, page 171)
and capping
the last cuff of warp 0 in (5.1) does not raise the warp from `0` to `1`. -/
noncomputable def warp : ℕ :=
  open Classical in if (cuffs π.S).Nonempty then max 1 (sSup {p | ∃ Θ ∈ cuffs π.S, p
    = π.warpAt Θ}) else 1

/-- `π` is `𝒯`-central: "$\alpha(c)$ is small relative to $\mathscr{T}$ for every $c \in
C(\Gamma)$", where `A ⊆ G` is
*small* if `(A, B) ∈ 𝒯` for some `B ⊆ G` (Graph Minors XVII, Section 4, page 169). -/
def IsCentral (𝒯 : Set (Hypergraph α β × Hypergraph α β)) : Prop :=
  ∀ c ∈ π.Γ.C, ∃ B, (π.cellGraph c, B) ∈ 𝒯

/-- `π` is simpler than `π'` (Graph Minors XVII, Section 5, page 171): "(i) $\Sigma$ is simpler than
$\Sigma'$ and the warp of $\pi$ is at most that of $\pi'$, or (ii) there is a homeomorphism
$\psi \colon \Sigma \to \Sigma'$ such that for every cuff $\Theta$ of $\Sigma$, the warp of $\pi$ at
$\Theta$ is at most the warp of $\pi'$ at $\psi(\Theta)$, with strict inequality for some cuff
$\Theta$." -/
def IsSimpler {α' : Type*} {β' : Type*} {G' : Hypergraph α' β'} (π' : Portrayal G') : Prop :=
  (IsSimplerThan π.S π'.S ∧ π.warp ≤ π'.warp) ∨
    ∃ ψ : π.S ≃ₜ π'.S, (∀ Θ ∈ cuffs π.S, π.warpAt Θ ≤ π'.warpAt (ψ '' Θ)) ∧
      ∃ Θ ∈ cuffs π.S, π.warpAt Θ < π'.warpAt (ψ '' Θ)

/-- `π` resembles `π'` (Graph Minors XVII, Section 5, page 171). -/
def Resembles {α' : Type*} {β' : Type*} {G' : Hypergraph α' β'} (π' : Portrayal G') : Prop :=
  ∃ ψ : π.S ≃ₜ π'.S, ∀ Θ ∈ cuffs π.S, π.warpAt Θ = π'.warpAt (ψ '' Θ)

/-- `π` is 0-redundant relative to `𝒯` (Graph Minors XVII, Section 5, page 171): "there is no
$\mathscr{T}$-central portrayal of $G$ simpler than $\pi$." -/
def IsZeroRedundant (𝒯 : Set (Hypergraph α β × Hypergraph α β)) : Prop :=
  ∀ π' : Portrayal G, π'.IsCentral 𝒯 → ¬ π'.IsSimpler π

/-- `π` is `z`-redundant (Graph Minors XVII, Section 6, page 174): "$z < ord(\mathscr{T})$, and for
every $Z \subseteq V(G)$ with $|Z| \le z$ there is no $\mathscr{T}/Z$-central portrayal of $G/Z$
simpler than $\pi$." -/
def IsRedundant (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (θ z : ℕ) : Prop :=
  z < θ ∧ ∀ Z ⊆ G.vertexSet, Z.ncard ≤ z → ∀ π' : Portrayal (quotientVertices G Z),
    π'.IsCentral (quotientTangle G 𝒯 Z) → ¬ π'.IsSimpler π

/-- The truth `(τ₁, …, τ₆)` of a portrayal (Graph Minors XVII, Section 8, page 181): `τᵢ` is the
number of internal cells `c` with `|cTilde| = 4 - i` for `i ≤ 4`, `τ₅ = |N(Γ) - bd(Σ)|` and
`τ₆ = |N(Γ) ∩ bd(Σ)|`. -/
noncomputable def truth : Fin 6 → ℕ := fun i ↦
  if i.1 < 4 then {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - i.1}.ncard
  else if i.1 = 4 then (π.Γ.N \ bd π.S).ncard else (π.Γ.N ∩ bd π.S).ncard

/-- `π` is truer than `π'`: its truth is lexicographically smaller (Graph Minors XVII, Section 8,
page 181). -/
def IsTruer {G' : Hypergraph α β} (π' : Portrayal G') : Prop :=
  ∃ k : Fin 6, (∀ i < k, π.truth i = π'.truth i) ∧ π.truth k < π'.truth k

/-- `π` is true relative to `𝒯` (Graph Minors XVII, Section 8, page 181): "A $0$-redundant
$\mathcal{T}$-central portrayal $\pi$ is *true* (relative to $\mathcal{T}$) if there is no truer
$\mathcal{T}$-central portrayal resembling $\pi$." -/
def IsTrue (𝒯 : Set (Hypergraph α β × Hypergraph α β)) : Prop :=
  π.IsCentral 𝒯 ∧ π.IsZeroRedundant 𝒯 ∧
    ∀ π' : Portrayal G, π'.IsCentral 𝒯 → π'.IsTruer π → ¬ π'.Resembles π

end Portrayal

/-! ### Controlling a minor (Sections 13 and 14) -/

/-- `𝒯` controls an `H`-minor of `G*` (Graph Minors XVII, Section 14, page 207; Graph Minors XX,
Section 10, page 354), where `G*` is the 1-skeleton `G.skeleton`. Here `H` is a graph given by its
vertex set `V(H)`, edge set and ends, as in Graph Minors XX: an `H`-minor is a function `α` with
- for each `v ∈ V(H)`, `α(v)` is a non-null connected subgraph of `sk(G)`, and `α(u)` and `α(v)` are
  disjoint for distinct `u, v`,
- `α(e) ∈ E(sk(G))` for each `e ∈ E(H)`, and `α(e) ≠ α(f)` for distinct `e, f`,
- for each `e ∈ E(H)` with distinct ends `u, v`, `α(e)` has one end in `V(α(u))` and the other in
  `V(α(v))`,
- for each loop `e ∈ E(H)` with end `v`, `V(α(v))` contains both ends of `α(e)` and
  `α(e) ∉ E(α(v))`,
- there do not exist `(A, B) ∈ 𝒯` of order `< |V(H)|` and `v ∈ V(H)` such that `V(α(v)) ⊆ V(A)`.
A connected subgraph `α(v)` is given by its vertex set `av v` and edge set `ae' v`. -/
def ControlsMinor {α : Type u} {β : Type v} {α' : Type*} {β' : Type*} (G : Hypergraph α β)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (H : Hypergraph α' β') : Prop :=
  H.IsGraph ∧ ∃ (av : α' → Set α) (ae' : α' → Set (Sym2 α)) (ae : β' → Sym2 α),
    (∀ v ∈ H.vertexSet, (av v).Nonempty ∧ av v ⊆ G.vertexSet ∧ ae' v ⊆ G.skeleton.edgeSet ∧
      (∀ x y, s(x, y) ∈ ae' v → x ∈ av v ∧ y ∈ av v) ∧
      ∀ x ∈ av v, ∀ y ∈ av v, Relation.ReflTransGen (fun a b ↦ s(a, b) ∈ ae' v) x y) ∧
    (∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v → Disjoint (av u) (av v)) ∧
    (∀ e ∈ H.edgeSet, ae e ∈ G.skeleton.edgeSet) ∧ InjOn ae H.edgeSet ∧
    (∀ e ∈ H.edgeSet, ∀ u v, u ≠ v → H.Inc e u → H.Inc e v →
      ∃ x ∈ av u, ∃ y ∈ av v, ae e = s(x, y)) ∧
    (∀ e ∈ H.edgeSet, ∀ v, H.ends e = {v} →
      ∃ x ∈ av v, ∃ y ∈ av v, ae e = s(x, y) ∧ ae e ∉ ae' v) ∧
    ∀ ⦃A B⦄, (A, B) ∈ 𝒯 → Hypergraph.separationOrder A B < H.vertexSet.ncard →
      ∀ v ∈ H.vertexSet, ¬ av v ⊆ A.vertexSet

/-- The surface `S` has a drawing of the hypergraph `H`, which is a graph: `H` can be drawn in `S`
(Graph Minors XVII, (14.2)). A drawing is a `Surface.Drawing` of a graph on `S` with vertices the
vertices of `H`, in which every edge of `H` is a line or loop. The drawing is given by an injective
map of `V(H)` into `S`, and for each edge `e` a set `edgeOf e`, with these pairwise disjoint and
meeting the vertices only at their ends. -/
def CanBeDrawn {α' : Type*} {β' : Type*} (S : Type) [TopologicalSpace S]
    (H : Hypergraph α' β') : Prop :=
  ∃ (ν : α' → S) (edgeOf : β' → Set S), InjOn ν H.vertexSet ∧
    (∀ e ∈ H.edgeSet, ∀ u v, H.Inc e u → H.Inc e v → u ≠ v →
      IsLineWithEnds (edgeOf e) (ν u) (ν v)) ∧
    (∀ e ∈ H.edgeSet, ∀ v, H.ends e = {v} → IsOArc (edgeOf e) ∧ ν v ∈ edgeOf e) ∧
    (∀ e ∈ H.edgeSet, ∀ f ∈ H.edgeSet, e ≠ f → edgeOf e ∩ edgeOf f ⊆ ν '' H.vertexSet) ∧
    (∀ e ∈ H.edgeSet, ∀ v ∈ H.vertexSet, ν v ∈ edgeOf e → H.Inc e v)

end GraphMinor.GM17
