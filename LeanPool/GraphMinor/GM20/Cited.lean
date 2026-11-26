/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Defs2
public import LeanPool.GraphMinor.GM18.Cited
public import LeanPool.GraphMinor.GM20.Defs

/-!
# Results cited in Graph Minors XX

This file states as `Prop`s the results of other papers of the series that the proof of Graph Minors
XX cites. Each is the statement of the cited paper, over the actual objects, and each is proved in
another file.

From Graph Minors XVIII:
* `GM18Theorem67Statement`, (6.7) (page 106), which is (3.1) of XX. It is proved as `gm18Theorem67`
  in
  `Section3.lean`.

From Graph Minors XIX:
* `GM19Theorem21Statement`, (2.1) (page 328), used for (8.1) of XX.

From Graph Minors XVII, used for (10.3) of XX. All but the last hold under the standing hypotheses
of the section of that paper (`GM17.Standing`):
* `GM17Theorem82Statement`, (8.2) (page 181);
* `GM17Theorem83Statement`, (8.3) (page 182);
* `GM17Theorem84Statement`, (8.4) (page 182);
* `GM17Theorem85Statement`, (8.5) (page 182);
* `GM17Theorem87Statement`, (8.7) (page 182);
* `GM17Theorem88Statement`, (8.8) (page 183);
* `GM17Theorem91Statement`, (9.1) (page 183);
* `GM17Theorem98Statement`, (9.8) (pages 187–188);
* `GM17Theorem117Statement`, (11.7) (page 195);
* `GM17Theorem142Statement`, (14.2) (page 209).
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface GraphMinor.GM18 GraphMinor.GM10 Hypergraph

universe u v w

/-! ### Graph Minors XVIII -/

/-- Graph Minors XVIII, (6.7) (page 106):
"**6.7.** *Let $\Omega$ be a well-quasi-order, let $\mathscr{C}$ be a well-behaved class of rootless
partial $\Omega$-patchworks, and let $\theta \ge 1$ be an integer. Let $\mathscr{D}$ be a class of
rootless, robust $\Omega$-patchworks and suppose that for each $P \in \mathscr{D}$ there is a
tie-breaker $\lambda$ in $\|P\|^-$ such that for every tangle $\mathscr{T}$ in $G^-$ of order $\ge
\theta$, there is an $\Omega$-place $(P, \mathscr{L})$ with heart in $\mathscr{C}$ such that
$\mathscr{L}^-$ $\theta$-isolates $\mathscr{T}$. Then $\mathscr{D}$ is well-quasi-ordered by
simulation.*"

Lean uses an infinite ambient edge type to provide fresh edge labels. -/
def GM18Theorem67Statement : Prop :=
  ∀ {Ω : Type (max u v)} [Preorder Ω] {α : Type u} {β : Type v} [Infinite β] (𝒞 : Set
    (PartialPatchwork Ω α β))
    (θ : ℕ) (𝒟 : Set (GM04.Patchwork Ω α β)),
    WellQuasiOrderedLE Ω → GM18.WellBehaved 𝒞 → (∀ P ∈ 𝒞, IsRootless P) → 1 ≤ θ →
    (∀ P ∈ 𝒟, IsRootless P ∧ P.IsRobust) →
    (∀ P ∈ 𝒟, ∃ (Λ : Type) (_ : LinearOrder Λ) (lam : Hypergraph α β × Hypergraph α β → Λ),
      IsTieBreaker P.G.toHypergraph lam ∧
      ∀ (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)), IsTangle P.G.toHypergraph θ' 𝒯 →
        θ ≤ θ' → ∃ ℒ : Set (RootedHypergraph α β),
          IsOmegaPlace (PartialPatchwork.ofPatchwork P) ℒ ∧
          (∃ Q ∈ 𝒞, HasPlaceHeart (PartialPatchwork.ofPatchwork P) ℒ Q) ∧
          GM18.Isolates P.G.toHypergraph lam θ 𝒯 (rootedLocationToLocation P.G ℒ)) →
    ∀ Q : ℕ → GM04.Patchwork Ω α β, (∀ i, Q i ∈ 𝒟) → ∃ i j, i < j ∧ GM04.Simulated (Q i) (Q j)

/-! ### Graph Minors XIX -/

/-- Graph Minors XIX, (2.1) (page 328):
"**2.1.** *Let $\Sigma$ be a surface, and let $\Omega$ be a well-quasi-order. Let $\Gamma_i$ ($i =
1, 2, \dots$) be a countable sequence of internally 3-connected paintings in $\Sigma$, and for each
$i \ge 1$ let $\phi_i \colon E(\Gamma_i) \to E(\Omega)$ be some function. Then there exist $j > i
\ge 1$ and a linear inflation $\sigma$ of $\Gamma_i$ in $\Gamma_j$ satisfying $\phi_i \le \phi_j
\circ \sigma$.*"
Surfaces of Graph Minors XIX are compact and connected. -/
def GM19Theorem21Statement : Prop :=
  ∀ (S : Type) [TopologicalSpace S] {Ω : Type w} [Preorder Ω], IsSurface S → ConnectedSpace S →
    WellQuasiOrderedLE Ω → ∀ (Γ : ℕ → GM19.Painting S) (φ : ℕ → Set S → Ω),
    (∀ i, (Γ i).IsInternallyThreeConnected) →
    ∃ i j, i < j ∧ ∃ (σv : S → Set S) (σe : Set S → Set S),
      GM19.IsLinearInflation (Γ i) (Γ j) σv σe ∧ ∀ e ∈ (Γ i).E, φ i e ≤ φ j (σe e)

/-! ### Graph Minors XVII -/

namespace GM17

open GraphMinor.GM17

variable {α : Type u} {β : Type v}

/-- The standing hypothesis of Graph Minors XVII, Sections 8 (page 181) and 9 (page 183), with
`r = 2p + 3`, and of Section 11 (page 189) with `r = 2p + 4` and `t = 6p + 8`. The portrayal `π` is
true, `r`-redundant, and `𝒯`-central,
with warp `≤ p` and `ord(𝒯) > t`. -/
structure Standing {G : Hypergraph α β} (𝒯 : Set (Hypergraph α β × Hypergraph α β))
    (θ p r t : ℕ) (π : Portrayal G) : Prop where
  isTangle : IsTangle G θ 𝒯
  isTrue : π.IsTrue 𝒯
  isRedundant : π.IsRedundant 𝒯 θ r
  warp_le : π.warp ≤ p
  lt : t < θ

/-- `α(Δ)`, the union of the `α(c)` over cells `c ⊆ Δ` (Graph Minors XVII, Section 5). It is small
when `(A, B) ∈ 𝒯` for some `B` and `A` has the same vertices and edges as the union; its vertex and
edge sets are `areaVertices`, `areaEdges`. -/
def areaVertices {G : Hypergraph α β} (π : Portrayal G) (Δ : Set π.S) : Set α :=
  ⋃ c ∈ {c ∈ π.Γ.C | c ⊆ Δ}, (π.cellGraph c).vertexSet

/-- The edges of `α(Δ)`. -/
def areaEdges {G : Hypergraph α β} (π : Portrayal G) (Δ : Set π.S) : Set β :=
  ⋃ c ∈ {c ∈ π.Γ.C | c ⊆ Δ}, (π.cellGraph c).edgeSet

end GM17

open GraphMinor.GM17

/-- Graph Minors XVII, (8.3) (page 182): "For every $\Gamma$-normal $I$-arc $F$ with $|F \cap
N(\Gamma)| = 2$, there is a disc $\Delta
\subseteq \Sigma$ with $F \subseteq bd(\Delta) \subseteq F \cup bd(\Sigma)$ such that
$\Delta \cap N(\Gamma) \subseteq F$ and $\Delta$ includes exactly one cell of $\Gamma$." Standing
hypothesis: `π` is true, `(2p + 3)`-redundant, `𝒯`-central, of warp `≤ p`,
with `ord(𝒯) > 4p + 5`. -/
def GM17Theorem83Statement : Prop :=
  ∀ {α : Type u} {β : Type v} {G : Hypergraph α β} (𝒯 : Set (Hypergraph α β × Hypergraph α β))
    (θ p : ℕ) (π : Portrayal G), GM17.Standing 𝒯 θ p (2 * p + 3) (4 * p + 5) π →
    ∀ F : Set π.S, IsLine F → F ∩ π.Γ.U ⊆ π.Γ.N → F ∩ bd π.S = lineEnds F →
      (F ∩ π.Γ.N).ncard = 2 →
      ∃ Δ : Set π.S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd π.S ∧ Δ ∩ π.Γ.N ⊆ F ∧
        {c ∈ π.Γ.C | c ⊆ Δ}.ncard = 1

/-- Graph Minors XVII, (8.5) (page 182):
"(8.5) *For every $\Gamma$-normal $O$-arc $F \subseteq \Sigma$ with $|F \cap N(\Gamma)| \le 3$,
there is a disc $\Delta \subseteq \Sigma$ with $F = bd(\Delta)$ such that $\alpha(\Delta)$ is small,
and either*
(i) *$\Delta \cap N(\Gamma) \subseteq F$ and $\Delta$ includes at most one cell of $\Gamma$, or*
(ii) *$|F \cap N(\Gamma)| = 3$, and $|\tilde{c}| = 2$ for every cell $c \subseteq \Delta$.*" -/
def GM17Theorem85Statement : Prop :=
  ∀ {α : Type u} {β : Type v} {G : Hypergraph α β} (𝒯 : Set (Hypergraph α β × Hypergraph α β))
    (θ p : ℕ) (π : Portrayal G), GM17.Standing 𝒯 θ p (2 * p + 3) (4 * p + 5) π →
    ∀ F : Set π.S, IsOArc F → F ∩ π.Γ.U ⊆ π.Γ.N → (F ∩ π.Γ.N).ncard ≤ 3 →
      ∃ Δ : Set π.S, IsClosedDisc Δ ∧ discBd Δ = F ∧
        (∃ A B, (A, B) ∈ 𝒯 ∧ A.vertexSet = GM17.areaVertices π Δ ∧
          A.edgeSet = GM17.areaEdges π Δ) ∧
        ((Δ ∩ π.Γ.N ⊆ F ∧ {c ∈ π.Γ.C | c ⊆ Δ}.ncard ≤ 1) ∨
          ((F ∩ π.Γ.N).ncard = 3 ∧ ∀ c ∈ π.Γ.C, c ⊆ Δ → (tilde c).ncard = 2))

/-- Graph Minors XVII, (8.2) (page 181):
"(8.2) *The boundary of every region is an $O$-arc, and in particular, $|\tilde{c}| \ge 2$ for every
cell $c$.*"
A region is an arcwise connected component of `Σ \ U(Γ)`. Standing hypothesis as in
`GM17Theorem83Statement`. -/
def GM17Theorem82Statement : Prop :=
  ∀ {α : Type u} {β : Type v} {G : Hypergraph α β} (𝒯 : Set (Hypergraph α β × Hypergraph α β))
    (θ p : ℕ) (π : Portrayal G), GM17.Standing 𝒯 θ p (2 * p + 3) (4 * p + 5) π →
    (∀ R ∈ arcComponentsIn (π.Γ.U)ᶜ, IsOArc (closure R \ R)) ∧
      ∀ c ∈ π.Γ.C, 2 ≤ (tilde c).ncard

/-- Graph Minors XVII, (8.4) (page 182): "`dom(γ) = N(Γ)`." Standing hypothesis as in
`GM17Theorem83Statement`. -/
def GM17Theorem84Statement : Prop :=
  ∀ {α : Type u} {β : Type v} {G : Hypergraph α β} (𝒯 : Set (Hypergraph α β × Hypergraph α β))
    (θ p : ℕ) (π : Portrayal G), GM17.Standing 𝒯 θ p (2 * p + 3) (4 * p + 5) π →
    π.domγ = π.Γ.N

/-- `C*(Γ)`, "the set of all $c \in C(\Gamma)$ such that there is no $c' \in C(\Gamma)$ with $c' \ne
c$ and $\tilde{c} \subseteq \tilde{c}'$" (Graph Minors XVII, Section 8, page 182). -/
def GM17.starCells {S : Type} [TopologicalSpace S] (Γ : GM17.Painting S) : Set (Set S) :=
  Γ.CStar

/-- Graph Minors XVII, (8.7) (page 182):
"(8.7) *For every node $n$ there are at least two cells $c \in C^*(\Gamma)$ with $n \in \tilde{c}$,
and if there are only two and $|\tilde{c}| = 2$ for one of them, then $c$ is a border cell.*"
Standing hypothesis as in `GM17Theorem83Statement`. -/
def GM17Theorem87Statement : Prop :=
  ∀ {α : Type u} {β : Type v} {G : Hypergraph α β} (𝒯 : Set (Hypergraph α β × Hypergraph α β))
    (θ p : ℕ) (π : Portrayal G), GM17.Standing 𝒯 θ p (2 * p + 3) (4 * p + 5) π →
    ∀ n ∈ π.Γ.N, 2 ≤ {c ∈ GM17.starCells π.Γ | n ∈ tilde c}.ncard ∧
      ({c ∈ GM17.starCells π.Γ | n ∈ tilde c}.ncard = 2 →
        ∀ c ∈ GM17.starCells π.Γ, n ∈ tilde c → (tilde c).ncard = 2 → (c ∩ bd π.S).Nonempty)

/-- Graph Minors XVII, (8.8) (page 183):
"(8.8) *If $c_1, c_2$ are distinct cells with $\tilde{c}_1 \subseteq \tilde{c}_2$, then $c_1$ is a
border cell, and $|\tilde{c}_2| = 3$.*"
Standing hypothesis as in `GM17Theorem83Statement`. -/
def GM17Theorem88Statement : Prop :=
  ∀ {α : Type u} {β : Type v} {G : Hypergraph α β} (𝒯 : Set (Hypergraph α β × Hypergraph α β))
    (θ p : ℕ) (π : Portrayal G), GM17.Standing 𝒯 θ p (2 * p + 3) (4 * p + 5) π →
    ∀ c₁ ∈ π.Γ.C, ∀ c₂ ∈ π.Γ.C, c₁ ≠ c₂ → tilde c₁ ⊆ tilde c₂ →
      (c₁ ∩ bd π.S).Nonempty ∧ (tilde c₂).ncard = 3

/-- Graph Minors XVII, (9.1) (page 183):
"(9.1) *Let $c_0$ be an internal cell, and let $v_1, v_2 \in \gamma(\tilde{c}_0)$. Then there is a
path in $\alpha(c_0)^*$ from $v_1$ to $v_2$ with no other vertex in $\gamma(\tilde{c}_0)$.*" -/
def GM17Theorem91Statement : Prop :=
  ∀ {α : Type u} {β : Type v} {G : Hypergraph α β} (𝒯 : Set (Hypergraph α β × Hypergraph α β))
    (θ p : ℕ) (π : Portrayal G), GM17.Standing 𝒯 θ p (2 * p + 3) (4 * p + 5) π →
    ∀ c₀ ∈ π.Γ.C, ¬ (c₀ ∩ bd π.S).Nonempty → ∀ n₁ ∈ tilde c₀, ∀ n₂ ∈ tilde c₀, n₁ ≠ n₂ →
      ∃ L : PathFromTo (π.cellGraph c₀).skeleton {π.nodeVertex n₁} {π.nodeVertex n₂},
        ∀ z ∈ L.walk.support, z ∈ π.nodeVertex '' tilde c₀ →
          z = π.nodeVertex n₁ ∨ z = π.nodeVertex n₂

/-- Graph Minors XVII, (9.8) (pages 187–188):
"(9.8) *Let $c_0$ be a border cell with $c_0 = \{n_1, n_2\}$. Then*
(i) *$|\beta(n_1)| = |\beta(n_2)| = q$ and $\beta(n_1) \cap \gamma(N(\Gamma)), \beta(n_2) \cap
\gamma(N(\Gamma)) = \emptyset$;* ...
(ii) *there is a linkage $\{P_1, \dots, P_q\}$ in $\alpha(c_0) \setminus \{\gamma(n_1),
\gamma(n_2)\}$ from $\beta(n_1)$ to $\beta(n_2)$ such that either there is a path $P_0$ such that
$\{P_0, P_1, \dots, P_q\}$ is a linkage in $\alpha(c_0)$ from $\beta(n_1 +)$ to $\beta(n_2 +)$, or
there is an internal cell $c$ with $|\tilde{c}| = 3$ and $\tilde{c}_0 \subseteq \tilde{c}$.*"
(Here $c_0 = \{n_1, n_2\}$ is a misprint in the paper for $\tilde{c}_0 = \{n_1, n_2\}$, and `q` is
the warp of `π` at the cuff `Θ`, as in (9.3).) -/
def GM17Theorem98Statement : Prop :=
  ∀ {α : Type u} {β : Type v} {G : Hypergraph α β} (𝒯 : Set (Hypergraph α β × Hypergraph α β))
    (θ p : ℕ) (π : Portrayal G), GM17.Standing 𝒯 θ p (2 * p + 3) (4 * p + 5) π →
    ∀ Θ ∈ cuffs π.S, ∀ c₀ ∈ π.Γ.C, (c₀ ∩ Θ).Nonempty → ∀ n₁ ∈ tilde c₀, ∀ n₂ ∈ tilde c₀, n₁ ≠ n₂ →
      (π.borderSet n₁).ncard = π.warpAt Θ ∧ (π.borderSet n₂).ncard = π.warpAt Θ ∧
      Disjoint (π.borderSet n₁) (π.nodeVertex '' π.Γ.N) ∧
      Disjoint (π.borderSet n₂) (π.nodeVertex '' π.Γ.N) ∧
      ∃ L : Fin (π.warpAt Θ) →
          PathFromTo (π.cellGraph c₀).skeleton (π.borderSet n₁) (π.borderSet n₂),
        (Pairwise fun i j ↦ Disjoint {z | z ∈ (L i).walk.support} {z | z ∈ (L j).walk.support}) ∧
        (∀ i, π.nodeVertex n₁ ∉ (L i).walk.support ∧ π.nodeVertex n₂ ∉ (L i).walk.support) ∧
        ((∃ L₀ : PathFromTo (π.cellGraph c₀).skeleton {π.nodeVertex n₁} {π.nodeVertex n₂},
            ∀ i, Disjoint {z | z ∈ L₀.walk.support} {z | z ∈ (L i).walk.support}) ∨
          ∃ c ∈ π.Γ.C, ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 ∧ tilde c₀ ⊆ tilde c)

/-- Graph Minors XVII, (11.7) (page 195), with the hypotheses of that part of Section 11:
"$\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ is a true, $(2p + 4)$-redundant,
$\mathcal{T}$-central portrayal of a hypergraph $G$, with warp $\le p$, and
$\operatorname{ord}(\mathcal{T}) > 6p + 8$" and "$c_0 \in C(\Gamma)$ and $(A, B) \in \mathscr{T}$
with $\alpha(c_0) \subseteq A$, satisfying
$$|V(A \cap B)| \le |V(\alpha(c_0) \cap \alpha(-c_0))|". Conclusion: "$(11.7) $|V(A \cap B)| =
|V(\alpha(c_0) \cap \alpha(-c_0))|.$" -/
def GM17Theorem117Statement : Prop :=
  ∀ {α : Type u} {β : Type v} {G : Hypergraph α β} (𝒯 : Set (Hypergraph α β × Hypergraph α β))
    (θ p : ℕ) (π : Portrayal G), GM17.Standing 𝒯 θ p (2 * p + 4) (6 * p + 8) π →
    ∀ c₀ ∈ π.Γ.C, ∀ ⦃A B⦄, (A, B) ∈ 𝒯 → π.cellGraph c₀ ≤ A →
      separationOrder A B ≤ ((π.cellGraph c₀).vertexSet ∩ π.otherVertices c₀).ncard →
      separationOrder A B = ((π.cellGraph c₀).vertexSet ∩ π.otherVertices c₀).ncard

/-- Graph Minors XVII, (14.2) (page 209): "For any graph $H$ there are numbers $p, q, z$ and $\theta
> z$, such that for every
hypergraph $G$ and every tangle $\mathscr{T}$ in $G$ of order $\ge \theta$, either* (i)
$\mathscr{T}$ *controls an $H$-minor of $G^*$, or* (ii) *there exists $Z \subseteq V(G)$
with $|Z| \le z$ and a $\mathscr{T}/Z$-central portrayal $\pi = (\Sigma, \Gamma, \alpha,
\beta, \gamma)$ of $G/Z$ with warp $\le p$, such that $\Sigma$ has $\le q$ cuffs and $H$
cannot be drawn in $\Sigma$, and $\pi$ is true and $(2p + 7)$-redundant." -/
def GM17Theorem142Statement : Prop :=
  ∀ {α' : Type} {β' : Type} (H : Hypergraph α' β'), H.IsGraph →
    ∃ p q z θ : ℕ, z < θ ∧ ∀ {α : Type u} {β : Type v} (G : Hypergraph α β) (θ' : ℕ)
      (𝒯 : Set (Hypergraph α β × Hypergraph α β)), IsTangle G θ' 𝒯 → θ ≤ θ' →
      ControlsMinor G 𝒯 H ∨ ∃ Z ⊆ G.vertexSet, Z.ncard ≤ z ∧
        ∃ π : Portrayal (quotientVertices G Z), π.warp ≤ p ∧ (cuffs π.S).encard ≤ q ∧
          ¬ CanBeDrawn π.S H ∧ π.IsTrue (quotientTangle G 𝒯 Z) ∧
          π.IsRedundant (quotientTangle G 𝒯 Z) (θ' - Z.ncard) (2 * p + 7)

end GraphMinor.GM20
