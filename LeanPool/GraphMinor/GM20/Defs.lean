/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM18.Defs
public import LeanPool.GraphMinor.GM19.Defs
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Definitions for Graph Minors XX: Wagner's conjecture

This file formalizes the definitions of N. Robertson and P. D. Seymour, *Graph Minors. XX. Wagner's
conjecture*, J. Combin. Theory Ser. B 92 (2004) 325–357, that are not already in the interface
files. Hypergraphs, separations, tangles, tie-breakers, distinctions, patches and patchworks are
those of `GraphMinor.Hypergraph.Basic`, `GraphMinor.GM10.Defs`, `GraphMinor.GM10.Defs2`,
`GraphMinor.GM04.Patchwork.Defs` and `GraphMinor.GM18.Defs`. In particular:

- a patchwork `(G, μ, Δ)` is a `GM18.UnlabeledPatchwork`, a partial `Ω`-patchwork is a
  `GM18.PartialPatchwork`, and an `Ω`-patchwork is a `GM04.Patchwork`;
- a rooted location is a set `ℒ` with `GM18.IsRootedLocation G ℒ`. The paper's condition
  "there exists $B \subseteq G$ such that $(A, B)$ is a separation of $G$" for `A` to be
  complemented, and its condition on
  `A₁, A₂`, are the conditions of Graph Minors XVIII, Section 5, in another wording;
- `ℒ⁻` is `GM18.rootedLocationToLocation G ℒ` and `M(G, ℒ)` is `GM18.rootedLocationCore G ℒ`;
- `G/W` is `GM10.quotientVertices G W` and `𝒯/W` is `GM10.quotientTangle G 𝒯 W`;
- "`ℒ` `θ`-isolates `𝒯`" is `GM18.Isolates G⁻ λ θ 𝒯 ℒ⁻`;
- "`(P, ℒ)` has heart `P'`" is `GM18.HasPatchworkHeart P ℒ P'`.

The functions `μ`, `Δ`, `φ` of a `GM04.Patchwork` are total, and only their values on `dom(μ)` and
on `E(G)` have a meaning. Every statement about sets of patchworks below sees only those values:
`IsCompletionOf` and the relations on patchworks compare them there.

New definitions, in the paper's order:
- Section 4: `IsCompletionOf`, `WellBehaved`, `IsEncoding`, `IsActive`, `IsOneVertexExtension`,
  `RootedHypergraph.slash`, `Patchwork.slash`, `IsCondensation`.
- Section 5: `zSet` (`Z(G)`), `InM` (`ℳ(𝒯, W, θ)`), `IsolatesModulo`, `IsFine`, `IsSuitable`.
- Section 6: `edgeBasedLam`, `IsEdgeBased`, `IsLinkedTo`, `locationSlash`.
- Section 7: `IsFree`.
- Section 8: `Painting`, `Painting.IsThreeConnected`, `Painting.sk`, `IsLinearInflation`.
- Section 9: `GradedSurface`, `Hull`, `IsHulled`.
- Section 10: `IsShelled`.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface GraphMinor.GM18 GraphMinor.GM10 Hypergraph

universe u v w

variable {α : Type u} {β : Type v}

/-! ## Section 4: well-behaved sets of patchworks -/

/-- `Q` is an `Ω`-completion of the patchwork `P` (Graph Minors XX, Section 4, page 330): "If $P =
(G, \mu, \Delta)$ is a patchwork and $\Omega$ is a quasi-order, we call every
$\Omega$-patchwork $(G, \mu, \Delta, \phi)$ an $\Omega$*-completion* of $P$." -/
structure IsCompletionOf {Ω Ω' : Type*} (P : GM04.Patchwork Ω' α β) (Q : GM04.Patchwork Ω α β) :
    Prop where
  G_eq : Q.G = P.G
  dom_eq : Q.dom = P.dom
  μ_eq : ∀ ⦃e⦄, e ∈ P.dom → Q.μ e = P.μ e
  Δ_eq : ∀ ⦃e⦄, e ∈ P.G.edgeSet → Q.Δ e = P.Δ e

/-- A set `𝓕` of patchworks is well-behaved (Graph Minors XX, Section 4, page 330): "for every
well-quasi-order $\Omega$ and every countable sequence $P_i$ ($i = 1, 2, \dots$)
of $\Omega$-completions of members of $\mathcal{F}$ there exist $j > i \ge 1$ such that
$P_i$ is simulated in $P_j$." Here `Ω` ranges over
`Type (max u v)`, which is closed under the constructions of the paper.

This uses the IV simulation relation. On each marked edge it sends source groupings into the
target patch. XX §3 requires equality with the target patch. -/
def WellBehaved (𝓕 : Set (UnlabeledPatchwork α β)) : Prop :=
  ∀ (Ω : Type (max u v)) [Preorder Ω], WellQuasiOrderedLE Ω →
    ∀ Q : ℕ → GM04.Patchwork Ω α β, (∀ i, ∃ P ∈ 𝓕, IsCompletionOf P (Q i)) →
      ∃ i j, i < j ∧ GM04.Simulated (Q i) (Q j)

/-- `γ` is an encoding of `𝓕₂` in `𝓕₁` (Graph Minors XX, Section 4, page 331): "A function $\gamma :
\mathcal{F}_2 \to \mathcal{F}_1$ is an *encoding* of $\mathcal{F}_2$ in
$\mathcal{F}_1$ if $P$ is simulated in $P'$ for all $P, P' \in \mathcal{F}_2$ such that
$\gamma(P)$ is simulated in $\gamma(P')$."

Both simulations here use the IV relation, which permits inclusion of transported patches.
XX §3 uses equality for those patches. -/
def IsEncoding {Ω₁ Ω₂ : Type*} [Preorder Ω₁] [Preorder Ω₂] (𝓕₁ : Set (GM04.Patchwork Ω₁ α β))
    (𝓕₂ : Set (GM04.Patchwork Ω₂ α β)) (γ : GM04.Patchwork Ω₂ α β → GM04.Patchwork Ω₁ α β) : Prop :=
  (∀ P ∈ 𝓕₂, γ P ∈ 𝓕₁) ∧
    ∀ P ∈ 𝓕₂, ∀ P' ∈ 𝓕₂, GM04.Simulated (γ P) (γ P') → GM04.Simulated P P'

/-- A patchwork is active if every vertex of `G` is incident with some `e ∈ dom(μ)` (Graph Minors
XX, Section 4, page 332). -/
def IsActive {Ω : Type*} (P : GM04.Patchwork Ω α β) : Prop :=
  ∀ v ∈ P.G.vertexSet, ∃ e ∈ P.dom, P.G.Inc e v

/-- The relation "`P₂` is a 1-vertex extension of `P₁`" (Graph Minors XX, Section 4, page 332): `P₂`
is `P₁` with a new vertex `v`, incident with `f` only, where `μ₂(f)` and `Δ₂(f)` are arbitrary on
the
new set of ends of `f`. -/
structure IsOneVertexExtension (P₁ P₂ : UnlabeledPatchwork α β) (f : β) (v : α) : Prop where
  f_mem : f ∈ P₁.dom
  v_notMem : v ∉ P₁.G.vertexSet
  roots_eq : P₂.G.roots = P₁.G.roots
  edgeSet_eq : P₂.G.edgeSet = P₁.G.edgeSet
  vertexSet_eq : P₂.G.vertexSet = P₁.G.vertexSet ∪ {v}
  ends_f : P₂.G.ends f = P₁.G.ends f ∪ {v}
  ends_ne : ∀ e ∈ P₁.G.edgeSet, e ≠ f → P₂.G.ends e = P₁.G.ends e
  dom_eq : P₂.dom = P₁.dom
  μ_ne : ∀ e ∈ P₁.dom, e ≠ f → P₂.μ e = P₁.μ e
  Δ_ne : ∀ e ∈ P₁.G.edgeSet, e ≠ f → P₂.Δ e = P₁.Δ e

/-- `π/W`: the march obtained by omitting all terms in `W` (Graph Minors XX, Section 4, page 333).
-/
noncomputable def marchSlash (π : List α) (W : Set α) : List α :=
  open Classical in π.filter (· ∉ W)

theorem mem_marchSlash {π : List α} {W : Set α} {v : α} :
    v ∈ marchSlash π W ↔ v ∈ π ∧ v ∉ W := by
  classical
  simp [marchSlash]

theorem nodup_marchSlash {π : List α} (h : π.Nodup) (W : Set α) : (marchSlash π W).Nodup := by
  classical
  exact h.filter _

/-- `G/W` for a rooted hypergraph (Graph Minors XX, Section 4, page 333): "`G/W` denotes
`(G⁻/W, π(G)/W)`." -/
noncomputable def _root_.GraphMinor.RootedHypergraph.slash (G : RootedHypergraph α β) (W : Set α) :
    RootedHypergraph α β where
  toHypergraph := quotientVertices G.toHypergraph W
  roots := marchSlash G.roots W
  roots_nodup := nodup_marchSlash G.roots_nodup W
  roots_subset v hv := by
    obtain ⟨h₁, h₂⟩ := mem_marchSlash.mp hv
    exact ⟨G.roots_subset v h₁, h₂⟩

/-- The patch `Δ'` of `P/W` obtained from `Δ` (Graph Minors XX, Section 4, page 333): "$\Delta'(e)$
consists of all groupings $K'$ with vertex set $Z \setminus W$ such that $K'
\cup N_{W \cap Z} \in \Delta(e)$." -/
def patchSlash (Δ : GM04.Patch α) (W : Set α) : GM04.Patch α where
  verts := Δ.verts \ W
  groupings := {K | GM04.IsGrouping (Δ.verts \ W) K ∧ K.verts = Δ.verts \ W ∧
    K ⊔ GM04.emptySubgraph (W ∩ Δ.verts) ∈ Δ}
  isGrouping _ h := h.1
  verts_eq _ h := h.2.1

/-- `N_{W ∩ Z}` together with a grouping `K` on `Z \ W` is a grouping on `Z`, the only grouping-
theoretic fact needed to see that `P/W` is a patchwork. -/
theorem isGrouping_sup_emptySubgraph {Z W : Set α} {K : (⊤ : SimpleGraph α).Subgraph}
    (hK : GM04.IsGrouping (Z \ W) K) :
    GM04.IsGrouping Z (K ⊔ GM04.emptySubgraph (W ∩ Z)) := by
  rw [GM04.isGrouping_iff] at hK ⊢
  refine ⟨?_, fun a b c hac hab hbc ↦ ?_⟩
  · rintro x (hx | hx)
    · exact (hK.1 hx).1
    · exact hx.2
  · simp only [SimpleGraph.Subgraph.sup_adj, GM04.not_emptySubgraph_adj, or_false] at hab hbc ⊢
    exact hK.2 a b c hac hab hbc

/-- `P/W` for an `Ω`-patchwork (Graph Minors XX, Section 4, page 333): "If $P = (G, \mu, \Delta)$ is
a patchwork and $W \subseteq V(G)$, $P/W$ denotes the patchwork
$(G/W, \mu', \Delta')$ where for $e \in dom(\mu)$, $\mu'(e) = \mu(e)/W$, and for $e \in
E(G)$, if $Z$ denotes the set of ends of $e$ in $G$ then $\Delta'(e)$ consists of all
groupings $K'$ with vertex set $Z \setminus W$ such that $K' \cup N_{W \cap Z} \in
\Delta(e)$. If $P = (G, \mu, \Delta, \phi)$ is an $\Omega$-patchwork and $W \subseteq V(G)$,
$P/W$ denotes the $\Omega$-patchwork $(G/W, \mu', \Delta', \phi)$" -/
noncomputable def _root_.GraphMinor.GM04.Patchwork.slash {Ω : Type*} (P : GM04.Patchwork Ω α β)
    (W : Set α) : GM04.Patchwork Ω α β where
  G := P.G.slash W
  dom := P.dom
  μ e := marchSlash (P.μ e) W
  Δ e := patchSlash (P.Δ e) W
  φ := P.φ
  dom_subset := P.dom_subset
  μ_nodup e he := nodup_marchSlash (P.μ_nodup e he) W
  μ_set e he := by
    ext v
    have h := Set.ext_iff.mp (P.μ_set e he) v
    simp only [mem_ofPred_eq, mem_marchSlash] at h ⊢
    exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h.mp h₁, h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h.mpr h₁, h₂⟩⟩
  Δ_verts e he := by
    change (P.Δ e).verts \ W = _
    rw [P.Δ_verts e he]
    ext v
    exact ⟨fun h ↦ h, fun h ↦ h⟩
  Δ_free e he hnd := by
    intro δ hδ hV
    exact ⟨hδ, hV, P.Δ_free e he hnd _ (isGrouping_sup_emptySubgraph hδ) (by
      ext x
      simp only [SimpleGraph.Subgraph.verts_sup, GM04.emptySubgraph_verts, hV, patchSlash]
      by_cases hx : x ∈ W <;> simp [hx])⟩

/-- `P₁` is a condensation of `P₂` (Graph Minors XX, Section 4, page 334): "$V(G_1) = V(G_2)$,
$\pi(G_1) = \pi(G_2)$, $dom(\mu_1) = E(G_1)$, $dom(\mu_2) = E(G_2)$, for
each $e \in E(G_1)$ there is a rooted subhypergraph $A_e \subseteq G_2$ with the following
properties: - $V(A_e)$ is the set of ends of $e$ in $G_1$, and $\pi(A_e) = \mu_1(e)$, -
$\bigcup_{e \in E(G_1)} E(A_e) = E(G_2)$, - for distinct $e, e' \in E(G_1)$, $E(A_e) \cap
E(A_{e'}) = \emptyset$, - for each $e \in E(G_1)$ and $K \in \Delta_1(e)$, $K$ is feasible
in $P_2|A_e$." -/
def IsCondensation (P₁ P₂ : UnlabeledPatchwork α β) : Prop :=
  P₁.G.vertexSet = P₂.G.vertexSet ∧ P₁.G.roots = P₂.G.roots ∧ P₁.dom = P₁.G.edgeSet ∧
    P₂.dom = P₂.G.edgeSet ∧ ∃ A : β → RootedHypergraph α β,
      (∀ e ∈ P₁.G.edgeSet, (A e).toHypergraph ≤ P₂.G.toHypergraph ∧
        (A e).vertexSet = P₁.G.ends e ∧ (A e).roots = P₁.μ e) ∧
      (⋃ e ∈ P₁.G.edgeSet, (A e).edgeSet) = P₂.G.edgeSet ∧
      (∀ e ∈ P₁.G.edgeSet, ∀ e' ∈ P₁.G.edgeSet, e ≠ e' → Disjoint (A e).edgeSet (A e').edgeSet) ∧
      ∀ e ∈ P₁.G.edgeSet, ∀ K ∈ P₁.Δ e, IsFeasibleGrouping (P₂.restrict (A e)) K

/-! ## Section 5: isolation modulo a subset -/

/-- `Z(G) = V(G) ∪ E(G)` (Graph Minors XX, Section 5, page 336). -/
def zSet (G : Hypergraph α β) : Set (α ⊕ β) := Sum.inl '' G.vertexSet ∪ Sum.inr '' G.edgeSet

section Distinction

variable {Λ : Type*} [LE Λ] (lam : Hypergraph α β × Hypergraph α β → Λ)
  (G : Hypergraph α β) (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (W : Set (α ⊕ β)) (θ : ℕ)

/-- The first two conditions in the definition of `ℳ(𝒯, W, θ)` (Graph Minors XX, Section 5,
page 336): `(A, B) ∈ 𝒯` has order `< θ`, `W ⊈ Z(B)`, and `(A, B)` is the `(𝒯, 𝒯')`-distinction for
some tangle `𝒯'` in `G`. -/
def InMPre (A B : Hypergraph α β) : Prop :=
  (A, B) ∈ 𝒯 ∧ separationOrder A B < θ ∧ ¬ W ⊆ zSet B ∧
    ∃ (θ' : ℕ) (𝒯' : Set (Hypergraph α β × Hypergraph α β)), IsTangle G θ' 𝒯' ∧
      IsDistinction lam 𝒯 𝒯' A B

/-- `(A, B) ∈ ℳ(𝒯, W, θ)` (Graph Minors XX, Section 5, page 336). -/
def InM (A B : Hypergraph α β) : Prop :=
  InMPre lam G 𝒯 W θ A B ∧ ∀ ⦃A' B' : Hypergraph α β⦄, InMPre lam G 𝒯 W θ A' B' →
    (A', B') ≠ (A, B) → ¬ (A ≤ A' ∧ B' ≤ B)

/-- `ℒ` `θ`-isolates `𝒯` modulo `W` (Graph Minors XX, Section 5, page 337): "{L}$ has order $<
\theta$, $\mathcal{L}^- \subseteq \mathcal{T}$, and for each $A \in
\mathcal{L}$ and every tangle $\mathcal{T}'$ in $G$ of order $\ge \theta$ with $((G
\setminus A)^-, A^-) \in \mathcal{T}'$, if $(C, D)$ is the $(\mathcal{T},
\mathcal{T}')$-distinction then either $C \subseteq A^-$ and $(G \setminus A)^- \subseteq
D$, or $W \nsubseteq Z(D)$." -/
structure IsolatesModulo (G : RootedHypergraph α β) (ℒ : Set (RootedHypergraph α β)) : Prop where
  isRootedLocation : IsRootedLocation G ℒ
  order_lt : ∀ ⦃A⦄, A ∈ ℒ → A.rootSet.ncard < θ
  subset : rootedLocationToLocation G ℒ ⊆ 𝒯
  distinction : ∀ ⦃A⦄, A ∈ ℒ → ∀ ⦃θ' : ℕ⦄ ⦃𝒯' : Set (Hypergraph α β × Hypergraph α β)⦄,
    IsTangle G.toHypergraph θ' 𝒯' → θ ≤ θ' → (complementHypergraph G A, A.toHypergraph) ∈ 𝒯' →
    ∀ ⦃C D⦄, IsDistinction lam 𝒯 𝒯' C D →
      (C ≤ A.toHypergraph ∧ complementHypergraph G A ≤ D) ∨ ¬ W ⊆ zSet D

/-- `ℒ` is `W`-suitable (Graph Minors XX, Section 5, page 337), with respect to `θ`, `𝒯` and `λ`:
- `ℒ` is fine, and `ℒ⁻ ⊆ 𝒯`, and `ℒ` has order `< θ²`,
- for each tangle `𝒯'` in `G` of order `≥ θ²`, if `(C, D) ∈ ℒ⁻` and `(D, C) ∈ 𝒯'` and `(A, B)` is
  the `(𝒯, 𝒯')`-distinction then either `A ⊆ C` and `D ⊆ B`, or `A ⊆ A*` and `B* ⊆ B` for some
  `(A*, B*) ∈ ℳ(𝒯, W, θ)`. -/
structure IsSuitable (G : RootedHypergraph α β) (ℒ : Set (RootedHypergraph α β)) : Prop where
  isRootedLocation : IsRootedLocation G ℒ
  fine : (∀ v ∈ G.vertexSet, ∃ A ∈ ℒ, v ∈ A.vertexSet) ∧ ∀ e ∈ G.edgeSet, ∃ A ∈ ℒ, e ∈ A.edgeSet
  subset : rootedLocationToLocation G ℒ ⊆ 𝒯
  order_lt : ∀ ⦃A⦄, A ∈ ℒ → A.rootSet.ncard < θ ^ 2
  distinction : ∀ ⦃θ' : ℕ⦄ ⦃𝒯' : Set (Hypergraph α β × Hypergraph α β)⦄,
    IsTangle G.toHypergraph θ' 𝒯' → θ ^ 2 ≤ θ' → ∀ ⦃C D⦄, (C, D) ∈ rootedLocationToLocation G ℒ →
    (D, C) ∈ 𝒯' → ∀ ⦃A B⦄, IsDistinction lam 𝒯 𝒯' A B →
      (A ≤ C ∧ D ≤ B) ∨ ∃ A' B', InM lam G.toHypergraph 𝒯 W θ A' B' ∧ A ≤ A' ∧ B' ≤ B

end Distinction

/-- A rooted location `ℒ` is fine if `⋃ (A⁻ : A ∈ ℒ) = G⁻` (Graph Minors XX, Section 5, page 337).
-/
def IsFine (G : RootedHypergraph α β) (ℒ : Set (RootedHypergraph α β)) : Prop :=
  (∀ v ∈ G.vertexSet, ∃ A ∈ ℒ, v ∈ A.vertexSet) ∧ ∀ e ∈ G.edgeSet, ∃ A ∈ ℒ, e ∈ A.edgeSet

/-! ## Section 6: eliminating the tie-breaker -/

/-- The weight `Σ (v(x) : x ∈ X)` of a set `X ⊆ Z(G)`. -/
noncomputable def weight (G : Hypergraph α β) (v : α ⊕ β → ℝ) (X : Set (α ⊕ β)) : ℝ :=
  ∑ᶠ x ∈ X ∩ zSet G, v x

/-- The triple `(|V(A ∩ B)|, Σ(v(x) : x ∈ Z(G) \ Z(A)), Σ(v(x) : x ∈ V(A ∩ B)))` (Graph Minors XX,
Section 6, page 342), for a separation `(A, B)` with `f ∈ E(A)`. -/
noncomputable def edgeBasedTriple (G : Hypergraph α β) (v : α ⊕ β → ℝ) (A B : Hypergraph α β) :
    ℝ ×ₗ ℝ ×ₗ ℝ :=
  toLex ((separationOrder A B : ℝ),
    toLex (weight G v (zSet G \ zSet A), weight G v (Sum.inl '' (A ∩ B).vertexSet)))

/-- The tie-breaker defined by `f, v` (Graph Minors XX, Section 6, page 342): `λ(A, B)` is the
triple
above for `f ∈ E(A)`, and "If $(A, B)$ is a separation with $f \in E(B)$, we define $\lambda(A, B) =
\lambda(B, A)$." -/
noncomputable def edgeBasedLam (G : Hypergraph α β) (f : β) (v : α ⊕ β → ℝ)
    (p : Hypergraph α β × Hypergraph α β) : ℝ ×ₗ ℝ ×ₗ ℝ :=
  open Classical in
  if f ∈ p.1.edgeSet then edgeBasedTriple G v p.1 p.2 else edgeBasedTriple G v p.2 p.1

/-- `v` assigns positive, rationally independent reals to the members of `Z(G)` (Graph Minors XX,
Section 6, page 342). -/
def IsIndependentWeight (G : Hypergraph α β) (v : α ⊕ β → ℝ) : Prop :=
  (∀ x ∈ zSet G, 0 < v x) ∧ LinearIndependent ℚ (fun x : zSet G ↦ v x)

/-- `lam` is an edge-based tie-breaker in `G`, defined by `f, v` (Graph Minors XX, Section 6,
page 344). -/
def IsDefinedBy (G : Hypergraph α β) (lam : Hypergraph α β × Hypergraph α β → ℝ ×ₗ ℝ ×ₗ ℝ) (f : β)
    (v : α ⊕ β → ℝ) : Prop :=
  f ∈ G.edgeSet ∧ IsIndependentWeight G v ∧ ∀ A B, G.IsSeparation A B → lam (A, B) =
    edgeBasedLam G f v (A, B)

/-- `lam` is an edge-based tie-breaker in `G` (Graph Minors XX, Section 6, page 344). -/
def IsEdgeBased (G : Hypergraph α β) (lam : Hypergraph α β × Hypergraph α β → ℝ ×ₗ ℝ ×ₗ ℝ) : Prop :=
  ∃ f v, IsDefinedBy G lam f v

/-- `ℒ` is linked to `𝒯` (Graph Minors XX, Section 6, page 344): "{L}^- \subseteq \mathcal{T}$ and
for each $A \in \mathcal{L}$ there is no $(A', B') \in
\mathcal{T}$ of order less than $|\bar{\pi}(A)|$ with $A^- \subseteq A'$ and $B' \subseteq
(G \setminus A)^-$." -/
def IsLinkedTo (G : RootedHypergraph α β) (𝒯 : Set (Hypergraph α β × Hypergraph α β))
    (ℒ : Set (RootedHypergraph α β)) : Prop :=
  rootedLocationToLocation G ℒ ⊆ 𝒯 ∧ ∀ ⦃A⦄, A ∈ ℒ → ∀ ⦃A' B'⦄, (A', B') ∈ 𝒯 →
    A.toHypergraph ≤ A' → B' ≤ complementHypergraph G A → A.rootSet.ncard ≤ separationOrder A' B'

/-- `ℒ/W = {A/W : A ∈ ℒ}` (Graph Minors XX, Section 6, page 344). -/
noncomputable def locationSlash (ℒ : Set (RootedHypergraph α β)) (W : Set α) :
    Set (RootedHypergraph α β) :=
  (fun A ↦ A.slash W) '' ℒ

/-! ## Section 7: another adjustment -/

/-- A patchwork or `Ω`-patchwork is free if `Δ(e)` is free for all `e ∈ E(G)` (Graph Minors XX,
Section 7, page 346). -/
def IsFree {Ω : Type*} (P : GM04.Patchwork Ω α β) : Prop := ∀ e ∈ P.G.edgeSet, (P.Δ e).IsFree

/-! ## Section 8: surfaces and paintings -/

/-- A painting in a surface (Graph Minors XX, Section 8, page 347):
"A *painting* $\Gamma$ in a surface $\Sigma$ is a triple $(U, N, \gamma)$, where $U \subseteq
\Sigma$ is closed, $N \subseteq U$ is finite, and
- $bd(\Sigma) \subseteq U$, and $U \setminus N$ has only finitely many arc-wise connected
components, called *cells*,
- for each cell $c$, $\bar{c}$ is a closed disc and $|\tilde{c}| = 2$ or 3 and $\bar{c} \cap N =
\tilde{c} \subseteq bd(\bar{c})$,
- for each cell $c$, if $c \cap bd(\Sigma) \ne \emptyset$ then $|\tilde{c}| = 2$, and $\bar{c} \cap
bd(\Sigma)$ is a line and its ends are the members of $\tilde{c}$,
- for each cell $c$, $\gamma(c)$ is a march $\mu$ with $\bar{\mu} = \tilde{c}$," -/
structure Painting (S : Type) [TopologicalSpace S] where
  /-- The set `U(Γ)`. -/
  U : Set S
  /-- The set `N(Γ)` of nodes. -/
  N : Set S
  /-- The march `γ(c)` of a cell. -/
  γ : Set S → List S
  isClosed_U : IsClosed U
  N_subset : N ⊆ U
  finite_N : N.Finite
  bd_subset : bd S ⊆ U
  finite_cells : (arcComponentsIn (U \ N)).Finite
  cell_disc : ∀ c ∈ arcComponentsIn (U \ N), IsClosedDisc (closure c)
  cell_size : ∀ c ∈ arcComponentsIn (U \ N), (tilde c).Finite ∧
    ((tilde c).ncard = 2 ∨ (tilde c).ncard = 3)
  closure_inter : ∀ c ∈ arcComponentsIn (U \ N), closure c ∩ N = tilde c
  tilde_subset : ∀ c ∈ arcComponentsIn (U \ N), tilde c ⊆ discBd (closure c)
  border_cell : ∀ c ∈ arcComponentsIn (U \ N), (c ∩ bd S).Nonempty →
    (tilde c).ncard = 2 ∧ IsLine (closure c ∩ bd S) ∧ lineEnds (closure c ∩ bd S) = tilde c
  γ_nodup : ∀ c ∈ arcComponentsIn (U \ N), (γ c).Nodup
  γ_set : ∀ c ∈ arcComponentsIn (U \ N), {n | n ∈ γ c} = tilde c

namespace Painting

variable {S : Type} [TopologicalSpace S]

/-- The set `𝒞(Γ)` of cells. -/
def C (Γ : Painting S) : Set (Set S) := arcComponentsIn (Γ.U \ Γ.N)

/-- A cell `c` is a border cell if `c ∩ bd(Σ) ≠ ∅` (Graph Minors XX, Section 8, page 348). -/
def IsBorder (c : Set S) : Prop := (c ∩ bd S).Nonempty

/-- `Γ` is 3-connected (Graph Minors XX, Section 8, page 348): "- for every $\Gamma$-normal O-arc
$F$ in $\Sigma$ with $|F \cap N(\Gamma)| \le 2$ there is a
closed disc $\Delta \subseteq \Sigma$ with $bd(\Delta) = F$ which includes at most one cell
of $\Gamma$ and with $\Delta \cap N(\Gamma) \subseteq F$, - for every $\Gamma$-normal line
$F$ in $\Sigma$ with $|F \cap N(\Gamma)| \le 2$ and with both ends in $bd(\Sigma)$ and with
no other point in $bd(\Sigma)$, there is a closed disc $\Delta \subseteq \Sigma$ with $F
\subseteq bd(\Delta) \subseteq F \cup bd(\Sigma)$ which includes at most one cell of
$\Gamma$ and with $\Delta \cap N(\Gamma) \subseteq F$." -/
def IsThreeConnected (Γ : Painting S) : Prop :=
  (∀ F : Set S, IsOArc F → F ∩ Γ.U ⊆ Γ.N → (F ∩ Γ.N).ncard ≤ 2 →
    ∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F ∧ {c ∈ Γ.C | c ⊆ Δ}.ncard ≤ 1 ∧ Δ ∩ Γ.N ⊆ F) ∧
  (∀ F : Set S, IsLine F → F ∩ Γ.U ⊆ Γ.N → (F ∩ Γ.N).ncard ≤ 2 → F ∩ bd S = lineEnds F →
    ∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd S ∧
      {c ∈ Γ.C | c ⊆ Δ}.ncard ≤ 1 ∧ Δ ∩ Γ.N ⊆ F)

/-- The skeleton `sk(Γ)` (Graph Minors XX, Section 8, page 348): for distinct `n₁, n₂ ∈ N(Γ)`, they
are adjacent if and only if there is a cell `c` with `n₁, n₂ ∈ cTilde`. -/
def sk (Γ : Painting S) : SimpleGraph S where
  Adj x y := x ≠ y ∧ x ∈ Γ.N ∧ y ∈ Γ.N ∧ ∃ c ∈ Γ.C, x ∈ tilde c ∧ y ∈ tilde c
  symm := ⟨fun _ _ ⟨h, hx, hy, c, hc, hxc, hyc⟩ ↦ ⟨h.symm, hy, hx, c, hc, hyc, hxc⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

end Painting

/-- A linear inflation of `Γ` in `Γ'` (Graph Minors XX, Section 8, page 348), the seven conditions
of
the paper. The non-null induced connected subgraph `ζ(n)` of `sk(Γ')` is given by its vertex set
`ζn n`. -/
structure IsLinearInflation {S : Type} [TopologicalSpace S] (Γ Γ' : Painting S) (ζn : S → Set S)
    (ζc : Set S → Set S) : Prop where
  /-- First condition. -/
  cell_mem : ∀ c ∈ Γ.C, ζc c ∈ Γ'.C
  cell_size : ∀ c ∈ Γ.C, (tilde (ζc c)).ncard = (tilde c).ncard
  borders_iff : ∀ c ∈ Γ.C, ∀ Θ ∈ cuffs S, (c ∩ Θ).Nonempty ↔ (ζc c ∩ Θ).Nonempty
  /-- Second condition. -/
  cell_injOn : InjOn ζc Γ.C
  /-- Third condition. -/
  orientation : ∀ c ∈ Γ.C, ∀ Θ ∈ cuffs S, (c ∩ Θ).Nonempty → ∀ f : Circle ≃ₜ Θ,
    ∀ n n', (Γ.γ c).head? = some n → (Γ'.γ (ζc c)).head? = some n' →
      GM19.ImmediatelyPrecedes f n (c ∩ Θ) → GM19.ImmediatelyPrecedes f n' (ζc c ∩ Θ)
  /-- Fourth condition. -/
  node_nonempty : ∀ n ∈ Γ.N, (ζn n).Nonempty
  node_subset : ∀ n ∈ Γ.N, ζn n ⊆ Γ'.N
  node_connected : ∀ n ∈ Γ.N, (Γ'.sk.induce (ζn n)).Preconnected
  /-- Fifth condition. -/
  node_disjoint : ∀ n₁ ∈ Γ.N, ∀ n₂ ∈ Γ.N, n₁ ≠ n₂ → Disjoint (ζn n₁) (ζn n₂)
  /-- Sixth condition: "$n$ is the $i$th node of $c$ if and only if $\zeta(n)$ contains the $i$th
  node of $\zeta(c)$". -/
  nodes : ∀ n ∈ Γ.N, ∀ c ∈ Γ.C, ∀ (i : ℕ) (hi : i < (Γ.γ c).length)
    (hi' : i < (Γ'.γ (ζc c)).length), (Γ.γ c)[i] = n ↔ (Γ'.γ (ζc c))[i] ∈ ζn n
  /-- Seventh condition. -/
  border_cell : ∀ c' ∈ Γ'.C, Painting.IsBorder c' → c' ∉ ζc '' Γ.C → ∃ n ∈ Γ.N, tilde c' ⊆ ζn n

/-! ## Section 9: patchworks from a surface -/

/-- A graded surface `(Σ, ρ)` (Graph Minors XX, Section 9, page 348): a surface `Σ` (compact and
connected, with possibly null boundary) and an integer `ρ(Θ) ≥ 0` for each cuff `Θ`. -/
structure GradedSurface where
  /-- The surface `Σ`. -/
  S : Type
  /-- The topology of `Σ`. -/
  [top : TopologicalSpace S]
  isSurface : IsSurface S
  connected : ConnectedSpace S
  /-- The grading `ρ`. -/
  ρ : Set S → ℕ

attribute [instance] GradedSurface.top

/-- `(Γ, β)` is a `(Σ, ρ)`-hull for a hypergraph `G` (Graph Minors XX, Section 9, pages 348–349).
The paper has `N(Γ) ⊆ V(G)` and `𝒞(Γ) = E(G)`. Here vertices of `G` lie in `α` and edges in `β`, so
the identification is given by an injection `node` of `N(Γ)` into `V(G)` and a bijection `cell` from
`𝒞(Γ)` onto `E(G)`. -/
structure Hull {X : GradedSurface} (Γ : Painting X.S) (G : Hypergraph α β) where
  /-- The vertex of `G` that is a node of `Γ`. -/
  node : X.S → α
  /-- The edge of `G` that is a cell of `Γ`. -/
  cell : Set X.S → β
  /-- The set `β(n)` for a border node `n`. -/
  border : X.S → Set α
  node_injOn : InjOn node Γ.N
  node_mem : ∀ n ∈ Γ.N, node n ∈ G.vertexSet
  cell_bijOn : BijOn cell Γ.C G.edgeSet
  /-- "for each $n \in N(\Gamma)$ and $c \in C(\Gamma)$, $n \in \tilde{c}$ if and only if $n$ is
  incident with $c$ in $G$". -/
  inc_iff : ∀ n ∈ Γ.N, ∀ c ∈ Γ.C, n ∈ tilde c ↔ G.Inc (cell c) (node n)
  border_subset : ∀ n ∈ Γ.N ∩ bd X.S, border n ⊆ G.vertexSet
  /-- "`β(n) ∩ N(Γ) = ∅`". -/
  border_disjoint : ∀ n ∈ Γ.N ∩ bd X.S, Disjoint (border n) (node '' Γ.N)
  /-- "$|\beta(n)| = \rho(\Theta)$, where $\Theta$ is the cuff bordered by $n$". -/
  border_ncard : ∀ Θ ∈ cuffs X.S, ∀ n ∈ Γ.N ∩ Θ, (border n).ncard = X.ρ Θ
  /-- "for nodes $n_1, n_2$ bordering distinct cuffs, $\beta(n_1) \cap \beta(n_2) = \emptyset$". -/
  border_cuffs : ∀ Θ₁ ∈ cuffs X.S, ∀ Θ₂ ∈ cuffs X.S, Θ₁ ≠ Θ₂ → ∀ n₁ ∈ Γ.N ∩ Θ₁, ∀ n₂ ∈ Γ.N ∩ Θ₂,
    Disjoint (border n₁) (border n₂)
  /-- "V(G) = N(\Gamma) \cup \bigcup (\beta(n) : n \in N(\Gamma) \cap bd(\Sigma))". -/
  vertexSet_eq : G.vertexSet = node '' Γ.N ∪ ⋃ n ∈ Γ.N ∩ bd X.S, border n
  /-- "for each internal cell $c$, the set of ends of $c$ in $G$ is $\tilde{c}$". -/
  ends_internal : ∀ c ∈ Γ.C, ¬ Painting.IsBorder c → G.ends (cell c) = node '' tilde c
  /-- "for each border cell $c$ with $n_1, n_2$ the set of ends of $c$ in $G$ is $\beta(n_1) \cup
  \beta(n_2) \cup \{n_1, n_2". -/
  ends_border : ∀ c ∈ Γ.C, Painting.IsBorder c →
    G.ends (cell c) = node '' tilde c ∪ ⋃ n ∈ tilde c, border n
  /-- "if $n_1, n_2, n_3, n_4 \in N(\Gamma)$ border the same cuff in order, then $\beta(n_1) \cap
  \beta(n_3) \subseteq \beta(n_2) \cup \beta(n_4)$". -/
  border_order : ∀ Θ ∈ cuffs X.S, ∀ n₁ ∈ Γ.N ∩ Θ, ∀ n₂ ∈ Γ.N ∩ Θ, ∀ n₃ ∈ Γ.N ∩ Θ, ∀ n₄ ∈ Γ.N ∩ Θ,
    GM19.InOrderOn Θ n₁ n₂ n₃ n₄ → border n₁ ∩ border n₃ ⊆ border n₂ ∪ border n₄

/-- `M` is a pairing as in the second part of the definition of `(Σ, ρ)`-hulled (Graph Minors XX,
Section 9, page 349): a pairing `M_c` with `V(M_c) = β(n₁) ∪ β(n₂) ∪ {n₁, n₂}`, such that `n₁, n₂`
are
adjacent in `M_c`, and `M_c` has `|β(n₁)| + 1 = |β(n₂)| + 1` components, each containing one vertex
of `β(n₁) ∪ {n₁}` and one of `β(n₂) ∪ {n₂}` (possibly the same). -/
structure IsCellPairing {X : GradedSurface} {Γ : Painting X.S} {G : Hypergraph α β}
    (h : Hull Γ G) (n₁ n₂ : X.S) (M : (⊤ : SimpleGraph α).Subgraph) : Prop where
  isPairing : GM04.IsPairing M.verts M
  verts_eq : M.verts = h.border n₁ ∪ h.border n₂ ∪ {h.node n₁, h.node n₂}
  adj : M.Adj (h.node n₁) (h.node n₂)
  components : ∀ D, GM04.IsComponent M D →
    (D.verts ∩ (h.border n₁ ∪ {h.node n₁})).ncard = 1 ∧
      (D.verts ∩ (h.border n₂ ∪ {h.node n₂})).ncard = 1

/-- The patchwork `P = (G, μ, Δ)` is `(Σ, ρ)`-hulled by `(Γ, h)` (Graph Minors XX, Section 9,
page 349). -/
structure IsHulledBy {X : GradedSurface} {Γ : Painting X.S} (P : UnlabeledPatchwork α β)
    (h : Hull Γ P.G.toHypergraph) : Prop where
  three_connected : Γ.IsThreeConnected
  /-- "for each internal cell $c \in C(\Gamma)$, $\Delta(c)$ is free". -/
  free_internal : ∀ c ∈ Γ.C, ¬ Painting.IsBorder c → (P.Δ (h.cell c)).IsFree
  /-- The second condition: the pairing `M_c`. -/
  border_pairing : ∀ c ∈ Γ.C, Painting.IsBorder c → ∀ n₁ ∈ tilde c, ∀ n₂ ∈ tilde c, n₁ ≠ n₂ →
    ∃ M, IsCellPairing h n₁ n₂ M ∧ (M ∈ P.Δ (h.cell c) ∨
      (M.deleteEdges {s(h.node n₁, h.node n₂)} ∈ P.Δ (h.cell c) ∧
        ∃ c' ∈ Γ.C, ¬ Painting.IsBorder c' ∧ n₁ ∈ tilde c' ∧ n₂ ∈ tilde c'))
  /-- "`π(G) = 0` and `dom(μ) = E(G)`". -/
  roots_nil : P.G.roots = []
  dom_eq : P.dom = P.G.edgeSet
  /-- "for each internal cell $c$, and for $1 \le i \le |\tilde{c}|$ the $i$th term of $\mu(c)$ is
  the $i$th node of $c$". -/
  μ_internal : ∀ c ∈ Γ.C, ¬ Painting.IsBorder c → P.μ (h.cell c) = (Γ.γ c).map h.node

/-- `P` is `(Σ, ρ)`-hulled (Graph Minors XX, Section 9, page 349). -/
def IsHulled (X : GradedSurface) (P : UnlabeledPatchwork α β) : Prop :=
  ∃ (Γ : Painting X.S) (h : Hull Γ P.G.toHypergraph), IsHulledBy P h

/-! ## Section 10: excluding a minor -/

/-- `(P, ℒ)` is `(Σ, ρ)`-shelled (Graph Minors XX, Section 10, pages 353–354), for a free rootless
patchwork `P`: `ℒ` is fine and there is a heart `P'` of `(P, ℒ)` with `E(G') = {e(A) : A ∈ ℒ}`, and
a
`(Σ, ρ)`-hull `(Γ, h)` for `G'⁻`, such that the two conditions on cells hold. -/
def IsShelled (X : GradedSurface) (P : UnlabeledPatchwork α β) (ℒ : Set (RootedHypergraph α β)) :
    Prop :=
  IsFine P.G ℒ ∧ ∃ (newEdge : RootedHypergraph α β → β) (P' : UnlabeledPatchwork α β)
    (Γ : Painting X.S) (h : Hull Γ P'.G.toHypergraph),
    IsPatchworkHeart P ℒ newEdge P' ∧ P'.G.edgeSet = newEdge '' ℒ ∧ Γ.IsThreeConnected ∧
    (∀ c ∈ Γ.C, ∀ A ∈ ℒ, h.cell c = newEdge A → ¬ Painting.IsBorder c →
      A.roots = (Γ.γ c).map h.node ∧
      ∀ K : (⊤ : SimpleGraph α).Subgraph, GM04.IsGrouping (h.node '' tilde c) K →
        K.verts = h.node '' tilde c →
        ∃ C : SimpleGraph α, C ≤ A.toHypergraph.skeleton ∧ ∀ x ∈ K.verts, ∀ y ∈ K.verts, x ≠ y →
          (C.Reachable x y ↔ K.Adj x y)) ∧
    (∀ c ∈ Γ.C, ∀ A ∈ ℒ, h.cell c = newEdge A → ∀ Θ ∈ cuffs X.S, (c ∩ Θ).Nonempty →
      ∀ n₁ ∈ tilde c, ∀ n₂ ∈ tilde c, n₁ ≠ n₂ →
      ∃ L : Fin (X.ρ Θ) → PathFromTo A.toHypergraph.skeleton (h.border n₁) (h.border n₂),
        (Pairwise fun i j ↦ Disjoint {z | z ∈ (L i).walk.support} {z | z ∈ (L j).walk.support}) ∧
        (∀ i, h.node n₁ ∉ (L i).walk.support ∧ h.node n₂ ∉ (L i).walk.support) ∧
        ((∃ L₀ : PathFromTo A.toHypergraph.skeleton {h.node n₁} {h.node n₂},
            ∀ i, Disjoint {z | z ∈ L₀.walk.support} {z | z ∈ (L i).walk.support}) ∨
          ∃ c' ∈ Γ.C, ¬ Painting.IsBorder c' ∧ n₁ ∈ tilde c' ∧ n₂ ∈ tilde c'))

end GraphMinor.GM20
