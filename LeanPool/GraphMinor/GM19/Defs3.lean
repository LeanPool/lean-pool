/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Defs2
public import LeanPool.GraphMinor.Surface.TopologyStatements

/-!
# Definitions for Graph Minors XIX, Sections 9–14

This file formalizes the remaining definitions of N. Robertson and P. D. Seymour,
*Graph Minors. XIX. Well-quasi-ordering on a surface*, J. Combin. Theory Ser. B **90** (2004),
325–385, Sections 9–14:

- **Section 9 (pages 351–353):** Disjoint colour schemes (`ColourScheme.IsDisjoint`,
  `ColourScheme.unionWQO`), inflations of subhypergraphs (`IsSubInflationIn`),
  $M(\Gamma, \mathscr{L})$ (`RootedLocation.M`), outlines (`IsOutline`), $\chi$-places (`Place`),
  and well-behaved sets of $\chi$-places (`IsWellBehavedPlaces`).
- **Section 10 (pages 353–357):** Tangle flaws: representativeness flaws (`IsRepFlaw`), distance
  flaws (`IsFlawedInDistance`), and freedom flaws (`IsFlawedInFreedom`).
- **Section 11 (pages 357–361):** Border label flaws: bites at a pole $r^*$ (`IsBiteAt`), their
  arcs (`IsBiteArc`, `biteArc`), the
  border distance $l(e_1, e_2)$ (`borderEdgeDist`), $(n, (\omega_1, \dots, \omega_m))$-flaws on a
  long side $S$ (`IsFlawedOnSide`), feasts (`IsFeast`), disjoint feasts (`IsDisjointFeast`), and
  $((\omega_1, \dots, \omega_m), S)$-flaws (`IsSideLabelFlaw`).
- **Section 12 (pages 362–365):** Internal label flaws: $(m, n, \omega_0)$-internal flaws
  (`IsFlawedInternally`), wheels (`IsWheel`), $W$-hubs of radius $\rho$ (`IsWheelHubOfRadius`),
  wheel radius (`wheelRadius`), and wheel covers (`IsWheelCover`).
- **Section 13 (pages 366–375):** Spokes of a wheel (`IsSpoke`), inner ends of spokes, optimal
  $W$-hubs (`IsOptimalWheelHub`), boundary sector discs $\Delta_v$ and boundary sector circuits
  $D_v$ (`IsBoundarySector`).
- **Section 14 (pages 375–379):** Singular and regular boundary region vertices
  (`IsSingularBoundaryRegion`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Function Topology
open GraphMinor.Surface GraphMinor.Hypergraph

universe u w

variable {S : Type u} [TopologicalSpace S] {α : Type w}

/-! ## Section 9: Disjoint colour schemes, outlines, and places -/

open Classical in
/-- A colour scheme `χ` is *disjoint* if `Ω_χ(3)`, `Ω_χ(2)` and all the `Ω_χ(S)`'s (over all sides
`S` of `Φ_χ`) have mutually disjoint element sets (Graph Minors XIX, Section 9, page 351:
"A colour scheme $\chi$ is *disjoint* if $\Omega_{\chi}(3)$, $\Omega_{\chi}(2)$ and all the
$\Omega_{\chi}(S)$'s (over all sides $S$ of $\Phi_{\chi}$) have mutually disjoint element
sets, and if $\chi$ is disjoint we denote the union of these well-quasi-orders by
$\Omega_{\chi}$"). -/
structure ColourScheme.IsDisjoint (χ : ColourScheme S α) : Prop where
  disj_2_3 : Disjoint χ.Ω2.E χ.Ω3.E
  disj_2_S : ∀ s ∈ χ.Φ.sides, Disjoint χ.Ω2.E (χ.ΩS s).E
  disj_3_S : ∀ s ∈ χ.Φ.sides, Disjoint χ.Ω3.E (χ.ΩS s).E
  disj_S_S : ∀ s₁ ∈ χ.Φ.sides, ∀ s₂ ∈ χ.Φ.sides, s₁ ≠ s₂ → Disjoint (χ.ΩS s₁).E (χ.ΩS s₂).E

open Classical in
/-- The union quasi-order `Ω_χ` of `Ω_χ(2)`, `Ω_χ(3)`, and `Ω_χ(S)` over all sides `S` of `Φ_χ`
(Graph Minors XIX, Section 9, page 351:
"If $\Omega_1, \ldots, \Omega_k$ are well-quasi-orders with $E(\Omega_1), \ldots,
E(\Omega_k)$ mutually disjoint, we define their union to be the well-quasi-order $\Omega$
with $E(\Omega) = E(\Omega_1) \cup \cdots \cup E(\Omega_k)$, in which $x \le y$ if and only
if $x, y \in E(\Omega_i)$ for some $i$ and $x \le y$ in $\Omega_i$"). -/
def ColourScheme.unionWQO {χ : ColourScheme S α} (hdisj : χ.IsDisjoint) : QuasiOrder α where
  E := χ.Ω2.E ∪ χ.Ω3.E ∪ ⋃ s ∈ χ.Φ.sides, (χ.ΩS s).E
  le x y :=
    (x ∈ χ.Ω2.E ∧ y ∈ χ.Ω2.E ∧ χ.Ω2.le x y) ∨
    (x ∈ χ.Ω3.E ∧ y ∈ χ.Ω3.E ∧ χ.Ω3.le x y) ∨
    (∃ s ∈ χ.Φ.sides, x ∈ (χ.ΩS s).E ∧ y ∈ (χ.ΩS s).E ∧ (χ.ΩS s).le x y)
  refl x hx := by
    rcases hx with (hx2 | hx3) | hxS
    · exact Or.inl ⟨hx2, hx2, χ.Ω2.refl x hx2⟩
    · exact Or.inr (Or.inl ⟨hx3, hx3, χ.Ω3.refl x hx3⟩)
    · rcases mem_iUnion₂.mp hxS with ⟨s, hs, hxs⟩
      exact Or.inr (Or.inr ⟨s, hs, hxs, hxs, (χ.ΩS s).refl x hxs⟩)
  trans x _ y _ z _ hxy hyz := by
    rcases hxy with ⟨hx2, hy2, h1⟩ | ⟨hx3, hy3, h1⟩ | ⟨s, hs, hxs, hys, h1⟩
    · rcases hyz with ⟨_, hz2, h2⟩ | ⟨hy3, _, _⟩ | ⟨s, hs, hys, _, _⟩
      · exact Or.inl ⟨hx2, hz2, χ.Ω2.trans x hx2 y hy2 z hz2 h1 h2⟩
      · exact False.elim (hdisj.disj_2_3.le_bot ⟨hy2, hy3⟩)
      · exact False.elim ((hdisj.disj_2_S s hs).le_bot ⟨hy2, hys⟩)
    · rcases hyz with ⟨hy2, _, _⟩ | ⟨_, hz3, h2⟩ | ⟨s, hs, hys, _, _⟩
      · exact False.elim (hdisj.disj_2_3.le_bot ⟨hy2, hy3⟩)
      · exact Or.inr (Or.inl ⟨hx3, hz3, χ.Ω3.trans x hx3 y hy3 z hz3 h1 h2⟩)
      · exact False.elim ((hdisj.disj_3_S s hs).le_bot ⟨hy3, hys⟩)
    · rcases hyz with ⟨hy2, _, _⟩ | ⟨hy3, _, _⟩ | ⟨s', hs', hys', hzs', h2⟩
      · exact False.elim ((hdisj.disj_2_S s hs).le_bot ⟨hy2, hys⟩)
      · exact False.elim ((hdisj.disj_3_S s hs).le_bot ⟨hy3, hys⟩)
      · by_cases hss : s = s'
        · subst hss
          exact Or.inr (Or.inr ⟨s, hs, hxs, hzs', (χ.ΩS s).trans x hxs y hys z hzs' h1 h2⟩)
        · exact False.elim ((hdisj.disj_S_S s hs s' hs' hss).le_bot ⟨hys, hys'⟩)

open Classical in
/-- Relation `x ≤ y` in `Ω_χ` (without requiring the disjointness proof in the type). -/
def ColourScheme.unionLE (χ : ColourScheme S α) (x y : α) : Prop :=
  (x ∈ χ.Ω2.E ∧ y ∈ χ.Ω2.E ∧ χ.Ω2.le x y) ∨
  (x ∈ χ.Ω3.E ∧ y ∈ χ.Ω3.E ∧ χ.Ω3.le x y) ∨
  (∃ s ∈ χ.Φ.sides, x ∈ (χ.ΩS s).E ∧ y ∈ (χ.ΩS s).E ∧ (χ.ΩS s).le x y)

open Classical in
/-- An inflation of a subhypergraph `H ⊆ Γ` in a painting `Γ'` (Graph Minors XIX, Section 9,
page 351:
"If $\Gamma, \Gamma'$ are paintings in $\Sigma$, and $H \subseteq \Gamma$ is a subhypergraph,
an *inflation* of $H$ in $\Gamma'$ is a function $\sigma$ with domain $V(H) \cup E(H)$
satisfying the three conditions of the definition of inflation in Section 2 with $\Gamma$
replaced by $H$"). -/
structure IsSubInflationIn (Γ : Painting S) (H : Hypergraph S (Set S)) (Γ' : Painting S)
    (σv : S → Set S) (σe : Set S → Set S) : Prop where
  H_le : H ≤ Γ.toHypergraph
  edge_mem : ∀ e ∈ H.edgeSet, σe e ∈ Γ'.E
  edge_size : ∀ e ∈ H.edgeSet, (tilde (σe e)).ncard = (tilde e).ncard
  edge_injOn : InjOn σe H.edgeSet
  vertex_nonempty : ∀ v ∈ H.vertexSet, (σv v).Nonempty
  vertex_subset : ∀ v ∈ H.vertexSet, σv v ⊆ Γ'.V
  vertex_connected : ∀ v ∈ H.vertexSet, (Γ'.skAdj.induce (σv v)).Preconnected
  vertex_disjoint : ∀ v₁ ∈ H.vertexSet, ∀ v₂ ∈ H.vertexSet, v₁ ≠ v₂ → Disjoint (σv v₁) (σv v₂)
  ends : ∀ e ∈ H.edgeSet, ∀ (i : ℕ) (hi : i < (Γ.γ e).length) (hi' : i < (Γ'.γ (σe e)).length),
    (Γ'.γ (σe e))[i] ∈ σv (Γ.γ e)[i]

open Classical in
/-- The complementary subhypergraph `M(Γ, ℒ) = Γ ∩ ⋂ (Aᶜ : A ∈ ℒ)` of a rooted location `ℒ` in a
painting `Γ` (Graph Minors XIX, Section 9, page 351:
"If $\mathscr{L}$ is a rooted location in $\Gamma$ we define $M(\Gamma, \mathscr{L})$ to be
$$\Gamma \cap \bigcap (A^c : A \in \mathscr{L})"). -/
def RootedLocation.M {Γ : Painting S} (L : RootedLocation Γ) : Hypergraph S (Set S) where
  vertexSet := {v ∈ Γ.V | ∀ A ∈ L.arms, v ∈ A.compl.vertexSet}
  edgeSet := {e ∈ Γ.E | ∀ A ∈ L.arms, e ∈ A.compl.edgeSet}
  Inc e v := (e ∈ Γ.E ∧ ∀ A ∈ L.arms, e ∈ A.compl.edgeSet) ∧ v ∈ Γ.V ∧ v ∈ tilde e
  vertex_mem_of_inc e v h := ⟨h.2.1, fun A hA ↦ by
    have heA : e ∈ A.compl.edgeSet := h.1.2 A hA
    have hends : A.compl.ends e = Γ.toHypergraph.ends e := (A.isSeparation.right_le.ends_eq e
      heA).symm
    have hv_end : v ∈ A.compl.ends e := by
      rw [hends]
      exact ⟨h.1.1, h.2.1, h.2.2⟩
    exact A.compl.vertex_mem_of_inc hv_end⟩
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := Γ.finite_V.subset fun _ hv ↦ hv.1
  edgeSet_finite := Γ.finite_edges.subset fun _ he ↦ he.1

open Classical in
theorem RootedLocation.M_le {Γ : Painting S} (L : RootedLocation Γ) :
    L.M ≤ Γ.toHypergraph where
  vertexSet_subset _ hv := hv.1
  edgeSet_subset _ he := he.1
  ends_eq _ he := by
    ext v
    simp only [Hypergraph.ends, RootedLocation.M, Painting.toHypergraph]
    exact ⟨fun h ↦ ⟨he, h.2.1, h.2.2⟩, fun h ↦ ⟨he.1, h.2.1, h.2.2⟩⟩

open Classical in
/-- A `χ`-place `(Γ, φ, ℒ)` consists of a `χ`-coloured painting `(Γ, φ)` together with a rooted
location `ℒ` in `Γ` (Graph Minors XIX, Section 9, page 352:
"If $\chi$ is disjoint, $(\Gamma, \phi)$ is a $\chi$-coloured painting, and $\mathscr{L}$ is
a rooted location in $\Gamma$, we call $(\Gamma, \phi, \mathscr{L})$ a $\chi$-*place"). -/
structure Place (χ : ColourScheme S α) where
  /-- `χ` is disjoint. -/
  disjoint : χ.IsDisjoint
  /-- The underlying `χ`-coloured painting `(Γ, φ)`. -/
  P : ColouredPainting χ
  /-- The rooted location `ℒ` in `Γ`. -/
  L : RootedLocation P.Γ

open Classical in
/-- An outline `τ : ℒ → ℒ'` of a `χ`-place `(Γ, φ, ℒ)` in `(Γ', φ', ℒ')` (Graph Minors XIX,
Section 9, page 351:
"A function $\tau \colon \mathscr{L} \to \mathscr{L}'$ is an *outline* of $(\Gamma, \phi,
\mathscr{L})$ in $(\Gamma', \phi', \mathscr{L}')$ if there is an inflation $\sigma$ of
$M(\Gamma, \mathscr{L})$ in $\Gamma'$, such that • $\sigma(e) \in E(M(\Gamma',
\mathscr{L}'))$ for each $e \in E(M(\Gamma, \mathscr{L}))$, • for each $A \in \mathscr{L}$,
$|\bar{\pi}(\tau(A))| = |\bar{\pi}(A)|$, and if $A_1, A_2 \in \mathscr{L}$ are distinct then
$\tau(A_1) \ne \tau(A_2)$, • for each $A \in \mathscr{L}$ and $1 \le i \le |\bar{\pi}(A)|$,
if $v$ is the $i$th term of $\pi(A)$ then $\sigma(v)$ contains the $i$th term of
$\pi(\tau(A))$, • for each $A \in \mathscr{L}$ and $v \in V(M(\Gamma, \mathscr{L}))$,
$|V(\sigma(v)) \cap V(\tau(A))| \le 1$, • for each $e \in E(M(\Gamma, \mathscr{L}))$,
$\phi(e) \le \phi'(\sigma(e))$ in $\Omega_{\chi}$"). -/
def IsOutline {χ : ColourScheme S α} (X Y : Place χ)
    (τ : Arm X.P.Γ → Arm Y.P.Γ) : Prop :=
  (∀ A ∈ X.L.arms, τ A ∈ Y.L.arms) ∧
  InjOn τ X.L.arms ∧
  ∃ (σv : S → Set S) (σe : Set S → Set S),
    IsSubInflationIn X.P.Γ X.L.M Y.P.Γ σv σe ∧
    (∀ e ∈ X.L.M.edgeSet, σe e ∈ Y.L.M.edgeSet) ∧
    (∀ A ∈ X.L.arms, (τ A).π.length = A.π.length ∧
      ∀ (i : ℕ) (hi : i < A.π.length) (hi' : i < (τ A).π.length),
        (τ A).π[i] ∈ σv (A.π[i])) ∧
    (∀ A ∈ X.L.arms, ∀ v ∈ X.L.M.vertexSet, (σv v ∩ (τ A).V).ncard ≤ 1) ∧
    (∀ e ∈ X.L.M.edgeSet, χ.unionLE (X.P.φ e) (Y.P.φ (σe e)))

open Classical in
/-- A set `P` of `χ`-places is *well-behaved* (Graph Minors XIX, Section 9, page 352:
"A set $\mathscr{P}$ of $\chi$-places is *well-behaved* if for every well-quasi-order
$\Omega$ and every countable sequence $(\Gamma_i, \phi_i, \mathscr{L}_i)$ ($i = 1, 2,
\ldots$) of members of $\mathscr{P}$, and for all functions $\xi_i \colon \mathscr{L}_i \to
E(\Omega)$, there exist $j > i \ge 1$ and an outline $\tau$ of $(\Gamma_i, \phi_i,
\mathscr{L}_i)$ in $(\Gamma_j, \phi_j, \mathscr{L}_j)$ such that $\xi_i(A) \le
\xi_j(\tau(A))$ for all $A \in \mathscr{L}_i$"). -/
def IsWellBehavedPlaces {χ : ColourScheme S α} (P_set : Set (Place χ)) : Prop :=
  ∀ {β : Type (max u w)} (Ω : QuasiOrder β), Ω.IsWQO →
    ∀ (seq : ℕ → Place χ), (∀ i, seq i ∈ P_set) →
    ∀ (ξ : ∀ i, Arm (seq i).P.Γ → β),
      (∀ i, ∀ A ∈ (seq i).L.arms, ξ i A ∈ Ω.E) →
      ∃ i j, i < j ∧ ∃ τ : Arm (seq i).P.Γ → Arm (seq j).P.Γ,
        IsOutline (seq i) (seq j) τ ∧
        ∀ A ∈ (seq i).L.arms, Ω.le (ξ i A) (ξ j (τ A))

open Classical in
/-- Two `χ`-places `X` and `Y` are related by a `Φ_χ`-preserving homeomorphism `f : S ≃ₜ S`
(Graph Minors XIX, Section 9, page 353:
"We define the image of a $\chi$-place under a $\Phi_\chi$-preserving homeomorphism in the
natural way"). -/
def IsPlaceHomeoImage {χ : ColourScheme S α} (X Y : Place χ) (f : S ≃ₜ S) : Prop :=
  IsFramePreservingHomeo χ.Φ f ∧
  f '' X.P.Γ.U = Y.P.Γ.U ∧
  f '' X.P.Γ.V = Y.P.Γ.V ∧
  (∀ e ∈ X.P.Γ.E, Y.P.Γ.γ (f '' e) = (X.P.Γ.γ e).map f ∧ Y.P.φ (f '' e) = X.P.φ e) ∧
  ∃ g : Arm X.P.Γ → Arm Y.P.Γ,
    BijOn g X.L.arms Y.L.arms ∧
    ∀ A ∈ X.L.arms,
      (g A).minus.vertexSet = f '' A.minus.vertexSet ∧
      (g A).minus.edgeSet = (fun e => f '' e) '' A.minus.edgeSet ∧
      (g A).compl.vertexSet = f '' A.compl.vertexSet ∧
      (g A).compl.edgeSet = (fun e => f '' e) '' A.compl.edgeSet ∧
      (g A).π = A.π.map f

/-! ## Section 10: Tangle flaws -/

open Classical in
/-- A datum `(Γ, φ, λ, 𝒯) ∈ 𝒟` as in Section 10 (Graph Minors XIX, Section 10, page 353:
"Let $\mathscr{D}$ be the set of all quadruples $(\Gamma, \phi, \lambda, \mathscr{T})$ such
that $(\Gamma, \phi) \in \mathscr{S}$, $\lambda$ is a tie-breaker in $\Gamma$, and
$\mathscr{T}$ is a tangle in $\Gamma$"). -/
structure TangleDatum {Shat : Type u} [TopologicalSpace Shat]
    (cap : IsCappedSurface S Shat) (χ : ColourScheme S α) where
  /-- The `χ`-coloured painting `(Γ, φ)`. -/
  P : ColouredPainting χ
  /-- The radial drawing `Γ*` of `Γ` in `Σ̂_χ`. -/
  rad : RadialDrawing cap P.Γ
  /-- The tie-breaker `λ` in `Γ`. -/
  tb : TieBreaker rad
  /-- The order `ord(𝒯)` of the tangle `𝒯`. -/
  ord : ℕ
  /-- The set of separations in the tangle `𝒯`. -/
  𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))
  /-- `𝒯` is a tangle of order `ord` in `Γ.toHypergraph`. -/
  isTangle : GM10.IsTangle P.Γ.toHypergraph ord 𝒯

namespace TangleDatum

variable {Shat : Type u} [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

open Classical in
/-- The painting `Γ` of a `TangleDatum`. -/
def Γ (D : TangleDatum cap χ) : Painting S := D.P.Γ

open Classical in
/-- The representativeness `rep(𝒯)` of the tangle in `D`. -/
noncomputable def rep (D : TangleDatum cap χ) : ℕ :=
  tangleRep D.rad D.ord D.𝒯

open Classical in
/-- The metric `d` of `𝒯` on `A(Γ)`. -/
noncomputable def dist (D : TangleDatum cap χ) (a b : Set Shat) : ℕ :=
  tangleMetric D.rad D.ord D.𝒯 a b

open Classical in
/-- The metric `d(x, y)` between vertices of `Γ*`, each read as its atom. -/
noncomputable def vDist (D : TangleDatum cap χ) (x y : Shat) : ℕ :=
  D.dist (D.rad.atomOf x) (D.rad.atomOf y)

open Classical in
/-- The metric `d(e, x)` between an edge `e ∈ E(Γ)` and a vertex `x ∈ V(Γ*)`. -/
noncomputable def edgeVertDist (D : TangleDatum cap χ) (e : Set S) (x : Shat) : ℕ :=
  D.dist (cap.emb '' e) (D.rad.atomOf x)

open Classical in
/-- The metric `d(e₁, e₂)` between two edges `e₁, e₂ ∈ E(Γ)`. -/
noncomputable def edgeDist (D : TangleDatum cap χ) (e₁ e₂ : Set S) : ℕ :=
  D.dist (cap.emb '' e₁) (cap.emb '' e₂)

open Classical in
/-- The inside `ins(F)` of a circuit `F` of `Γ*` with respect to `𝒯`. -/
noncomputable def ins (D : TangleDatum cap χ) (F : Drawing Shat) : Set Shat :=
  if h : ∃ Δ : Set Shat, IsInsOf D.rad D.ord D.𝒯 F Δ then Classical.choose h else ∅

open Classical in
/-- A circuit `F` of `Γ*` is a *representativeness flaw* for `(Γ, φ, λ, 𝒯)` (Graph Minors XIX,
Section 10, page 353:
"Let $(\Gamma, \phi, \lambda, \mathscr{T}) \in \mathscr{D}$, such that
$rep(\Gamma), ord(\mathscr{T}) > rep(\mathscr{T})$. Then $\hat{\Sigma}_\chi$ is not a sphere, and
there is a circuit $F$ of $\Gamma^*$ with $\frac{1}{2}|E(F)| \le rep(\mathscr{T})$ such that
$\Sigma_1$ is not a disc, where $\Sigma_1, \Sigma_2$ are the closures of the two components of
$\hat{\Sigma}_\chi \setminus U(F)$ and $(\Gamma \cap \Sigma_1, \Gamma \cap \Sigma_2) \in
\mathscr{T}$. (It follows that $\frac{1}{2}|E(F)| = rep(\mathscr{T})$ for every such $F$.) Let us
choose such a circuit $F$ with $\lambda(F)$ minimal. We call $F$ a *representativeness flaw* for
$(\Gamma, \phi, \lambda, \mathscr{T})$"). -/
structure IsRepFlaw (D : TangleDatum cap χ) (F : Drawing Shat) : Prop where
  lt_rep_Γ : (D.rep : ℕ∞) < Painting.rep D.rad
  lt_ord_T : D.rep < D.ord
  not_sphere : ¬ IsSphere Shat
  is_circuit : F.IsCircuitOf D.rad.G
  card_le : F.E.ncard ≤ 2 * D.rep
  has_non_disc : ∃ S₁ S₂ : Set Shat, IsSidesOf F S₁ S₂ ∧ ¬ IsClosedDisc S₁ ∧
    (D.Γ.restrict (cap.emb ⁻¹' S₁), D.Γ.restrict (cap.emb ⁻¹' S₂)) ∈ D.𝒯
  minimal_weight : ∀ F' : Drawing Shat, F'.IsCircuitOf D.rad.G →
    F'.E.ncard ≤ 2 * D.rep →
    (∃ S₁' S₂' : Set Shat, IsSidesOf F' S₁' S₂' ∧ ¬ IsClosedDisc S₁' ∧
      (D.Γ.restrict (cap.emb ⁻¹' S₁'), D.Γ.restrict (cap.emb ⁻¹' S₂')) ∈ D.𝒯) →
    D.tb.weightSub F ≤ D.tb.weightSub F'

open Classical in
/-- A datum `(Γ, φ, λ, 𝒯) ∈ 𝒟` is *$n$-flawed in distance* (Graph Minors XIX, Section 10, page 355:
"More precisely, for $n \ge 1$ an integer, let us say that $(\Gamma, \phi, \lambda,
\mathscr{T}) \in \mathscr{D}$ is *$n$-flawed in distance* if $rep(\mathscr{T}) > n$, and
$dist(\Gamma) > \frac{1}{2}n + 1$, and there are distinct poles $r_1^*, r_2^*$ with
$d(r_1^*, r_2^*) \le n$"). -/
def IsFlawedInDistance (D : TangleDatum cap χ) (n : ℕ) : Prop :=
  n < D.rep ∧
  ((n + 2 : ℕ) : ℕ∞) < 2 * Painting.dist D.rad ∧
  ∃ r₁ ∈ D.rad.poles, ∃ r₂ ∈ D.rad.poles, r₁ ≠ r₂ ∧ D.vDist r₁ r₂ ≤ n

open Classical in
/-- A datum `(Γ, φ, λ, 𝒯) ∈ 𝒟` is *$n$-flawed in freedom* (Graph Minors XIX, Section 10, page 357:
"We say that $(\Gamma, \phi, \lambda, \mathscr{T}) \in \mathscr{D}$ is *$n$-flawed in
freedom* if $rep(\mathscr{T}) > n$, and $d(r^*_1, r^*_2) > n$ for every two distinct poles
$r^*_1, r^*_2$, and there is a circuit $F$ of $\Gamma^*$ with $\frac{1}{2}|E(F)| \le n$ such
that $ins(F)$ includes a long side of $\Phi_\chi$ or more than $\frac{1}{2}|E(F)|$ vertices
of $\Phi_\chi$"). -/
def IsFlawedInFreedom (D : TangleDatum cap χ) (n : ℕ) : Prop :=
  n < D.rep ∧
  (∀ r₁ ∈ D.rad.poles, ∀ r₂ ∈ D.rad.poles, r₁ ≠ r₂ → n < D.vDist r₁ r₂) ∧
  ∃ F : Drawing Shat, F.IsCircuitOf D.rad.G ∧ F.E.ncard ≤ 2 * n ∧
    ((∃ side ∈ χ.Φ.longSides, cap.emb '' side ⊆ D.ins F) ∨
      F.E.ncard < 2 * ((cap.emb '' χ.Φ.V) ∩ D.ins F).ncard)

/-! ## Section 11: Border label flaws -/

open Classical in
/-- A circuit `F` of `Γ*` is a *bite at `r*`* if `½|E(F)| < rep(𝒯)` and `r* ∈ V(F)` (Graph Minors
XIX, Section 11, page 357:
"By a *bite at $r^*$* we mean a circuit $F$ of $\Gamma^*$ with $\frac{1}{2}|E(F)| <
rep(\mathscr{T})$, such that $r^* \in V(F)$"). -/
structure IsBiteAt (D : TangleDatum cap χ) (rstar : Shat) (F : Drawing Shat) : Prop where
  pole_mem : rstar ∈ D.rad.poles
  is_circuit : F.IsCircuitOf D.rad.G
  card_lt : F.E.ncard < 2 * D.rep
  rstar_mem : rstar ∈ F.V

open Classical in
/-- The border distance `l(e₁, e₂)` between two edges `e₁, e₂ ∈ E(Γ)` bordering the same cuff
(Graph Minors XIX, Section 11, page 357:
"If $e_1, e_2$ are edges of $\Gamma$ bordering $\bar{r}\setminus r$, we define $l(e_1, e_2)$
to be the minimum of $\frac{1}{2}|E(F)|$ over all bites $F$ at $r^*$ with $e_1, e_2
\subseteq ins(F)$, if there is such a bite, and otherwise $l(e_1, e_2) = rep(\mathscr{T})$"). -/
noncomputable def borderEdgeDist (D : TangleDatum cap χ) (rstar : Shat) (e₁ e₂ : Set S) : ℕ :=
  if _h : ∃ F : Drawing Shat, D.IsBiteAt rstar F ∧
      cap.emb '' e₁ ⊆ D.ins F ∧ cap.emb '' e₂ ⊆ D.ins F then
    sInf {k : ℕ | ∃ F : Drawing Shat, D.IsBiteAt rstar F ∧
      cap.emb '' e₁ ⊆ D.ins F ∧ cap.emb '' e₂ ⊆ D.ins F ∧ F.E.ncard = 2 * k}
  else
    D.rep

open Classical in
/-- The edges `e₁, …, eₘ` lie on `side` in order: they are distinct, and each comes before the next
on the cuff `c`, reading `side` from its tail `u₀` to its head `u₁`. -/
def BordersInOrder (χ : ColourScheme S α) (Γ : Painting S) (side c : Set S) {m : ℕ}
    (e : Fin m → Set S) (u₀ u₁ : S) : Prop :=
  (χ.Φ.γ side).head? = some u₀ ∧ (χ.Φ.γ side).getLast? = some u₁ ∧ Function.Injective e ∧
    (∀ i : Fin m, e i ∈ Γ.E ∧ e i ⊆ side) ∧
    ∀ i j : Fin m, i < j → ∀ x ∈ e i, ∀ y ∈ e j, InOrderOn c u₀ x y u₁

open Classical in
/-- The last condition in the definition of "flawed on `S`": "there do not exist distinct edges
$e_1, \dots, e_m \in E(\Gamma)$ bordering $S$ in order,
such that $\phi(e_i) \ge \omega_i$ ($1 \le i \le m$), and $l(e_i, e_j) > n$ ($1 \le i < j
\le m$) and $l(e_i, s) > n$ ($1 \le i \le m$) for every short side $s$ bordering the same
cuff as $S$" (Graph Minors XIX, Section 11, page 358). -/
def NoSideMatch (D : TangleDatum cap χ) (side : Set S) (n : ℕ) (ω : List α) : Prop :=
  ∀ rstar ∈ D.rad.poles, ∀ c ∈ cuffs S, rstar ∈ cap.cuffDisc c → side ⊆ c →
    ¬ ∃ (e : Fin ω.length → Set S) (u₀ u₁ : S), BordersInOrder χ D.Γ side c e u₀ u₁ ∧
      (∀ (i : Fin ω.length), (χ.ΩS side).le (ω[i.val]) (D.P.φ (e i))) ∧
      (∀ i j : Fin ω.length, i < j → n < D.borderEdgeDist rstar (e i) (e j)) ∧
      (∀ i : Fin ω.length, ∀ s ∈ χ.Φ.shortSides, s ⊆ c → n < D.borderEdgeDist rstar (e i) s)

open Classical in
/-- A datum `(Γ, φ, λ, 𝒯) ∈ 𝒟` is *`(n, (ω₁, …, ωₘ))`-flawed on `S`* (Graph Minors XIX,
Section 11, pages 357–358:
"Let $S$ be a long side of $\Phi_\chi$, let $m \ge 1$, let $\omega_1, \dots, \omega_m$ be a
sequence of elements of $\Omega_\chi(S)$, and let $n \ge 4$. We say that $(\Gamma, \phi,
\lambda, \mathscr{T}) \in \mathscr{D}$ is $(n, (\omega_1, \dots, \omega_m))$-*flawed on $S$*
if - $rep(\mathscr{T}) \ge 2(m + 1)n + 8$, and $dist(\Gamma) \ge \frac{1}{2}(m + 1)n + 1$, -
$(\Gamma, \phi, \lambda, \mathscr{T})$ is not $(m + 1)n$-flawed in distance, - $(\Gamma,
\phi, \lambda, \mathscr{T})$ is not $(m + 1)n$-flawed in freedom, and ... - there do not exist
distinct edges $e_1, \dots, e_m \in E(\Gamma)$ bordering $S$ in order, such that $\phi(e_i)
\ge \omega_i$ ($1 \le i \le m$), and $l(e_i, e_j) > n$ ($1 \le i < j \le m$) and $l(e_i, s)
> n$ ($1 \le i \le m$) for every short side $s$ bordering the same cuff as $S$"). The bound on
> `dist(Γ)` is strict here.
With equality, "not `(m + 1)n`-flawed in distance" says nothing, since being flawed asks for
`dist(Γ) > ½(m + 1)n + 1`, while the proof of (11.2) needs that poles are far apart. The proof of
(4.1) has the strict bound. -/
def IsFlawedOnSide (D : TangleDatum cap χ) (side : Set S) (n : ℕ)
    (ω : List α) : Prop :=
  let m := ω.length
  2 * (m + 1) * n + 8 ≤ D.rep ∧
  (((m + 1) * n + 2 : ℕ) : ℕ∞) < 2 * Painting.dist D.rad ∧
  ¬ D.IsFlawedInDistance ((m + 1) * n) ∧
  ¬ D.IsFlawedInFreedom ((m + 1) * n) ∧
  D.NoSideMatch side n ω

open Classical in
/-- `I` is an arc in `ins(F) ∩ (rBar \ r)` joining the two neighbours in `F` of `r*`. When the
circuit
`F` has length two the two neighbours coincide, and the arc is that one vertex. -/
def IsBiteArc (D : TangleDatum cap χ) (rstar : Shat) (F : Drawing Shat) (I : Set Shat) : Prop :=
  I ⊆ D.ins F ∩ (closure (D.rad.regionOf rstar) \ D.rad.regionOf rstar) ∧
    ∃ u v : Shat, {x | ∃ e ∈ F.E, closure e ∩ F.V = {rstar, x}} = {u, v} ∧
      ((u = v ∧ I = {u}) ∨ (u ≠ v ∧ IsLineWithEnds I u v))

open Classical in
/-- The I-arc `I(F) ⊆ ins(F) ∩ (rBar \ r)` of a bite `F` at `r*` joining the two neighbours in `F`
of
`r*` (Graph Minors XIX, Section 11, page 358:
"If $F$ is a bite at $r^*$, we define $I(F)$ to be the I-arc in $ins(F) \cap (\bar{r}
\setminus r)$ joining the two neighbours in $F$ of $r"). The two arcs of the cuff between these
neighbours lie on different
sides of `F`, so this arc is unique, and the union below is that arc. -/
def biteArc (D : TangleDatum cap χ) (rstar : Shat) (F : Drawing Shat) : Set Shat :=
  ⋃₀ {I | D.IsBiteArc rstar F I}

open Classical in
/-- The union `I(ℱ) = ⋃ (I(F) : F ∈ ℱ)` of the bite arcs of a set `ℱ` of bites (Graph Minors XIX,
Section 11, page 358:
"If $\mathscr{F}$ is a set of bites at $r^*$, we define $I(\mathscr{F}) = \bigcup(I(F) : F
\in \mathscr{F})$"). -/
def feastArcUnion (D : TangleDatum cap χ) (rstar : Shat) (ℱ : Set (Drawing Shat)) : Set Shat :=
  ⋃ F ∈ ℱ, D.biteArc rstar F

open Classical in
/-- The order `∑ (½|E(F)| : F ∈ ℱ)` of a finite set `ℱ` of bites at `r*` (Graph Minors XIX,
Section 11, page 358:
"The order of a set $\mathscr{F}$ of bites at $r^*$ is $\Sigma(\frac{1}{2}|E(F)| : F \in
\mathscr{F})$"). -/
noncomputable def feastOrder (ℱ : Set (Drawing Shat)) : ℕ :=
  if h : ℱ.Finite then ∑ F ∈ h.toFinset, F.E.ncard / 2 else 0

open Classical in
/-- A set `ℱ` of bites at `r*` is a *feast* for `(S, (ω₁, …, ωₘ))` (Graph Minors XIX, Section 11,
page 358:
"A set $\mathscr{F}$ of bites at $r^*$ is a *feast* if
- $|\mathscr{F}| \le m + 1$,
- $I(\mathscr{F})$ includes the short sides of $\Phi_\chi$ with an end in common with $S$, and
- for each component $X$ of $S \setminus I(\mathscr{F})$ there exists $h$ with $1 \le h \le m$ such
  that $\phi(e) \not\ge \omega_h$ for all $e \in E(\Gamma)$ with $e \subseteq X$"). -/
structure IsFeast (D : TangleDatum cap χ) (rstar : Shat) (side : Set S)
    (ω : List α) (ℱ : Set (Drawing Shat)) : Prop where
  finite_bites : ℱ.Finite
  all_bites : ∀ F ∈ ℱ, D.IsBiteAt rstar F
  card_le : ℱ.ncard ≤ ω.length + 1
  includes_short_sides : ∀ s ∈ χ.Φ.shortSides, (closure s ∩ closure side).Nonempty →
    cap.emb '' s ⊆ D.feastArcUnion rstar ℱ
  component_omits : ∀ X ∈ componentsIn (side \ cap.emb ⁻¹' D.feastArcUnion rstar ℱ),
    ∃ (h : ℕ) (hh : h < ω.length), ∀ e ∈ D.Γ.E, e ⊆ X → ¬ (χ.ΩS side).le (ω[h]) (D.P.φ e)

open Classical in
/-- A feast `ℱ` is *disjoint* (Graph Minors XIX, Section 11, page 360:
"A feast $\mathscr{F}$ is *disjoint* if $I(F) = ins(F) \cap (\bar{r} \setminus r)$ for each
$F \in \mathscr{F}$, and $ins(F) \cap ins(F') = \{r^*\}$ for all distinct $F, F' \in
\mathscr{F}$"). -/
structure IsDisjointFeast (D : TangleDatum cap χ) (rstar : Shat) (side : Set S)
    (ω : List α) (ℱ : Set (Drawing Shat)) : Prop extends
    D.IsFeast rstar side ω ℱ where
  arc_eq : ∀ F ∈ ℱ, D.biteArc rstar F =
    D.ins F ∩ (closure (D.rad.regionOf rstar) \ D.rad.regionOf rstar)
  ins_inter : ∀ F ∈ ℱ, ∀ F' ∈ ℱ, F ≠ F' → D.ins F ∩ D.ins F' = {rstar}

open Classical in
/-- A disjoint feast `ℱ` of order `≤ (m + 1)n` whose members are `λ`-linked to `𝒯` is an
*`((ω₁, …, ωₘ), S)`-flaw* for `(Γ, φ, λ, 𝒯)` (Graph Minors XIX, Section 11, page 361:
"If $(\Gamma, \phi, \lambda, \mathcal{T}) \in \mathcal{D}$ is $(n, (\omega_1, \ldots,
\omega_m))$-flawed on $S$, it follows from 11.2, 11.3, 11.4 that there is a disjoint feast
$\mathcal{F}$ of order $\le (m+1)n$, such that each of its members is $\lambda$-linked to
$\mathcal{T}$. We call $\mathcal{F}$ an $((\omega_1, \ldots, \omega_m), S)$-flaw for
$(\Gamma, \phi, \lambda, \mathcal{T})$"). -/
structure IsSideLabelFlaw (D : TangleDatum cap χ) (rstar : Shat) (side : Set S) (n : ℕ)
    (ω : List α) (ℱ : Set (Drawing Shat)) : Prop extends
    D.IsDisjointFeast rstar side ω ℱ where
  order_le : feastOrder ℱ ≤ (ω.length + 1) * n
  all_linked : ∀ F ∈ ℱ, IsLambdaLinkedCircuit D.tb D.ord D.𝒯 F

/-! ## Section 12: Internal label flaws and wheels -/

open Classical in
/-- `x ≤ y` in `Ω_χ(k)`, for `k = 2, 3`. -/
def sizeLE (χ : ColourScheme S α) (k : ℕ) (x y : α) : Prop :=
  (k = 2 ∧ χ.Ω2.le x y) ∨ (k = 3 ∧ χ.Ω3.le x y)

open Classical in
/-- The last condition in the definition of "flawed internally": there do not exist edges
`e₁, …, eₘ` of `Γ` such that `φ(eᵢ) ≥ ω₀`, `d(eᵢ, eⱼ) > n` and `d(eᵢ, r*) > n` for every pole `r*`.
The paper's `ω₀` lies in `Ω_χ(k)`, for `k = 2` or `3`, in a disjoint colour scheme. So the edges
`eᵢ` are internal of size `k`, and we say so, since we allow a colour scheme that is not disjoint.
-/
def NoInternalMatch (D : TangleDatum cap χ) (m n k : ℕ) (ω₀ : α) : Prop :=
  ¬ ∃ e : Fin m → Set S,
    (∀ i : Fin m, e i ∈ D.Γ.E ∧ Painting.IsInternal (e i) ∧ (tilde (e i)).ncard = k ∧
      sizeLE χ k ω₀ (D.P.φ (e i))) ∧
    (∀ i j : Fin m, i < j → n < D.edgeDist (e i) (e j)) ∧
    (∀ i : Fin m, ∀ rstar ∈ D.rad.poles, n < D.edgeVertDist (e i) rstar)

open Classical in
/-- A datum `(Γ, φ, λ, 𝒯) ∈ 𝒟` is *`(m, n, ω₀)`-flawed internally* (Graph Minors XIX, Section 12,
page 362:
"Let $\chi, \mathcal{S}, \mathcal{D}$ be as in Section 10, let $\omega_0 \in
E(\Omega_\chi(2)) \cup E(\Omega_\chi(3))$, and let $m \ge 1, n \ge 4$. We say that $(\Gamma,
\phi, \lambda, \mathcal{T}) \in \mathcal{D}$ is $(m, n, \omega_0)$-flawed internally if *
$rep(\mathcal{T}) \ge 5^{2m+2}n$, and $dist(\Gamma) \ge \frac{1}{2} 5^{2m+2}n + 1$, *
$(\Gamma, \phi, \lambda, \mathcal{T})$ is not $5^{2m+2}n$-flawed in distance, * there do not
exist edges $e_1, \ldots, e_m$ of $\Gamma$ such that $\phi(e_i) \ge \omega_0$ $(1 \le i \le
m)$, $d(e_i, e_j) > n$ $(1 \le i < j \le m)$, and $d(e_i, r^*) > n$ $(1 \le i \le m)$ for
every pole $r^*$, where $d$ is the metric of $\mathcal{T}$"). Here `k` is `2` or `3`, and `ω₀ ∈
E(Ω_χ(k))`. The first bullet is strict
here. With equality, "not `5^{2m+2}n`-flawed in distance" says nothing, since being flawed asks
for `rep(𝒯) > n` and `dist(Γ) > ½n + 1`, while the proof of (12.3) needs that poles are far apart.
The proof of (4.1) has the strict inequalities. -/
def IsFlawedInternally (D : TangleDatum cap χ) (m n : ℕ) (k : ℕ) (ω₀ : α) : Prop :=
  5 ^ (2 * m + 2) * n < D.rep ∧
  ((5 ^ (2 * m + 2) * n + 2 : ℕ) : ℕ∞) < 2 * Painting.dist D.rad ∧
  ¬ D.IsFlawedInDistance (5 ^ (2 * m + 2) * n) ∧
  D.NoInternalMatch m n k ω₀

open Classical in
/-- A closed disc `W ⊆ Σ̂` is a *wheel* and a subdrawing `H ⊆ Γ*` is a *`W`-hub of radius `ρ`*
(Graph Minors XIX, Section 12, page 362:
"Let $W \subseteq \hat{\Sigma}$ be a closed disc with $bd(W) \subseteq U(\Gamma^*)$, let $H$ be a
subdrawing of $\Gamma^*$ with $U(H) \subseteq W \setminus bd(W)$, and let $\rho \ge 1$ be an
integer with $rep(\mathcal{T}) \ge 2\rho + 3$. We say that $W$ is a *wheel*, and $H$ is a *$W$-hub
of radius $\rho$*, if:
* $W$ includes $ins(F)$ for every circuit $F$ of $\Gamma^*$ with $|E(F)| \le 4\rho + 4$ and
  $U(F) \subseteq W$,
* $W$ contains every vertex of $\Gamma^*$ adjacent in $\Gamma^*$ to two members of
  $V(\Gamma) \cap bd(W)$, and $W$ includes every edge of $\Gamma^*$ with both ends in $bd(W)$,
* either $|V(H)| = 1$ or $H$ is a $\mathcal{T}$-enclave with $|E(H)| \le 4\rho + 4$; if
  $|V(H)| = 1$, then there is no $\mathcal{T}$-enclave $H'$ with $|E(H')| \le 4\rho + 4$ and
  $V(H) \subseteq ins(H') \setminus U(H')$; and if $H$ is a $\mathcal{T}$-enclave, then there is no
  $\mathcal{T}$-enclave $H' \ne H$ with $|E(H')| \le 4\rho + 4$ and $U(H) \subseteq ins(H')$,
* $W$ contains every vertex of $\Gamma$ joined to $V(H)$ by a path in $\Gamma^*$ of $\le \rho$
  edges, and
* for every $v \in V(\Gamma) \cap bd(W)$ there is a path of $\Gamma^*$ from $v$ to $V(H)$ with
  $\le \rho$ edges, and no such path with $\le \rho - 2$ edges"). -/
structure IsWheelHubOfRadius (D : TangleDatum cap χ) (W : Set Shat) (H : Drawing Shat)
    (ρ : ℕ) : Prop where
  pos_ρ : 1 ≤ ρ
  rep_ge : 2 * ρ + 3 ≤ D.rep
  is_disc : IsClosedDisc W
  bd_sub : discBd W ⊆ D.rad.G.U
  H_sub : H.IsSubdrawing D.rad.G
  H_in_int : H.U ⊆ W \ discBd W
  ins_sub : ∀ F : Drawing Shat, F.IsCircuitOf D.rad.G → F.E.ncard ≤ 4 * ρ + 4 →
    F.U ⊆ W → D.ins F ⊆ W
  two_nbrs_in_W : ∀ x ∈ D.rad.G.V,
    ∀ v₁ ∈ (cap.emb '' D.Γ.V) ∩ discBd W, ∀ v₂ ∈ (cap.emb '' D.Γ.V) ∩ discBd W,
    v₁ ≠ v₂ →
    (∃ e₁ ∈ D.rad.G.E, tilde e₁ = {x, v₁}) →
    (∃ e₂ ∈ D.rad.G.E, tilde e₂ = {x, v₂}) →
    x ∈ W
  chord_in_W : ∀ e ∈ D.rad.G.E, tilde e ⊆ discBd W → e ⊆ W
  hub_cond :
    ((H.V.ncard = 1 ∧ H.E = ∅ ∧
      ∀ H' : Drawing Shat, IsEnclave D.tb D.ord D.𝒯 H' → H'.E.ncard ≤ 4 * ρ + 4 →
        ¬ (H.V ⊆ D.ins H' \ H'.U)) ∨
    (IsEnclave D.tb D.ord D.𝒯 H ∧ H.E.ncard ≤ 4 * ρ + 4 ∧
      ∀ H' : Drawing Shat, IsEnclave D.tb D.ord D.𝒯 H' → H' ≠ H → H'.E.ncard ≤ 4 * ρ + 4 →
        ¬ (H.U ⊆ D.ins H')))
  close_in_W : ∀ v ∈ cap.emb '' D.Γ.V,
    (∃ P : Drawing Shat, ∃ h ∈ H.V, P.IsPathOf D.rad.G v h ∧ P.E.ncard ≤ ρ) → v ∈ W
  bd_dist : ∀ v ∈ (cap.emb '' D.Γ.V) ∩ discBd W,
    (∃ P : Drawing Shat, ∃ h ∈ H.V, P.IsPathOf D.rad.G v h ∧ P.E.ncard ≤ ρ) ∧
    ¬ (∃ P : Drawing Shat, ∃ h ∈ H.V, P.IsPathOf D.rad.G v h ∧ P.E.ncard + 2 ≤ ρ)

open Classical in
/-- A closed disc `W ⊆ Σ̂` is a *wheel* if there exist a `W`-hub `H` and radius `ρ` (Graph Minors
XIX, Section 12, page 362). -/
def IsWheel (D : TangleDatum cap χ) (W : Set Shat) : Prop :=
  ∃ (H : Drawing Shat) (ρ : ℕ), D.IsWheelHubOfRadius W H ρ

open Classical in
/-- The *radius* of a wheel `W` is the minimum radius of all `W`-hubs (Graph Minors XIX,
Section 12, page 362:
"The *radius* of a wheel $W$ is the minimum radius of all $W$-hubs"). -/
noncomputable def wheelRadius (D : TangleDatum cap χ) (W : Set Shat) : ℕ :=
  sInf {ρ : ℕ | ∃ H : Drawing Shat, D.IsWheelHubOfRadius W H ρ}

open Classical in
/-- A set `𝒲` of wheels is a *cover* for `(Γ, φ, λ, 𝒯)` with respect to `ω₀` (Graph Minors XIX,
Section 12, page 364:
"A set $\mathcal{W}$ of wheels is a *cover* (for $(\Gamma, \phi, \lambda, \mathcal{T})$) if *
the members of $\mathcal{W}$ are mutually disjoint, * $bd(W) \subseteq \Sigma_\chi \setminus
bd(\Sigma_\chi)$ for each $W \in \mathcal{W}$, * for each pole $r^*$ there exists $W \in
\mathcal{W}$ with $r^* \in W$ and hence with $r \subseteq W$, * for every $e \in Z$ there
exists $W \in \mathcal{W}$ with $e \subseteq W$, * for each $W \in \mathcal{W}$, $(W
\setminus bd(W)) \cap V(\Gamma) \ne \emptyset$"). -/
structure IsWheelCover (D : TangleDatum cap χ) (ω₀ : α)
    (𝒲 : Set (Set Shat)) : Prop where
  finite_wheels : 𝒲.Finite
  all_wheels : ∀ W ∈ 𝒲, D.IsWheel W
  pairwise_disjoint : 𝒲.PairwiseDisjoint id
  bd_in_interior : ∀ W ∈ 𝒲, discBd W ⊆ cap.emb '' (univ \ bd S)
  poles_covered : ∀ rstar ∈ D.rad.poles, ∃ W ∈ 𝒲, rstar ∈ W
  Z_covered : ∀ e ∈ D.Γ.E, χ.unionLE ω₀ (D.P.φ e) →
    ∃ W ∈ 𝒲, cap.emb '' e ⊆ W
  interior_vertex : ∀ W ∈ 𝒲, ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty

/-! ## Section 13: Spokes of a wheel and optimal hubs -/

open Classical in
/-- A path `P` of `Γ*` is a *spoke* of `(W, H)` from `v ∈ V(Γ) ∩ bd(W)` to `h ∈ V(H)` (Graph
Minors XIX, Section 13, page 366:
"By a *spoke* of $W$ we mean a path $P$ of $\Gamma^*$ from some $v \in V(\Gamma) \cap bd(W)$
to some $h \in V(H)$, such that • there is no path of $\Gamma^*$ from $v$ to $V(H)$ with
fewer than $|E(P)|$ edges, and • there is no path $P'$ of $\Gamma^*$ from $v$ to $V(H)$ with
$|E(P)|$ edges and with $\lambda(P') < \lambda(P)$"). -/
structure IsSpoke (D : TangleDatum cap χ) (W : Set Shat) (H : Drawing Shat)
    (v h : Shat) (P : Drawing Shat) : Prop where
  v_mem : v ∈ (cap.emb '' D.Γ.V) ∩ discBd W
  h_mem : h ∈ H.V
  is_path : P.IsPathOf D.rad.G v h
  min_length : ∀ (P' : Drawing Shat), ∀ h' ∈ H.V, P'.IsPathOf D.rad.G v h' →
    P.E.ncard ≤ P'.E.ncard
  min_weight : ∀ (P' : Drawing Shat), ∀ h' ∈ H.V, P'.IsPathOf D.rad.G v h' →
    P'.E.ncard = P.E.ncard → D.tb.weightSub P ≤ D.tb.weightSub P'

open Classical in
/-- A `W`-hub `H` is *optimal* (Graph Minors XIX, Section 13, page 367:
"A $W$-hub $H$ is said to be *optimal* if • $H$ has the same radius as $W$, that is, $H$ has
radius minimum over all $W$-hubs, and • either $|V(H)| = 1$, or there is no 1-vertex $W$-hub
with the same radius as $W$"). -/
structure IsOptimalWheelHub (D : TangleDatum cap χ) (W : Set Shat) (H : Drawing Shat)
    (ρ : ℕ) : Prop extends D.IsWheelHubOfRadius W H ρ where
  ρ_eq_radius : ρ = D.wheelRadius W
  one_vertex_priority : H.V.ncard = 1 ∨
    ¬ ∃ H' : Drawing Shat, D.IsWheelHubOfRadius W H' ρ ∧ H'.V.ncard = 1

open Classical in
/-- The boundary sector disc `Δ_v ⊆ W` and circuit `D_v` for `v ∈ R* ∩ bd(W)` (Graph Minors XIX,
Section 13, page 368:
"Let $v \in R^* \cap bd(W)$, with neighbours $v_1, v_2$ in $\Gamma^* \cap bd(W)$. Let $f_i$
be the edge of $\Gamma^* \cap bd(W)$ with ends $v, v_i$ ($i = 1, 2$). If $S_{v_1}$ meets
$S_{v_2}$ we define $\Delta_v$ to be the disc in $W$ bounded by the closure of $$(U(S_{v_1}
\cup S_{v_2}) \setminus U(S_{v_1} \cap S_{v_2})) \cup f_1 \cup f_2.$$ If $S_{v_1}$ does not
meet $S_{v_2}$, let their inner ends be $h_1, h_2$ respectively, let $P$ be the path of $H$
joining $h_1, h_2$ such that the disc in $W$ bounded by $$U(S_{v_1} \cup S_{v_2} \cup P)
\cup \bar{f}_1 \cup \bar{f}_2$$ does not include $ins(H)$, and let $\Delta_v$ be this disc.
In either case, let $D_v$ be the circuit of $\Gamma^*$ with $U(D_v) = bd(\Delta_v)$"). -/
structure IsBoundarySector (D : TangleDatum cap χ) (W : Set Shat) (H : Drawing Shat)
    (rstar : Shat) (Δv : Set Shat) (Dv : Drawing Shat) : Prop where
  rstar_mem : rstar ∈ D.rad.Rstar ∩ discBd W
  Δv_sub : Δv ⊆ W
  is_disc : IsClosedDisc Δv
  Dv_circuit : Dv.IsCircuitOf D.rad.G
  Dv_U : Dv.U = discBd Δv
  sector_spec : ∃ (v₁ v₂ h₁ h₂ : Shat) (f₁ f₂ : Set Shat) (S₁ S₂ : Drawing Shat),
    v₁ ≠ v₂ ∧
    f₁ ∈ D.rad.G.E ∧ f₁ ⊆ discBd W ∧ tilde f₁ = {rstar, v₁} ∧
    f₂ ∈ D.rad.G.E ∧ f₂ ⊆ discBd W ∧ tilde f₂ = {rstar, v₂} ∧
    D.IsSpoke W H v₁ h₁ S₁ ∧ D.IsSpoke W H v₂ h₂ S₂ ∧
    (((S₁.V ∩ S₂.V).Nonempty ∧
      discBd Δv = closure (((S₁.U ∪ S₂.U) \ (S₁.U ∩ S₂.U)) ∪ f₁ ∪ f₂)) ∨
    (Disjoint S₁.V S₂.V ∧ ∃ P : Drawing Shat, P.IsPathOf H h₁ h₂ ∧
      discBd Δv = S₁.U ∪ S₂.U ∪ P.U ∪ closure f₁ ∪ closure f₂ ∧
      ¬ (D.ins H ⊆ Δv)))

/-! ## Section 14: Removing wheel covers -/

open Classical in
/-- A region vertex `r* ∈ R* ∩ bd(W)` is *singular* (and *regular* otherwise) with respect to an
optimal `W`-hub `H` (Graph Minors XIX, Section 14, page 375:
"If $|V(H(W))| = 1$, designate some vertex of $R^* \cap bd(W)$ as *singular*, and the other
vertices of $R^* \cap bd(W)$ as *regular*. If $|V(H(W))| > 1$, we say $r^* \in R^* \cap
bd(W)$ is *singular* if $S_{v_1}, S_{v_2}$ have distinct inner ends, where $v_1, v_2$ are
the neighbours of $r^*$ in $\Gamma^* \cap bd(W)$, and $S_{v_1}, S_{v_2}$ are the
corresponding spokes; and $r^*$ is *regular* otherwise"). -/
def IsSingularBoundaryRegion (D : TangleDatum cap χ) (W : Set Shat) (H : Drawing Shat)
    (rstar₀ rstar : Shat) : Prop :=
  rstar ∈ D.rad.Rstar ∩ discBd W ∧
  ((H.V.ncard = 1 ∧ rstar = rstar₀) ∨
   (1 < H.V.ncard ∧ ∃ (v₁ v₂ h₁ h₂ : Shat) (f₁ f₂ : Set Shat) (S₁ S₂ : Drawing Shat),
      v₁ ≠ v₂ ∧ h₁ ≠ h₂ ∧
      f₁ ∈ D.rad.G.E ∧ f₁ ⊆ discBd W ∧ tilde f₁ = {rstar, v₁} ∧
      f₂ ∈ D.rad.G.E ∧ f₂ ⊆ discBd W ∧ tilde f₂ = {rstar, v₂} ∧
      D.IsSpoke W H v₁ h₁ S₁ ∧ D.IsSpoke W H v₂ h₂ S₂))

end TangleDatum

end GraphMinor.GM19
