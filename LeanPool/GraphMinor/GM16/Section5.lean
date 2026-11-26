/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4
import LeanPool.GraphMinor.GM16.Metric

import LeanPool.GraphMinor.GM12.Bridge

/-!
# Graph Minors XVI, Section 5: Induction on Horns

This file formalizes Section 5 ("Induction on horns", pages 54–58) of
N. Robertson and P. D. Seymour, *Graph Minors. XVI. Excluding a non-planar graph*, J. Combin.
Theory Ser. B 89 (2003) 43–76:

- Statements of **Graph Minors XVI, (5.1)** (`GM16Theorem51Statement`, page 55),
  **(5.2)** (`GM16Theorem52Statement`, page 55),
  **(5.3)** (`GM16Theorem53Statement`, page 56),
  **(5.4)** (`GM16Theorem54Statement`, page 56), and
  **(5.5)** (`GM16Theorem55Statement`, page 57).
- Proof of **Graph Minors XVI, (5.2)** (`theorem_5_2`, page 55), deduced from
  `GM12Theorem44Statement` and `controlsMinor_of_gm12`.
- Monotonicity lemmas for horns and animals (`IsHorn.mono`, `IsAnimal.mono`, `HasAnimal.mono`,
  `HasHairlessAnimal.mono`) and existence of a hairless animal with `0` horns from a `Σ`-span
  (`hasHairlessAnimal_zero_of_isSigmaSpan`).
- Proof of **Graph Minors XVI, (4.1)** (`theorem_4_1`, page 58) from `(5.1)` and `(5.5)` by
  induction on the number of horns `0 ≤ i ≤ μ = p * (p - 1) / 2`.
The backward and tower inductions are proved in `InductionsProved.lean`.
-/

@[expose] public section

namespace GraphMinor.GM16

open Set Function Topology
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14 GraphMinor.GM15

universe u v w

variable {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}

/-! ## Monotonicity of Horns and Animals -/

omit [T2Space S] in
/-- Monotonicity of `IsHorn`: a horn of cardinality `σ₁` and breadth `≥ θ₁` restricts to a horn of
cardinality `σ₂ ≤ σ₁` and breadth `≥ θ₂ ≤ θ₁`. -/
theorem IsHorn.mono {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {d : Set S → Set S → ℕ} {v : α} {θ₁ σ₁ θ₂ σ₂ : ℕ}
    {P : Fin σ₁ → Graph α β} {u : Fin σ₁ → S}
    (h : IsHorn G H η d v θ₁ σ₁ P u) (hθ : θ₂ ≤ θ₁) (hσ : σ₂ ≤ σ₁) :
    IsHorn G H η d v θ₂ σ₂ (fun i => P ⟨i.1, by omega⟩) (fun i => u ⟨i.1, by omega⟩) := by
  rcases h with ⟨hv, hu, hP, hinter_H, hinter_P, hdist⟩
  refine ⟨hv, fun i => hu ⟨i.1, by omega⟩, fun i => hP ⟨i.1, by omega⟩,
    fun i => hinter_H ⟨i.1, by omega⟩, ?_, ?_⟩
  · intro i j hij
    exact hinter_P ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ (fun h_eq => hij (Fin.ext (Fin.mk.inj h_eq)))
  · intro i j hij
    exact hθ.trans (hdist ⟨i.1, by omega⟩ ⟨j.1, by omega⟩
      (fun h_eq => hij (Fin.ext (Fin.mk.inj h_eq))))

/-- Monotonicity of `IsAnimal` in strength `(θ, σ)`: an animal of strength `≥ (θ₁, σ₁)` has
strength `≥ (θ₂, σ₂)` whenever `1 ≤ θ₂ ≤ θ₁` and `σ₂ ≤ σ₁`. -/
theorem IsAnimal.mono {G : Graph α β}
    {T_star : Set (Hypergraph α β × Hypergraph α β)} {θ_star : ℕ}
    {H : Drawing S} {η : SpanEmbedding H G} {θ_span : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {X : Set α} {Y : Set S}
    {χ δ θ₁ σ₁ θ₂ σ₂ : ℕ}
    (h : IsAnimal G T_star θ_star H η θ_span T d X Y χ δ θ₁ σ₁)
    (hθ₂_pos : 1 ≤ θ₂) (hθ : θ₂ ≤ θ₁) (hσ : σ₂ ≤ σ₁) :
    IsAnimal G T_star θ_star H η θ_span T d X Y χ δ θ₂ σ₂ := by
  rcases h with ⟨_, hθ₁_span, hSpan, hMet, hX_sub, hX_card, hY_sub, hY_card, hHorns, hHairs,
    hY_dist⟩
  refine ⟨hθ₂_pos, hθ.trans hθ₁_span, hSpan, hMet, hX_sub, hX_card, hY_sub, hY_card, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨P, u, hHorn⟩ := hHorns v hv
    exact ⟨_, _, hHorn.mono hθ hσ⟩
  · intro u hu
    obtain ⟨v, P, hv, huv, hP, hdisj, hd⟩ := hHairs u hu
    exact ⟨v, P, hv, huv, hP, hdisj, hθ.trans hd⟩
  · intro u₁ hu₁ u₂ hu₂ hne
    exact hθ.trans (hY_dist u₁ hu₁ u₂ hu₂ hne)

/-- Monotonicity of `HasAnimal` in strength `(θ, σ)`. -/
theorem HasAnimal.mono {G : Graph α β}
    {T_star : Set (Hypergraph α β × Hypergraph α β)} {θ_star : ℕ}
    {χ δ θ₁ σ₁ θ₂ σ₂ : ℕ}
    (h : HasAnimal S G T_star θ_star χ δ θ₁ σ₁)
    (hθ₂_pos : 1 ≤ θ₂) (hθ : θ₂ ≤ θ₁) (hσ : σ₂ ≤ σ₁) :
    HasAnimal S G T_star θ_star χ δ θ₂ σ₂ := by
  obtain ⟨H, η, θ_span, T, d, X, Y, hAnim⟩ := h
  exact ⟨H, η, θ_span, T, d, X, Y, hAnim.mono hθ₂_pos hθ hσ⟩

/-- Monotonicity of `HasHairlessAnimal` in strength `(θ, σ)`. -/
theorem HasHairlessAnimal.mono {G : Graph α β}
    {T_star : Set (Hypergraph α β × Hypergraph α β)} {θ_star : ℕ}
    {χ θ₁ σ₁ θ₂ σ₂ : ℕ}
    (h : HasHairlessAnimal S G T_star θ_star χ θ₁ σ₁)
    (hθ₂_pos : 1 ≤ θ₂) (hθ : θ₂ ≤ θ₁) (hσ : σ₂ ≤ σ₁) :
    HasHairlessAnimal S G T_star θ_star χ θ₂ σ₂ :=
  HasAnimal.mono h hθ₂_pos hθ hσ

/-- Any `Σ`-span `(H, η, T)` of order `θ_span ≥ θ ≥ 1` with metric `d` yields a hairless animal
with `0` horns and strength `≥ (θ, σ)` for every `σ ≥ 0` (Graph Minors XVI, Section 5, page 58). -/
theorem hasHairlessAnimal_zero_of_isSigmaSpan {G : Graph α β}
    {T_star : Set (Hypergraph α β × Hypergraph α β)} {θ_star θ_span θ σ : ℕ}
    {H : Drawing S} {η : SpanEmbedding H G}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hθ_pos : 1 ≤ θ) (hθ_le : θ ≤ θ_span)
    (hSpan : IsSigmaSpan G H η θ_star θ_span T_star T)
    (hMet : HasTangleMetric H θ_span T d) :
    HasHairlessAnimal S G T_star θ_star 0 θ σ := by
  refine ⟨H, η, θ_span, T, d, ∅, ∅, hθ_pos, hθ_le, hSpan, hMet,
    empty_subset _, ncard_empty α, empty_subset _, ncard_empty S, ?_, ?_, ?_⟩
  · intro _ hv; exact False.elim hv
  · intro _ hu; exact False.elim hu
  · intro _ hu₁; exact False.elim hu₁

/-! ## Statements of (5.1), (5.2), (5.3), (5.4), and (5.5) (pages 55–57) -/

/-- Statement of Graph Minors XVI, (5.1) (page 55):
"Let $\Sigma$ be a surface and let $p, \tau, \chi \ge 0$ and $\phi, \psi \ge 1$. Then there exist
$\sigma, \kappa, \rho, \zeta \ge 0$ and $\theta \ge 1$ such that if $\mathscr{T}^*$ is a tangle in a
graph $G$, and there is a hairless animal with $\chi$ horns, of strength $\ge (\theta, \sigma)$,
then either:
1. there is a $\Sigma'$-span of order $\ge \phi$, for some surface $\Sigma'$ obtained from $\Sigma$
   by adding a handle or a crosscap, or
2. there is a hairless animal with $\chi + 1$ horns, of strength $\ge (\psi, \tau)$, or
3. there exists $Z \subseteq V(G)$ with $|Z| \le \zeta$, and a $\mathscr{T}^* \setminus Z$-central
   segregation of $G \setminus Z$ of type $(\rho, \kappa)$ with a proper arrangement in $\Sigma$, or
4. $\mathscr{T}^*$ controls a $K_p$-minor of $G$." -/
def GM16Theorem51Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ p τ χ φ ψ : ℕ, 1 ≤ φ → 1 ≤ ψ →
      ∃ σ κ ρ ζ θ : ℕ, 1 ≤ θ ∧
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (hT : IsGraphTangle G θ_star T_star),
          HasHairlessAnimal S G T_star θ_star χ θ σ →
          (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S')
            (H' : Drawing S') (η' : SpanEmbedding H' G) (θ_span' : ℕ)
            (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
            IsClosedSurface S' ∧ ConnectedSpace S' ∧
            IsObtainedByAddingHandleOrCrosscap S S' ∧
            φ ≤ θ_span' ∧ IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨
          HasHairlessAnimal S G T_star θ_star (χ + 1) ψ τ ∨
          (∃ (Z : Set α) (S_seg : Set (Society α β))
            (α_disc : Society α β → Set S) (α_pt : α → S),
            Z ⊆ V(G) ∧ Z.ncard ≤ ζ ∧ Z.ncard < θ_star ∧
            IsCentralSegregation (deleteVertices G Z)
              (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) S_seg ∧
            IsSegregationOfType (deleteVertices G Z) ρ κ S_seg ∧
            IsProperArrangement S_seg α_disc α_pt) ∨
          ControlsMinor G (completeGraph p) T_star

/-- Statement of Graph Minors XVI, (5.2) (page 55):
"Let $\Sigma$ be a surface and let $p \ge 0$. Then there exists $\theta \ge 1$ such that if
$\mathscr{T}^*$ is a tangle in a graph $G$, and $H, \eta, \mathscr{T}$ is a $\Sigma$-span of order
$\ge \theta$ with metric $d$, and
* $s_1, t_1, \dots, s_\mu, t_\mu$ are distinct vertices of $H$, where $\mu = \frac{1}{2}p(p - 1)$,
  such that $d(u, v) \ge \theta$ for all distinct $u, v \in \{s_1, t_1, \dots, s_\mu, t_\mu\}$, and
* $Q_1, \dots, Q_\mu$ are mutually disjoint $\eta(H)$-paths, such that $Q_i$ has ends
  $\eta(s_i), \eta(t_i) (1 \le i \le \mu)$,
then $\mathscr{T}^*$ controls a $K_p$-minor of $G$." -/
def GM16Theorem52Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ p : ℕ, ∃ θ : ℕ, 1 ≤ θ ∧
      let μ := p * (p - 1) / 2
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star θ_span : ℕ)
        (T_star : Set (Hypergraph α β × Hypergraph α β))
        (H : Drawing S) (η : SpanEmbedding H G)
        (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ)
        (s t : Fin μ → S) (Q : Fin μ → Graph α β),
        IsSigmaSpan G H η θ_star θ_span T_star T →
        HasTangleMetric H θ_span T d →
        θ ≤ θ_span →
        (∀ i : Fin μ, s i ∈ H.V ∧ t i ∈ H.V ∧ s i ≠ t i) →
        Injective s → Injective t → Disjoint (range s) (range t) →
        (∀ u ∈ range s ∪ range t, ∀ v ∈ range s ∪ range t, u ≠ v → θ ≤ d {u} {v}) →
        (∀ i : Fin μ, IsHPathWithEnds G η.imageGraph (Q i) (η.vMap (s i)) (η.vMap (t i))) →
        Pairwise (fun i j => Disjoint V(Q i) V(Q j)) →
        ControlsMinor G (completeGraph p) T_star

/-- **Graph Minors XVI, (5.2)** (page 55, citing Graph Minors XII, (4.4)):
"Let $\Sigma$ be a surface and let $p \ge 0$. Then there exists $\theta \ge 1$ such that if
$\mathscr{T}^*$ is a tangle in a graph $G$, and $H, \eta, \mathscr{T}$ is a $\Sigma$-span of order
$\ge \theta$ with metric $d$, and
* $s_1, t_1, \dots, s_\mu, t_\mu$ are distinct vertices of $H$, where $\mu = \frac{1}{2}p(p - 1)$,
  such that $d(u, v) \ge \theta$ for all distinct $u, v \in \{s_1, t_1, \dots, s_\mu, t_\mu\}$, and
* $Q_1, \dots, Q_\mu$ are mutually disjoint $\eta(H)$-paths, such that $Q_i$ has ends
  $\eta(s_i), \eta(t_i) (1 \le i \le \mu)$,
then $\mathscr{T}^*$ controls a $K_p$-minor of $G$." -/
theorem theorem_5_2_proof :
    GM16Theorem52Statement.{u, v, w} := by
  intro S _ _ hS hconn p
  obtain ⟨θ, hθ1, hprop⟩ := GraphMinor.GM12.gm16_theorem44.{u, v, w} hS hconn p
  refine ⟨θ, hθ1, fun G θ_star θ_span T_star H η T d s t Q hSpan hMet hθ hst hs ht hdisj_st hd hQ
    hdisj_Q => ?_⟩
  exact controlsMinor_of_gm12 (hprop G θ_star θ_span T_star H η T d s t Q hSpan hMet hθ hst hs ht
    hdisj_st hd hQ hdisj_Q)

/-- Statement of Graph Minors XVI, (5.3) (page 56):
"Let $G$ be a graph and let $Y \subseteq V(G)$, such that no component of $G$ contains exactly one
vertex in $Y$. If $\mu, \tau \ge 0$ are integers and $|Y| > \tau(\mu - 1)$, then either:
* there are $\mu$ disjoint paths of $G$ each with both ends distinct and in $Y$ and with no internal
  vertex in $Y$, or
* there exist $v \in V(G)$ and $\tau$ paths $P_1, \dots, P_\tau$ of $G$, with ends
  $v, u_i (1 \le i \le \tau)$ respectively, mutually disjoint except for $v$, and such that for
  $1 \le i \le \tau, u_i \in Y$ and $u_i \ne v$, and no internal vertex of $P_i$ is in $Y$." -/
def GM16Theorem53Statement : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (Y : Set α) (μ τ : ℕ),
    V(G).Finite → E(G).Finite → Y ⊆ V(G) →
    (∀ y ∈ Y, ∃ y' ∈ Y, y' ≠ y ∧ Relation.ReflTransGen G.Adj y y') →
    τ * (μ - 1) < Y.ncard →
    (∃ (P : Fin μ → Graph α β) (s t : Fin μ → α),
      Pairwise (fun i j => Disjoint V(P i) V(P j)) ∧
      ∀ i : Fin μ, s i ∈ Y ∧ t i ∈ Y ∧ s i ≠ t i ∧
        IsGraphPathWithEnds G (P i) (s i) (t i) ∧
        V(P i) ∩ Y = {s i, t i}) ∨
    (∃ (v : α) (P : Fin τ → Graph α β) (u : Fin τ → α),
      v ∈ V(G) ∧
      (∀ i j : Fin τ, i ≠ j → V(P i) ∩ V(P j) = {v} ∧ Disjoint E(P i) E(P j)) ∧
      ∀ i : Fin τ, u i ∈ Y ∧ u i ≠ v ∧
        IsGraphPathWithEnds G (P i) v (u i) ∧
        V(P i) ∩ Y ⊆ {v, u i})

/-- Statement of Graph Minors XVI, (5.4) (page 56):
"Let $G$ be a graph, and let $v \in V(G)$. For $1 \le i \le n$ let $P_i$ be a path of $G$
with distinct ends $v, u_i$, such that $P_1, \dots, P_n$ are mutually disjoint except for
$v$. Let $Q_1, \dots, Q_m$ be mutually disjoint paths of $G$, not passing through $v$, such
that $Q_i$ has ends $s_i, t_i$ for $1 \le i \le m$. Let* $$Z = \{u_1, \dots, u_n, s_1, t_1,
\dots, s_m, t_m\}.$$ *If $n \ge 5m + 2$, there are $m + 1$ mutually disjoint paths of $G$,
each with distinct ends both in $Z$."

We require `s j ≠ t j` for every `j`. The printed statement omits this,
but its proof on page 57 uses that each `Q_j` has at least two vertices in
`Z`. This corrects the singleton-path counterexample. In the use in (5.5),
the `Q_j` are `H`-paths, whose ends are distinct by the definition in
Graph Minors XIV. -/
def GM16Theorem54Statement : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (v : α) (n m : ℕ)
    (P : Fin n → Graph α β) (u : Fin n → α)
    (Q : Fin m → Graph α β) (s t : Fin m → α),
    V(G).Finite → E(G).Finite → v ∈ V(G) →
    (∀ i : Fin n, u i ≠ v ∧ IsGraphPathWithEnds G (P i) v (u i)) →
    (∀ i j : Fin n, i ≠ j → V(P i) ∩ V(P j) = {v} ∧ Disjoint E(P i) E(P j)) →
    (∀ j : Fin m, v ∉ V(Q j) ∧ IsGraphPathWithEnds G (Q j) (s j) (t j)) →
    (∀ j : Fin m, s j ≠ t j) →
    Pairwise (fun i j => Disjoint V(Q i) V(Q j)) →
    5 * m + 2 ≤ n →
    let Z := range u ∪ range s ∪ range t
    ∃ (R : Fin (m + 1) → Graph α β) (a b : Fin (m + 1) → α),
      Pairwise (fun i j => Disjoint V(R i) V(R j)) ∧
      ∀ i : Fin (m + 1), a i ∈ Z ∧ b i ∈ Z ∧ a i ≠ b i ∧
        IsGraphPathWithEnds G (R i) (a i) (b i)

/-- Statement of Graph Minors XVI, (5.5) (page 57):
"For any surface $\Sigma$ and integer $p \ge 0$, there exists $\theta \ge 1$ such that, if
$\mathscr{T}^*$ is a tangle in a graph $G$ and there is a hairless animal with
$\frac{1}{2}p(p - 1)$ horns and with strength $\ge (\theta, 4p(p - 1))$, then $\mathscr{T}^*$
controls a $K_p$-minor of $G$." -/
def GM16Theorem55Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ p : ℕ, ∃ θ : ℕ, 1 ≤ θ ∧
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
        (T_star : Set (Hypergraph α β × Hypergraph α β)),
        IsGraphTangle G θ_star T_star →
        HasHairlessAnimal S G T_star θ_star (p * (p - 1) / 2) θ (4 * p * (p - 1)) →
        ControlsMinor G (completeGraph p) T_star

/-! ## Proof of Graph Minors XVI, (4.1) from (5.1) and (5.5) (page 58) -/


end GraphMinor.GM16
