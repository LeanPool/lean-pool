/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Minor.CompleteGraph

public import LeanPool.GraphMinor.GM14.Cited
public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM15.Defs

/-!
# Results from Graph Minors IX, XI, XII, and XIV cited in Graph Minors XV

This file states as `Prop`s the results from *Graph Minors IX. Disjoint crossed paths* (JCTB 49
(1990) 40–77), *Graph Minors XI. Circuits on a surface* (JCTB 60 (1994) 72–106),
*Graph Minors XII. Distance on a surface* (JCTB 64 (1995) 240–272), and
*Graph Minors XIV. Extending an embedding* (JCTB 65 (1995) 23–50) that are cited in
*Graph Minors XV. Giant steps* (JCTB 68 (1996) 112–148) over the shared definitions in
`GraphMinor.GM09.Defs`, `GraphMinor.GM10.Defs`, `GraphMinor.GM11.Defs`, `GraphMinor.GM12.Defs`,
`GraphMinor.GM14.Defs`, and `GraphMinor.GM15.Defs`:

- **Re-exported from `GraphMinor.GM14.Cited`:**
  - `GM11Theorem63Statement`: Graph Minors XI, (6.3) (page 89), used in (4.1) of Graph Minors XV.
  - `GM11Theorem810Statement`: Graph Minors XI, (8.10) (page 100).
  - `GM11Theorem812Statement`: Graph Minors XI, (8.12) (page 102), used in (4.1) of Graph Minors XV.
  - `GM12Theorem710Statement`: Graph Minors XII, (7.10) (page 270), used in (4.4) of Graph Minors
    XV.
- **From Graph Minors IX:**
  - `GM09Theorem71Statement`: (7.1) (page 59), quoted with a misprint as XV (6.2) (page 134).
  - `GM09Theorem81Statement`: (8.1) (page 60), nonempty-boundary case used in XV (2.1) (page 116).
  - `GM09Theorem1111Statement`: (11.11) (page 74), used to deduce (6.1) of Graph Minors XV
    (page 134).
- **From Graph Minors XI:**
  - `GM11Theorem91Statement`: metric facts for `HasTangleMetric`, including the triangle
    inequality from (9.1) (page 104).
- **From Graph Minors XII:**
  - `GM12Theorem41Statement`: (4.1) (page 248), used in (4.7) of Graph Minors XV (page 127).
  - `GM12Theorem45Statement`: (4.5) (page 252), used in (8.1) of Graph Minors XV (page 145).
  - `GM12Theorem51Statement`: (5.1) (page 254), used in (3.5) of Graph Minors XV (page 123).
  - `GM12Theorem52Statement`: corrected (5.2) with `2 ≤ θ` (page 254), used in XV (3.3) (page 121).
  - `GM12Theorem61Statement`: corrected (6.1) with `2 ≤ k` (pages 257–258), used in XV (3.4).
  - `GM12Theorem711Statement`: (7.11) (page 271), used in (4.3) of Graph Minors XV (page 125).
- **From Graph Minors XIV:**
  - `GM14Theorem73Statement`: (7.3) (page 36), used in claim (4) of XV (7.7) (page 141).
  - `GM14Theorem96Statement`: (9.6) (page 47), used in Section 7 of Graph Minors XV (pages 138–144).
  - `GM14Theorem101Statement`: (10.1) (page 49), used in (7.4) of Graph Minors XV (page 137).
-/

@[expose] public section

namespace GraphMinor.GM15

open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14

universe u v w

export GM14 (GM11Theorem63Statement GM11Theorem810Statement GM11Theorem812Statement
  GM12Theorem710Statement)

/-! ## 1. Results from Graph Minors IX -/

/-- Statement of Graph Minors IX, (7.1) (page 59). XV (6.2) (page 134) quotes it with a misprint
in the threshold, printing $2\tau_i$ for $2\tau_1$.
"Let $\phi \ge 2$, $\tau_1 \ge 3$, $\tau_2 \ge 4$ be integers. Let $\mathcal{P}$ be a crooked
transaction in a society $(G, \Omega)$ such that $|\mathcal{P}| \ge (\phi - 1)(2\tau_1 +
\tau_2 - 7)$. Then there exists $\mathcal{P}' \subseteq \mathcal{P}$ such that either* (i)
*$|\mathcal{P}'| = \phi$ and $\mathcal{P}'$ is a crosscap transaction, or* (ii)
*$|\mathcal{P}'| = \tau_1$ and $\mathcal{P}'$ is a leap transaction, or* (iii)
*$|\mathcal{P}'| = \tau_2$ and $\mathcal{P}'$ is a doublecross transaction." -/
def GM09Theorem71Statement : Prop :=
  ∀ {α : Type u} {β : Type v} (S : Society α β) (φ τ₁ τ₂ : ℕ)
    (P_set : Set (Graph α β)),
    2 ≤ φ → 3 ≤ τ₁ → 4 ≤ τ₂ →
    S.IsCrookedTransaction P_set →
    (φ - 1) * (2 * τ₁ + τ₂ - 7) ≤ P_set.ncard →
    ∃ P' ⊆ P_set,
      (P'.ncard = φ ∧ S.IsCrosscapTransaction P') ∨
      (P'.ncard = τ₁ ∧ S.IsLeapTransaction P') ∨
      (P'.ncard = τ₂ ∧ S.IsDoublecrossTransaction P')

/-- The nonempty-boundary case of Graph Minors IX, (8.1) (page 60), used in (2.1) of XV
(page 116) and (3.2) of XVI (page 50). The corrected full theorem also covers the null graph.
Every society `(G, Ω)` with `ΩBar ≠ ∅` and with no transaction of cardinality `> k` has a linear
decomposition of depth `≤ k`. -/
def GM09Theorem81Statement : Prop :=
  ∀ {α : Type u} {β : Type v} (S : Society α β) (k : ℕ),
    S.Ω.bar.Nonempty → S.IsPVortex k → S.HasLinearDecompositionOfDepthLE k

/-- Statement of Graph Minors IX, (11.11) (page 74), used to deduce (6.1) of Graph Minors XV
(page 134):
"Let $p \ge 2$, with $p \neq 3$. Let $(G, \Omega)$ be a society with no crooked transaction
of cardinality $p$. Then there is a feasible segregation $\{(A_0, \Omega_0), \dots, (A_k,
\Omega_k)\}$ of $(G, \Omega)$ such that $|\bar{\Omega}_1|, \dots, |\bar{\Omega}_k| \le 3$
and $(A_0, \Omega_0)$ has no transaction of cardinality $> 3p + 9$." -/
def GM09Theorem1111Statement : Prop :=
  ∀ {α : Type u} {β : Type v} (S : Society α β) (p : ℕ),
    2 ≤ p → p ≠ 3 →
    (∀ P_set : Set (Graph α β), S.IsCrookedTransaction P_set → P_set.ncard ≠ p) →
    ∃ (k : ℕ) (A₀ : Society α β) (A : Fin k → Society α β),
      IsFeasibleSegregation S A₀ A ∧
      (∀ i : Fin k, (A i).Ω.bar.ncard ≤ 3) ∧
      (∀ P_set : Set (Graph α β), A₀.IsTransaction P_set → P_set.ncard ≤ 3 * p + 9)

/-! ## 2. Results from Graph Minors XI -/

/-- Metric facts for a respectful tangle, including the triangle inequality from Graph Minors XI,
(9.1) (page 104), transferred from the radial slope distance.

For a respectful tangle `T` of order `θ` in a 2-cell drawing `H` in `Σ` with metric `d`:
(i) `A(H)` partitions `Σ`;
(ii) `d` satisfies the following laws on `A(H)` (`d(a, b) ≤ θ`, `d(a, a) = 0`, `d(a, b) = d(b, a)`,
`d(a, b) + d(b, c) ≥ d(a, c)`);
(iii) if `E(H) ≠ ∅`, `v ∈ V(H)`, `r ∈ R(H)` and `v ∈ closure r`, then `d(v, r) ≤ 1`;
(iv) if `v ∈ V(H)`, `e ∈ E(H)` and `v ∈ closure e`, then `d(v, e) ≤ 2`.
Parts (iii) and (iv) follow from the definition of the metric in Graph Minors XIV, page 27.
The bound in (iv) cannot be lowered to 1, although XIV writes this on page 36. The atom of `K`
for `e` is a region bounded by a circuit of length 4, and on a grid `K` has no circuit of length 2.
-/
def GM11Theorem91Statement : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] [T2Space S]
    (H : Drawing S) (θ : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ),
    IsClosedSurface S → ConnectedSpace S →
    HasTangleMetric H θ T d →
    (∀ σ : S, ∃! a : Set S, a ∈ H.A ∧ σ ∈ a) ∧
    (∀ a ∈ H.A, d a a = 0) ∧
    (∀ a ∈ H.A, ∀ b ∈ H.A, d a b ≤ θ) ∧
    (∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a) ∧
    (∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A, d a c ≤ d a b + d b c) ∧
    (H.E.Nonempty → ∀ v ∈ H.V, ∀ r ∈ H.R, v ∈ closure r → d {v} r ≤ 1) ∧
    (∀ v ∈ H.V, ∀ e ∈ H.E, v ∈ closure e → d {v} e ≤ 2)

/-! ## 3. Results from Graph Minors XII -/

/-- Statement of Graph Minors XII, (1.2) (page 242), derived from Graph Minors XI, (8.12)
(page 102) and used in (4.1) of Graph Minors XV (page 125), with the necessary hypothesis
`2 ≤ Γ.E.ncard` (as in Graph Minors XIV, (7.1), page 35; see the correction to (1.2) in
`corrections/GM12.md`):
Let `T` be a respectful tangle of order `θ ≥ 2` in a 2-cell drawing `Γ` with `|E(Γ)| ≥ 2` in a
connected surface `Σ`, and let its metric be `d`. Let `c ∈ A(Γ)`; then there is an edge `e` of `Γ`
with `d(c, e) = θ`. -/
def GM12Theorem12Statement : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] [T2Space S]
    (Γ : Drawing S) (θ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (c : Set S),
    IsClosedSurface S → ConnectedSpace S →
    2 ≤ θ → HasTangleMetric Γ θ T d → 2 ≤ Γ.E.ncard → c ∈ Γ.A →
    ∃ e ∈ Γ.E, d c e = θ

/-- Statement of Graph Minors XII, (4.1) (page 248), used in the proof of (4.7) of Graph Minors XV
(page 127):
"Let $\mathscr{T}$ be a respectful tangle in a 2-cell drawing $\Gamma$ in a connected surface
$\Sigma$, with metric $d$. Let $u, v \in V(\Gamma)$, and let $P$ be a path of $\Gamma$ between $u$
and $v$. If $(A, B) \in \mathscr{T}$ and $V(P) \subseteq V(A)$ then $(A, B)$ has order $\ge
\frac{1}{2} d(u, v)$." -/
def GM12Theorem41Statement : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] [T2Space S]
    (Γ P : Drawing S) (θ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (A B : Hypergraph S (Set S)) (u v : S),
    IsClosedSurface S → ConnectedSpace S →
    HasTangleMetric Γ θ T d →
    u ∈ Γ.V → v ∈ Γ.V →
    P.IsPathBetween u v → P.IsSubdrawing Γ →
    (A, B) ∈ T → P.V ⊆ A.vertexSet →
    d {u} {v} ≤ 2 * separationOrder A B

/-- The complete simple graph `K_p` on `Fin p` (with unordered pairs of distinct vertices as edges),
used for `GM12.ControlsMinor` in `GM12Theorem45Statement`. -/
abbrev completeGraph (n : ℕ) : Graph (Fin n) (Sym2 (Fin n)) := GraphMinor.completeGraph n

/-- Statement of Graph Minors XII, (4.5) (page 252), used in (8.1) of Graph Minors XV (page 145):
For any connected surface `Σ` with `bd(Σ) = ∅` and any integer `p ≥ 0`, there exist `κ, ϕ ≥ 0` such
that if `T*` is a tangle of order `≥ p` in a graph `G` and `H, η, T` is a `Σ`-span of order `≥ ϕ` in
`G` with respect to `T*` with `≥ κ` independent eyes, then `T*` controls a `K_p` minor of `G` in the
sense of `GM12.ControlsMinor`. -/
def GM12Theorem45Statement : Prop :=
  ∀ (S : Type w) [TopologicalSpace S] [T2Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ p : ℕ, ∃ κ φ : ℕ,
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
        (T_star : Set (Hypergraph α β × Hypergraph α β))
        (H : Drawing S) (η : SpanEmbedding H G) (θ : ℕ)
        (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ)
        (hSpan : IsSigmaSpan G H η θ_star θ T_star T),
        HasTangleMetric H θ T d →
        p ≤ θ_star → φ ≤ θ →
        HasIndependentEyes G H η θ T d κ →
        GM12.ControlsMinor
          (Hypergraph.ofGraph G hSpan.isControlling.isTangle_star.finite_V
            hSpan.isControlling.isTangle_star.finite_E)
          θ_star T_star (completeGraph p)

/-- Statement of Graph Minors XII, (5.1) (page 254), used in (3.5) of Graph Minors XV (page 123):
"Let $\Sigma_2$ be a handle of $\Sigma$, and let $\Sigma_1, \hat{\Sigma}_1$ be defined as above.
Let the two components of $\Sigma_1 \cap \Sigma_2$ be $C_1, C_2$. Let $\Gamma$ be a drawing in
$\Sigma$ such that $C_1, C_2$ are $\Gamma$-normal, and $$|V(\Gamma) \cap C_1| = |V(\Gamma) \cap
C_2| = \theta,$$ and such that $\Gamma \cap \Sigma_2$ has $\theta$ components, each a path with one
end in $C_1$ and the other in $C_2$. Suppose that every $\Gamma$-normal line $F \subseteq
\Sigma_1$ with one end in $C_1$ and one end in $C_2$ satisfies $|F \cap V(\Gamma)| \ge \theta$. Let
$\mathscr{T}_1$ be a tangle in $\Gamma \cap \hat{\Sigma}_1$, respectful towards $\hat{\Sigma}_1$,
of order $\theta$, such that $V(\Gamma) \cap C_1, V(\Gamma) \cap C_2$ are free with respect to
$\mathscr{T}_1$. Then the tangle in $\Gamma$ induced by $\mathscr{T}_1$ is respectful towards
$\Sigma$." -/
def GM12Theorem51Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    {S_hat : Type w} [TopologicalSpace S_hat] [T2Space S_hat]
    (C : Fin 2 → Set S) (P₁ P₂ : Set S) (ι : P₁ → S_hat) (D : Fin 2 → Set S_hat)
    (Γ : Drawing S) (Γ₁ : Drawing S_hat) (θ : ℕ)
    (T₁ : Set (Hypergraph S_hat (Set S_hat) × Hypergraph S_hat (Set S_hat)))
    (P : Fin θ → Drawing S) (a b : Fin θ → S),
    IsClosedSurface S → ConnectedSpace S →
    GM12.IsHandleSplit C P₁ P₂ ι D →
    GM12.IsCappedDrawing ι Γ Γ₁ →
    Γ.IsNormal (C 0) → Γ.IsNormal (C 1) →
    (Γ.V ∩ C 0).ncard = θ → (Γ.V ∩ C 1).ncard = θ →
    (∀ i : Fin θ, a i ∈ Γ.V ∩ C 0 ∧ b i ∈ Γ.V ∩ C 1 ∧
      (P i).IsPathBetween (a i) (b i) ∧ (P i).IsSubdrawing (Γ.interSet P₂)) →
    Pairwise (fun i j => Disjoint (P i).U (P j).U) →
    (Γ.interSet P₂).U = ⋃ i : Fin θ, (P i).U →
    (∀ F : Set S, IsLine F → Γ.IsNormal F → F ⊆ P₁ →
      (F ∩ C 0).Nonempty → (F ∩ C 1).Nonempty → θ ≤ (F ∩ Γ.V).ncard) →
    IsTangle Γ₁.toHypergraph θ T₁ →
    (PaintingOrDrawing.drawing Γ₁).IsRespectful θ T₁ →
    IsFreeSet Γ₁.toHypergraph T₁ θ (ι '' ((↑) ⁻¹' (Γ.V ∩ C 0))) →
    IsFreeSet Γ₁.toHypergraph T₁ θ (ι '' ((↑) ⁻¹' (Γ.V ∩ C 1))) →
    (PaintingOrDrawing.drawing Γ).IsRespectful θ (GM12.inducedAcross ι Γ Γ₁ θ T₁)

/-- Statement of Graph Minors XII, (5.2) (page 254), used in (3.3) of Graph Minors XV (page 121):
"Let $\Sigma_2$ be a crosscap of $\Sigma$, and let $\Sigma_1, \hat{\Sigma}_1$ be defined as above.
Let $\Gamma$ be a drawing in $\Sigma$ such that $\Sigma_1 \cap \Sigma_2$ is $\Gamma$-normal, and
$|V(\Gamma) \cap \Sigma_1 \cap \Sigma_2| = 2\theta$, and $\Gamma \cap \Sigma_2$ has $\theta$
components, each a path with ends some opposite pair of vertices in $V(\Gamma) \cap \Sigma_1 \cap
\Sigma_2$, in the natural sense. Suppose that $\mathscr{T}_1$ is a tangle in $\Gamma \cap
\hat{\Sigma}_1$, respectful towards $\hat{\Sigma}_1$, of order $\theta$, and every subset
$V(\Gamma) \cap \Sigma_1 \cap \Sigma_2$ of cardinality $\le \theta$ is free with respect to
$\mathscr{T}_1$. Then the tangle in $\Gamma$ induced by $\mathscr{T}_1$ is respectful towards
$\Sigma$."
The paper allows `θ = 1`, which is false: the one path may run along the boundary of the band, and
then the core of the band misses `Γ` and bounds no disc. So we assume `2 ≤ θ`. The use in XV (3.3)
has `3 ≤ φ`. -/
def GM12Theorem52Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    {S_hat : Type w} [TopologicalSpace S_hat] [T2Space S_hat]
    (C : Fin 1 → Set S) (P₁ P₂ : Set S) (ι : P₁ → S_hat) (D : Fin 1 → Set S_hat)
    (Γ : Drawing S) (Γ₁ : Drawing S_hat) (θ : ℕ)
    (T₁ : Set (Hypergraph S_hat (Set S_hat) × Hypergraph S_hat (Set S_hat)))
    (P : Fin θ → Drawing S) (a b : Fin θ → S),
    2 ≤ θ →
    IsClosedSurface S → ConnectedSpace S →
    GM12.IsCrosscapSplit C P₁ P₂ ι D →
    GM12.IsCappedDrawing ι Γ Γ₁ →
    Γ.IsNormal (C 0) →
    (Γ.V ∩ C 0).ncard = 2 * θ →
    ((List.ofFn a ++ List.ofFn b).Nodup) →
    GM12.IsListedInOrderOn (C 0) (List.ofFn a ++ List.ofFn b) →
    range a ∪ range b = Γ.V ∩ C 0 →
    (∀ i : Fin θ, (P i).IsPathBetween (a i) (b i) ∧ (P i).IsSubdrawing (Γ.interSet P₂)) →
    Pairwise (fun i j => Disjoint (P i).U (P j).U) →
    (Γ.interSet P₂).U = ⋃ i : Fin θ, (P i).U →
    IsTangle Γ₁.toHypergraph θ T₁ →
    (PaintingOrDrawing.drawing Γ₁).IsRespectful θ T₁ →
    (∀ X ⊆ ι '' ((↑) ⁻¹' (Γ.V ∩ C 0)), X.ncard ≤ θ → IsFreeSet Γ₁.toHypergraph T₁ θ X) →
    (PaintingOrDrawing.drawing Γ).IsRespectful θ (GM12.inducedAcross ι Γ Γ₁ θ T₁)

/-- Statement of Graph Minors XII, (6.1) (pages 257–258, written with `θ = 2k`), used in the
proof of Graph Minors XV (3.4) (page 123):
"Let $\Gamma$ be a 2-cell drawing in a connected surface $\Sigma$, and let $F$ be a $\Gamma$-normal
$O$-arc bounding a closed disc $\Delta \subseteq \Sigma$. Let $|F \cap V(\Gamma)| = \theta \ge 2$,
where $\theta$ is even, and let $$F \cap V(\Gamma) = \{v_1, v_2, \dots, v_\theta\}$$ numbered in
order on $F$. Let the components of $\Gamma \cap \Delta$ be $P_1, P_2, \dots, P_{\theta/2}$, where
for $1 \le i \le \theta/2$ $P_i$ is a path with ends $v_i, v_{\theta+1-i}$. Let $e_i$ be an edge of
$P_i$ ($1 \le i \le \theta/2$). Let $\Sigma_1 = \overline{\Sigma - \Delta}$, let $\Gamma_1 = \Gamma
\cap \Sigma_1$ be 2-cell (in $\Sigma$), and let $\mathscr{T}_1$ be a tangle in $\Gamma_1$ of order
$\theta_1 > \theta$, respectful towards $\Sigma$. Let $\mathscr{T}$ be the tangle in $\Gamma$
induced by $\mathscr{T}_1$; then $\mathscr{T}$ is clearly respectful towards $\Sigma$. Let $d$ be
the metric derived from $\mathscr{T}$. Finally, let $F \cap V(\Gamma_1)$ be free with respect to
$\mathscr{T}_1$. ... (6.1) In these circumstances, $d(e_1, e_{\theta/2}) \ge \theta$."
We assume `2 ≤ k` since `k = 1` would give `e₁ = e_k` and `d(e₁, e₁) = 0`. Its use in
the proof of XV (3.4) gives `d'(v_k, v_{2k}) ≥ 2k - 8`, as stated on page 122.
The proof on page 123 misprints those vertices as `v₁` and `v₂`. -/
def GM12Theorem61Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    (Γ : Drawing S) (F Δ : Set S) (k θ₁ : ℕ)
    (T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (a b : Fin k → S) (P : Fin k → Drawing S) (e_path : Fin k → Set S)
    (i₀ i_last : Fin k),
    IsClosedSurface S → ConnectedSpace S →
    2 ≤ k → 2 * k < θ₁ →
    (PaintingOrDrawing.drawing Γ).IsTwoCell →
    IsOArc F → Γ.IsNormal F → IsClosedDisc Δ → subBd Δ = F →
    ((List.ofFn a ++ (List.ofFn b).reverse).Nodup) →
    GM12.IsListedInOrderOn F (List.ofFn a ++ (List.ofFn b).reverse) →
    range a ∪ range b = F ∩ Γ.V →
    (∀ i : Fin k, (P i).IsPathBetween (a i) (b i) ∧ (P i).IsSubdrawing (Γ.interSet Δ)) →
    Pairwise (fun i j => Disjoint (P i).U (P j).U) →
    (Γ.interSet Δ).U = ⋃ i : Fin k, (P i).U →
    (∀ i : Fin k, e_path i ∈ (P i).E) →
    (PaintingOrDrawing.drawing (Γ.interSet (closure (univ \ Δ)))).IsTwoCell →
    IsRespectfulDrawingTangle (Γ.interSet (closure (univ \ Δ))) θ₁ T₁ →
    HasTangleMetric Γ θ₁
      (GM12.inducedBySubgraph Γ.toHypergraph (Γ.interSet (closure (univ \ Δ))).toHypergraph θ₁ T₁)
      d →
    IsFreeSet (Γ.interSet (closure (univ \ Δ))).toHypergraph T₁ θ₁
      (F ∩ (Γ.interSet (closure (univ \ Δ))).V) →
    i₀.1 = 0 → i_last.1 = k - 1 →
    2 * k ≤ d (e_path i₀) (e_path i_last)

/-- Statement of Graph Minors XII, (7.7) (page 268), used in (4.5) of Graph Minors XV (page 126):
"Let $\mathscr{T}$ be a respectful tangle of order $\theta$ in a 2-cell drawing $\Gamma$ in a
connected surface $\Sigma$; let its metric be $d$. Let $\Gamma'$ be a 2-cell subdrawing of
$\Gamma$, and let $\mathscr{T}'$ be a respectful tangle of order $\theta' \le \theta$ in $\Gamma'$,
with metric $d'$. Then
(i) for $k \ge 0$, if $d'(a', b') \ge d(a, b) - k$ for all $a, b \in A(\Gamma)$ and $a', b' \in
A(\Gamma')$ with $a \subseteq a'$ and $b \subseteq b'$, then $d(a, b) \ge \min(d'(a', b'), \theta -
k)$ for all such $a, b, a', b'$
(ii) if $\theta = \theta'$ and $\mathscr{T}$ is the tangle in $\Gamma$ induced by $\mathscr{T}'$,
then $d(a, b) \ge d'(a', b')$ for all $a, b \in A(\Gamma)$ and $a', b' \in A(\Gamma')$ with $a
\subseteq a'$ and $b \subseteq b'$." -/
def GM12Theorem77Statement : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] [T2Space S]
    (Γ Γ' : Drawing S) (θ θ' : ℕ)
    (T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d d' : Set S → Set S → ℕ),
    IsClosedSurface S → ConnectedSpace S →
    HasTangleMetric Γ θ T d →
    Γ'.IsSubdrawing Γ → (PaintingOrDrawing.drawing Γ').IsTwoCell →
    θ' ≤ θ → HasTangleMetric Γ' θ' T' d' →
    (∀ k : ℕ,
      (∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
        a ⊆ a' → b ⊆ b' → d a b - k ≤ d' a' b') →
      ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
        a ⊆ a' → b ⊆ b' → min (d' a' b') (θ - k) ≤ d a b) ∧
    (θ = θ' → T = GM12.inducedBySubgraph Γ.toHypergraph Γ'.toHypergraph θ' T' →
      ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
        a ⊆ a' → b ⊆ b' → d' a' b' ≤ d a b)

/-- Statement of Graph Minors XII, (7.11) (page 271), used in (4.3) of Graph Minors XV (page 125),
with the hypothesis "if `z ∈ E(H)` then `λ ≥ 2`" that XII states in (7.8) and (7.10) and omits here.
Without it the statement is false, for a path of three edges on the sphere with `θ = 2`, `z` the
middle edge and `λ ≤ 1` (see the correction to (7.11) in `corrections/GM12.md`):
Let `H` be a 2-cell drawing with `E(H) ≠ ∅` in a connected surface `Σ`, with a respectful tangle
`T` of order `θ` with metric `d`. Let `z ∈ A(H)` and let `λ ≥ 0` be an integer with `λ < θ`, such
that if `z ∈ E(H)` then `λ ≥ 2`. Then `H - z^λ` is 2-cell. -/
def GM12Theorem711Statement : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] [T2Space S]
    (H : Drawing S) (θ lam : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (z : Set S),
    IsClosedSurface S → ConnectedSpace S →
    HasTangleMetric H θ T d → H.E.Nonempty → z ∈ H.A → lam < θ → (z ∈ H.E → 2 ≤ lam) →
    (PaintingOrDrawing.drawing (deleteAtomNeighborhood H d z lam)).IsTwoCell

/-! ## 4. Results from Graph Minors XIV -/

/-- Statement of Graph Minors XIV, (7.3) (page 36), used in claim (4) of XV (7.7) (page 141).
Let `H` be a 2-cell drawing in `Σ` with `E(H) ≠ ∅`, and let `T` be a respectful tangle in `H` of
order `θ`, with metric `d`. Let `z ∈ A(H)`, and let `(A, B) ∈ T` with `E(B) ≠ {z}`. Then there
exists `e ∈ E(B)` with `d(z, e) ≥ θ - |V(A ∩ B)|`. -/
def GM14Theorem73Statement : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] [T2Space S]
    (H : Drawing S) (θ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (A B : Hypergraph S (Set S)) (z : Set S),
    IsClosedSurface S → ConnectedSpace S → H.E.Nonempty →
    HasTangleMetric H θ T d → z ∈ H.A → (A, B) ∈ T → B.edgeSet ≠ {z} →
    ∃ e ∈ B.edgeSet, θ - separationOrder A B ≤ d z e

/-- Statement of Graph Minors XIV, (9.6) (pages 47–48), used in (7.5) of Graph Minors XV
(page 138):
"Let $H$ be a 2-cell, rigid drawing in $\Sigma$, let $z \in A(H)$, and let $\mathscr{T}$ be a
respectful tangle in $H$ of order $\theta$, with metric $d$. Let $\pi \ge 0$ with $\pi \ne 1, 3$,
let $\beta \ge 2\pi + 8$ be even, and let $\theta \ge 16\beta + 17$. Let $H$ be a subgraph of $G$,
let $J$ be the union of some bridges of $H$ in $G$ such that $d(z, v) < \beta$ for each ... $v \in
V(H
\cap J)$, and let $G'$ be the union of $H$ and all the other bridges of $H$ in $G$. Let
$\mathscr{S}$ be a $\mathscr{T}$-local 3-segregation of $G'$, and let $\alpha$ be an arrangement of
$\mathscr{S}$ in $\Sigma$ compatible with $H$. Then there is a $(3\beta + 3)$-zone $\Lambda$ around
$z$, and a closed disc $\Delta \subseteq \Sigma$ with $bd(\Delta)$ $\alpha$-normal and with
$\Lambda \subseteq \Delta$, with the following properties:
(i) $d(z, x) \le 3\beta + 6$ for all $x \in A(H)$ with $x \cap \Delta \ne \emptyset$
(ii) $x \subseteq \Delta - bd(\Delta)$ for all $x \in A(H)$ with $d(z, x) < \beta$
(iii) $H \cap \overline{\Sigma - \Delta}$ has a circuit, and $H \cap (\Sigma - \Lambda)$ is a rigid
drawing in $\Sigma$
(iv) one of the following alternatives holds:
(a) there is a crooked transaction $\mathscr{P}$ of cardinality $\ge \pi$ in $(G, \Omega_0)$ (where
$\Omega_0$ is a natural order of $V(H) \cap bd(\Lambda)$ from $bd(\Lambda)$), such that
$V(\mathscr{P})$ is free with respect to the tangle of order $\theta - 4(3\beta + 3) - 2$ obtained
from $\mathscr{T}$ by clearing $\Lambda$, and each $P \in \mathscr{P}$ meets $H \cap (\Sigma -
\Lambda)$ in precisely the ends of $P$
(b) there is no crooked transaction of cardinality $\ge \pi$ in $(\alpha^{-1}(\Delta) \cup J,
\alpha^{-1}(bd(\Delta)))$." -/
def GM14Theorem96Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G_amb G G' J : Graph α β) (B_J B_rem : Set (Graph α β))
    (H : Drawing S) (η : SpanEmbedding H G_amb) (η' : SpanEmbedding H G')
    (θ π beta : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (z : Set S)
    (S_seg : Set (Society α β)) (α_disc : Society α β → Set S) (α_pt : α → S),
    IsClosedSurface S → ConnectedSpace S →
    V(G_amb).Finite → E(G_amb).Finite →
    IsRigid H → HasTangleMetric H θ T d → z ∈ H.A →
    π ≠ 1 → π ≠ 3 → 2 * π + 8 ≤ beta → Even beta → 16 * beta + 17 ≤ θ →
    (∀ B ∈ B_J, IsBridge G_amb η.imageGraph B) →
    (∀ B ∈ B_rem, IsBridge G_amb η.imageGraph B) →
    Disjoint B_J B_rem →
    J = subgraphSUnion G_amb B_J →
    G' = subgraphSUnion G_amb {η.imageGraph, subgraphSUnion G_amb B_rem} →
    G = subgraphUnion G_amb G' J →
    (∀ v ∈ H.V, η'.vMap v = η.vMap v) →
    (∀ e ∈ H.E, η'.eMap e = η.eMap e) →
    (∀ v ∈ H.V, η.vMap v ∈ V(J) → d z {v} < beta) →
    IsThreeSegregation G' S_seg →
    IsTangleLocal G' H η' T S_seg →
    IsSurfaceArrangement S_seg α_disc α_pt →
    IsCompatibleWith G' H η' S_seg α_disc α_pt →
    ∃ (Λ Δ : Set S)
      (T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d₁ : Set S → Set S → ℕ)
      (clearedEmbedding : SpanEmbedding (clearedSubdrawing H Λ) G_amb)
      (clearedSociety localSociety : Society α β),
      IsLambdaZoneAround H d (3 * beta + 3) z Λ ∧
      IsClearedTangle H T d θ (3 * beta + 3) Λ T₁ d₁ ∧
      IsClosedDisc Δ ∧
      IsArrangementNormal S_seg α_disc α_pt (subBd Δ) ∧
      Λ ⊆ Δ ∧
      (∀ x ∈ H.A, (x ∩ Δ).Nonempty → d z x ≤ 3 * beta + 6) ∧
      (∀ x ∈ H.A, d z x < beta → x ⊆ Δ \ subBd Δ) ∧
      (∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing (H.interSet (closure (univ \ Δ)))) ∧
      IsRigid (clearedSubdrawing H Λ) ∧
      (∀ v ∈ (clearedSubdrawing H Λ).V, clearedEmbedding.vMap v = η.vMap v) ∧
      (∀ e ∈ (clearedSubdrawing H Λ).E, clearedEmbedding.eMap e = η.eMap e) ∧
      clearedSociety.G = G ∧
      clearedSociety.Ω.bar = clearedEmbedding.vMap '' ((clearedSubdrawing H Λ).V ∩ subBd Λ) ∧
      (∃ inv_v : α → S,
        (∀ x ∈ clearedSociety.Ω.bar, inv_v x ∈ (clearedSubdrawing H Λ).V ∩ subBd Λ
          ∧ clearedEmbedding.vMap (inv_v x) = x)
          ∧
        IsNaturalOrderFrom inv_v clearedSociety.Ω (subBd Λ)) ∧
      localSociety.G = subgraphUnion G_amb J (arrangementPullbackGraph G' S_seg α_disc α_pt Δ) ∧
      IsPullbackPerm S_seg α_pt (subBd Δ) localSociety.Ω ∧
      ((∃ (P_set : Set (Graph α β)) (X : Set S),
          clearedSociety.IsCrookedTransaction P_set ∧
          π ≤ P_set.ncard ∧
          (∀ P ∈ P_set, ∀ a b : α,
            clearedSociety.IsOmegaPathWithEnds P a b →
            IsHPathWithEnds G_amb clearedEmbedding.imageGraph P a b) ∧
          X ⊆ (clearedSubdrawing H Λ).V ∩ subBd Λ ∧
          clearedSociety.transactionEnds P_set = clearedEmbedding.vMap '' X ∧
          IsFreeSet (clearedSubdrawing H Λ).toHypergraph T₁ (θ - 4 * (3 * beta + 3) - 2) X) ∨
       (∀ P_set : Set (Graph α β), localSociety.IsCrookedTransaction P_set → ¬ π ≤ P_set.ncard))

/-- Statement of Graph Minors XIV, (10.1) (page 49), used in (7.4) of Graph Minors XV (page 137):
Let `H` be a 2-cell, rigid drawing in `Σ`, and let `T` be a respectful tangle in `H` of order `θ`,
with metric `d`. Let `η` embed `H` in `G₀`, let `μ ≥ 12` be an even integer with `θ ≥ 16μ + 17`,
and suppose that
(i) `d(u, v) < μ` for every `η(H)`-path in `G₀` with ends `η(u), η(v)`, and
(ii) if `T'` is the tangle of order `θ - 4(3μ + 3) - 2` obtained from `T` by clearing some
`(3μ + 3)`-zone `Λ` such that `H ∩ (Σ - Λ)` is a rigid drawing in `Σ`, then `Λ` is not an eye of
`H ∩ (Σ - Λ)` in `G₀` with respect to `T'`.
Then there is a `T`-local 3-segregation of `G₀` and an arrangement of it in `Σ` compatible with
`H`. -/
def GM14Theorem101Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G₀ : Graph α β) (H : Drawing S) (η : SpanEmbedding H G₀) (θ μ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ),
    IsClosedSurface S → ConnectedSpace S →
    V(G₀).Finite → E(G₀).Finite →
    IsRigid H → HasTangleMetric H θ T d →
    12 ≤ μ → Even μ → 16 * μ + 17 ≤ θ →
    ¬ IsMuSteppedSpan G₀ H η d μ →
    (∀ (z Λ : Set S)
        (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d' : Set S → Set S → ℕ)
        (η' : SpanEmbedding (clearedSubdrawing H Λ) G₀),
      IsLambdaZoneAround H d (3 * μ + 3) z Λ →
      IsClearedTangle H T d θ (3 * μ + 3) Λ T' d' →
      IsRigid (clearedSubdrawing H Λ) →
      (∀ v ∈ (clearedSubdrawing H Λ).V, η'.vMap v = η.vMap v) →
      (∀ e ∈ (clearedSubdrawing H Λ).E, η'.eMap e = η.eMap e) →
      ¬ IsDrawingEye G₀ (clearedSubdrawing H Λ) η' (θ - 4 * (3 * μ + 3) - 2) T' Λ) →
    ∃ (S_seg : Set (Society α β)) (α_disc : Society α β → Set S) (α_pt : α → S),
      IsThreeSegregation G₀ S_seg ∧
      IsTangleLocal G₀ H η T S_seg ∧
      IsSurfaceArrangement S_seg α_disc α_pt ∧
      IsCompatibleWith G₀ H η S_seg α_disc α_pt

end GraphMinor.GM15
