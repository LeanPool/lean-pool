/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section3

import LeanPool.GraphMinor.GM12.Bridge

/-!
# Graph Minors XVI, Section 4: Induction on the Surface

This file formalizes Section 4 ("Induction on the surface", pages 52–54) of
N. Robertson and P. D. Seymour, *Graph Minors. XVI. Excluding a non-planar graph*, J. Combin.
Theory Ser. B 89 (2003) 43–76:

- `IsObtainedByAddingHandleOrCrosscap`: a surface `Σ'` obtained from `Σ` by adding a handle or a
  crosscap.
- Statement of **Graph Minors XVI, (4.1)** (`GM16Theorem41Statement`, page 52).
- Statement of **Graph Minors XVI, (4.2)** (`GM16Theorem42Statement`, page 53).
- Statement and proof of **Graph Minors XVI, (4.3)** (`GM16Theorem43Statement`, `theorem_4_3`,
  page 54), deduced from `GM12Theorem43Statement` and `controlsMinor_of_gm12`.
- Monotonicity of `IsSegregationOfType` (`IsSegregationOfType.mono`).
- Proof of **Graph Minors XVI, (3.1)** (`theorem_3_1`, page 54) from `(4.1)`, `(4.2)`, `(4.3)`,
  and `GM12Theorem42Statement` by induction over the finite surface tower.
The backward and tower inductions are proved in `InductionsProved.lean`.
-/

@[expose] public section

namespace GraphMinor.GM16

open Set Function Topology
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14 GraphMinor.GM15

universe u v w u' v'

variable {α : Type u} {β : Type v}

/-! ## Surface Operations and Statements of (4.1), (4.2), and (4.3) (pages 52–54) -/

/-- A surface `S'` is obtained from `S` by adding a handle or a crosscap
(Graph Minors XVI, Section 4, page 52). -/
def IsObtainedByAddingHandleOrCrosscap
    (S : Type w) [TopologicalSpace S] (S' : Type w) [TopologicalSpace S'] : Prop :=
  IsObtainedByAddingHandle S S' ∨ IsObtainedByAddingCrosscap S S'

/-- Statement of Graph Minors XVI, (4.1) (page 52):
"Let $\Sigma$ be a surface and let $p \ge 0$, $\phi \ge 1$. Then there exist $\kappa, \rho, \zeta
\ge 0$
and $\theta \ge 1$ such that if $\mathscr{T}^*$ is a tangle in a graph $G$, and there is a
$\Sigma$-span of order $\ge \theta$, then either
• there is a $\Sigma'$-span of order $\ge \phi$, for some surface $\Sigma'$ obtained from $\Sigma$
  by adding a handle or crosscap, or
• there exists $Z \subseteq V(G)$ with $|Z| \le \zeta$, and a $\mathscr{T}^* \setminus Z$-central
  segregation of $G \setminus Z$ of type $(\rho, \kappa)$ with a proper arrangement in $\Sigma$, or
• $\mathscr{T}^*$ controls a $K_p$ minor of $G$." -/
def GM16Theorem41Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ p φ : ℕ, 1 ≤ φ →
      ∃ κ ρ ζ θ : ℕ, 1 ≤ θ ∧
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star θ_span : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (H : Drawing S) (η : SpanEmbedding H G)
          (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (hT : IsGraphTangle G θ_star T_star),
          θ ≤ θ_span → IsSigmaSpan G H η θ_star θ_span T_star T →
          (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S')
            (H' : Drawing S') (η' : SpanEmbedding H' G) (θ_span' : ℕ)
            (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
            IsClosedSurface S' ∧ ConnectedSpace S' ∧
            IsObtainedByAddingHandleOrCrosscap S S' ∧
            φ ≤ θ_span' ∧ IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨
          (∃ (Z : Set α) (S_seg : Set (Society α β))
            (α_disc : Society α β → Set S) (α_pt : α → S),
            Z ⊆ V(G) ∧ Z.ncard ≤ ζ ∧ Z.ncard < θ_star ∧
            IsCentralSegregation (deleteVertices G Z)
              (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) S_seg ∧
            IsSegregationOfType (deleteVertices G Z) ρ κ S_seg ∧
            IsProperArrangement S_seg α_disc α_pt) ∨
          ControlsMinor G (completeGraph p) T_star

/-- Statement of Graph Minors XVI, (4.2) (page 53):
"For any integer $\theta \ge 1$ there exists $\theta^* \ge 1$ such that if $\mathscr{T}^*$ is a
tangle of order $\ge \theta^*$ in a graph $G$, there is a $\Sigma$-span of order $\ge \theta$, where
$\Sigma$ is the sphere." -/
def GM16Theorem42Statement : Prop :=
  ∀ θ : ℕ, 1 ≤ θ →
    ∃ θ_star : ℕ, 1 ≤ θ_star ∧
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_G : ℕ)
        (T_star : Set (Hypergraph α β × Hypergraph α β)),
        IsGraphTangle G θ_G T_star → θ_star ≤ θ_G →
        ∀ (S : Type w) [TopologicalSpace S] [T2Space S],
          IsClosedSurface S → ConnectedSpace S → IsSphere S →
          ∃ (H : Drawing S) (η : SpanEmbedding H G) (θ_span : ℕ)
            (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
            θ ≤ θ_span ∧ IsSigmaSpan G H η θ_G θ_span T_star T

/-- Statement of Graph Minors XVI, (4.3) (page 54):
"If $L$ is a graph and $\Sigma$ is a surface such that $L$ can be drawn in $\Sigma$, there is an
integer $\theta \ge 1$ with the following property. If $\mathscr{T}^*$ is a tangle in a graph $G$
controlling no $L$ minor, then there is no $\Sigma$-span of order $\ge \theta$." -/
def GM16Theorem43Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    {α' : Type u'} {β' : Type v'} (L : Graph α' β'),
    IsClosedSurface S → ConnectedSpace S → V(L).Finite → E(L).Finite →
    CanBeDrawnIn S L →
    ∃ θ : ℕ, 1 ≤ θ ∧
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
        (T_star : Set (Hypergraph α β × Hypergraph α β))
        (H : Drawing S) (η : SpanEmbedding H G) (θ_span : ℕ)
        (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
        IsGraphTangle G θ_star T_star →
        ¬ ControlsMinor G L T_star →
        θ ≤ θ_span → ¬ IsSigmaSpan G H η θ_star θ_span T_star T

/-- **Graph Minors XVI, (4.3)** (page 54, citing Graph Minors XII, (4.3)):
"If $L$ is a graph and $\Sigma$ is a surface such that $L$ can be drawn in $\Sigma$, there is an
integer $\theta \ge 1$ with the following property. If $\mathscr{T}^*$ is a tangle in a graph $G$
controlling no $L$ minor, then there is no $\Sigma$-span of order $\ge \theta$." -/
theorem theorem_4_3_proof :
    GM16Theorem43Statement.{u, v, w, u', v'} := by
  intro S _ _ α' β' L hS hconn hVL hEL hdraw
  obtain ⟨θ, hθ1, hprop⟩ := GraphMinor.GM12.gm16_theorem43.{u, v, w, u', v'} L hS hconn hVL hEL
    hdraw
  refine ⟨θ, hθ1, fun G θ_star T_star H η θ_span T hT hnot_ctrl hθ hSpan => ?_⟩
  have hnot_gm12 :
      ¬ GM12.ControlsMinor (Hypergraph.ofGraph G hT.finite_V hT.finite_E) θ_star T_star L :=
    fun h => hnot_ctrl (controlsMinor_of_gm12 h)
  exact hprop G θ_star T_star H η θ_span T hT hnot_gm12 hθ hSpan

/-! ## Monotonicity of `IsRhoVortex` and `IsSegregationOfType` -/

/-- Monotonicity of `IsRhoVortex`: a `ρ₁`-vortex is a `ρ₂`-vortex whenever `ρ₁ ≤ ρ₂`. -/
theorem IsRhoVortex.mono {S : Society α β} {ρ₁ ρ₂ : ℕ} (h : IsRhoVortex S ρ₁) (hle : ρ₁ ≤ ρ₂) :
    IsRhoVortex S ρ₂ := by
  intro u hu v hv huv ⟨P, hdisj, hends⟩
  refine h u hu v hv huv ⟨fun i => P ⟨i.1, by omega⟩, ?_, fun i => hends ⟨i.1, by omega⟩⟩
  intro i j hij
  exact hdisj (fun h_eq => hij (Fin.ext (Fin.mk.inj h_eq)))

/-- Monotonicity of `IsSegregationOfType`: a segregation of type `(ρ₁, κ₁)` is of type `(ρ₂, κ₂)`
whenever `ρ₁ ≤ ρ₂` and `κ₁ ≤ κ₂`. -/
theorem IsSegregationOfType.mono {G : Graph α β} {ρ₁ κ₁ ρ₂ κ₂ : ℕ}
    {S_seg : Set (Society α β)} (h : IsSegregationOfType G ρ₁ κ₁ S_seg)
    (hρ : ρ₁ ≤ ρ₂) (hκ : κ₁ ≤ κ₂) :
    IsSegregationOfType G ρ₂ κ₂ S_seg where
  isSegregation := h.isSegregation
  vortex_count_le := h.vortex_count_le.trans hκ
  is_rho_vortex _ hS h3 := (h.is_rho_vortex hS h3).mono hρ

/-! ## Proof of Graph Minors XVI, (3.1) from (4.1), (4.2), and (4.3) (page 54) -/

/-- A finite tower of closed connected surfaces `Σ_0, …, Σ_{n-1}` for a graph `L`
(Graph Minors XVI, Section 4, page 54):
"Up to homeomorphism, let $\Sigma_1, \dots, \Sigma_n$ be all the surfaces on which $L$ cannot be
drawn together with the sphere and all the surfaces which can be obtained from a surface on which
$L$ cannot be drawn by adding a handle or crosscap. (There are only finitely many up to
homeomorphism.) Let us number $\Sigma_1, \dots, \Sigma_n$ so that for $1 \le i, j \le n$, if
$\Sigma_j$ can be obtained from $\Sigma_i$ by adding a handle or crosscap then $j \ge i$." -/
structure SurfaceTowerFor {α' : Type u'} {β' : Type v'} (L : Graph α' β') where
  /-- Number of surfaces in the tower (`n ≥ 1`). -/
  n : ℕ
  /-- `1 ≤ n`. -/
  one_le_n : 1 ≤ n
  /-- The surfaces `Σ_0, …, Σ_{n-1}`. -/
  Surf : Fin n → Type w
  /-- Topological space structure on each `Σ_i`. -/
  topSpace : ∀ i, TopologicalSpace (Surf i)
  /-- Hausdorff structure on each `Σ_i`. -/
  t2Space : ∀ i, @T2Space (Surf i) (topSpace i)
  /-- Each `Σ_i` is a closed surface. -/
  isClosedSurface : ∀ i, @IsClosedSurface (Surf i) (topSpace i)
  /-- Each `Σ_i` is connected. -/
  isConnected : ∀ i, @ConnectedSpace (Surf i) (topSpace i)
  /-- `Σ_0` is a 2-sphere. -/
  isSphere_zero : @IsSphere (Surf ⟨0, one_le_n⟩) (topSpace ⟨0, one_le_n⟩)
  /-- If `L` cannot be drawn in `Σ_i` and `S'` is obtained from `Σ_i` by adding a handle or
  crosscap, then `S'` appears at some later index `j > i` in the tower (up to homeomorphism, so any
  `S'`-span of order `≥ φ` yields a `Σ_j`-span of order `≥ φ`). -/
  step_index : ∀ (i : Fin n),
    ¬ @CanBeDrawnIn _ _ (Surf i) (topSpace i) L →
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star φ : ℕ)
      (T_star : Set (Hypergraph α β × Hypergraph α β))
      (S' : Type w) [TopologicalSpace S'] [T2Space S']
      (H' : Drawing S') (η' : SpanEmbedding H' G) (θ_span' : ℕ)
      (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
      IsClosedSurface S' → ConnectedSpace S' →
      @IsObtainedByAddingHandleOrCrosscap (Surf i) (topSpace i) S' _ →
      φ ≤ θ_span' → IsSigmaSpan G H' η' θ_star θ_span' T_star T' →
      ∃ (j : Fin n), i < j ∧
        ∃ (H_j : @Drawing (Surf j) (topSpace j)) (η_j : @SpanEmbedding (Surf j)
          (topSpace j) α β H_j G)
          (θ_span_j : ℕ)
          (T_j : Set (Hypergraph (Surf j) (Set (Surf j)) × Hypergraph (Surf j) (Set (Surf j)))),
          φ ≤ θ_span_j ∧
          @IsSigmaSpan α β (Surf j) (topSpace j) (t2Space j) G H_j η_j θ_star θ_span_j T_star T_j

/-- The finite surface tower used in Graph Minors XVI, proof of (3.1), page 54.
For a single vertex the sphere alone suffices, since the vertex can be drawn
in every surface. For the complete graph on five vertices, the sphere is the
only closed connected surface excluding the graph. Its one-step successors
must also be included. Existence of these towers is a surface topology result. -/
def SurfaceTowerStatement : Prop :=
  ∀ {α' : Type u'} {β' : Type v'} (L : Graph α' β'),
    V(L).Finite → E(L).Finite → Nonempty (SurfaceTowerFor.{u, v, w, u', v'} L)

attribute [local instance] SurfaceTowerFor.topSpace SurfaceTowerFor.t2Space


end GraphMinor.GM16
