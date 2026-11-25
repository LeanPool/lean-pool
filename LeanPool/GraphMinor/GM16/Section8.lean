/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

import LeanPool.GraphMinor.GM12.Section79

public import LeanPool.GraphMinor.GM16.Section7
import LeanPool.GraphMinor.GM10.TangleLemmas
import LeanPool.GraphMinor.GM09.Basic

/-!
# Graph Minors XVI, Section 8: Non-Level `Σ`-Spans

This file formalizes Section 8 ("Non-level $\Sigma$-spans", pages 64–70) of
N. Robertson and P. D. Seymour, *Graph Minors. XVI. Excluding a non-planar graph*, J. Combin.
Theory Ser. B 89 (2003) 43–76:

- Truncation of a respectful tangle in a drawing (`IsRespectfulDrawingTangle.truncation`).
- Restriction of a `SpanEmbedding H G` to `G \ Z` when `Z` is disjoint from `V(η(H))`
  (`restrictDeleteVertices`).
- Statement of **Graph Minors XVI, (8.1)** (`GM16Theorem81Statement`, page 64).
- Statement and complete proof of **Graph Minors XVI, (8.2)** (`GM16Theorem82Statement`,
  `theorem_8_2`, pages 64–65): if `Z ⊆ V(G) \ V(η(H))` with `|Z| < ord(T)` and
  `1 ≤ θ' ≤ ord(T) - |Z|`, the truncation `T'` of `T` to order `θ'` is a `Σ`-span in `G \ Z`
  with respect to `T* \ Z`.
- Statement of **Graph Minors XVI, (8.3)** (`GM16Theorem83Statement`, page 65), together with
  Claims (1) and (2) of the proof of `(7.1)` (`theorem_7_1_claim_1`, `theorem_7_1_claim_2`,
  page 69).
-/

@[expose] public section

namespace GraphMinor.GM16

open Set Function Topology
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14 GraphMinor.GM15

universe u v w

variable {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}

/-! ## Truncation of Respectful Drawing Tangles and Span Embeddings -/

omit [T2Space S] in
/-- The truncation `GM10.truncation T θ'` of a respectful tangle `T` of order `θ` in `H` to order
`θ'` (`1 ≤ θ' ≤ θ`) is a respectful tangle of order `θ'` in `H` (Graph Minors XVI, Section 8,
page 64). -/
theorem IsRespectfulDrawingTangle.truncation {H : Drawing S} {θ θ' : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hResp : IsRespectfulDrawingTangle H θ T) (h1 : 1 ≤ θ') (hle : θ' ≤ θ) :
    IsRespectfulDrawingTangle H θ' (GM10.truncation T θ') := by
  exact GM12.IsRespectfulDrawingTangle.truncation hResp h1 hle

/-- If `K ≤ G` and `Disjoint V(K) Z`, then `K ≤ GM09.deleteVertices G Z`. -/
theorem le_deleteVertices_of_disjoint {G K : Graph α β} {Z : Set α}
    (hle : K ≤ G) (hdisj : Disjoint V(K) Z) :
    K ≤ GM09.deleteVertices G Z := by
  refine ⟨fun v hv => ⟨hle.vertexSet_mono hv, hdisj.notMem_of_mem_left hv⟩,
    fun {e x y} hlink => ?_⟩
  have hxK : x ∈ V(K) := K.left_mem_of_isLink hlink
  have hyK : y ∈ V(K) := K.left_mem_of_isLink hlink.symm
  exact ⟨(hle.isLink_iff hlink.edge_mem).mp hlink,
    ⟨hle.vertexSet_mono hxK, hdisj.notMem_of_mem_left hxK⟩,
    ⟨hle.vertexSet_mono hyK, hdisj.notMem_of_mem_left hyK⟩⟩

/-- Restrict a `SpanEmbedding H G` to `GM09.deleteVertices G Z` when `Z` is disjoint from
`V(η.imageGraph)`. -/
def restrictDeleteVertices {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) (Z : Set α) (hdisj : Disjoint V(η.imageGraph) Z) :
    SpanEmbedding H (GM09.deleteVertices G Z) where
  imageGraph := η.imageGraph
  vMap := η.vMap
  eMap := η.eMap
  imageGraph_le := le_deleteVertices_of_disjoint η.imageGraph_le hdisj
  bijOn_v := η.bijOn_v
  bijOn_e := η.bijOn_e
  inc_iff := η.inc_iff

/-! ## Statements of (8.1), (8.2), and (8.3), and Proof of (8.2) (pages 64–65) -/

/-- Statement of Graph Minors XVI, (8.1) (page 64):
"Let $\Sigma$ be a surface and let $\delta \ge 0$ and $\phi, \psi \ge 3$. Then there exists
$\gamma \ge 0$ and $\theta > (4\gamma + 2)\delta$ such that if $\mathcal{T}^*$ is a tangle in a
graph $G$ and $H, \mathcal{T}$ is a $\Sigma$-span of order $\ge \theta$, and $Y \subseteq V(H)$
satisfies $|Y| = \delta$ and $d(y, y') \ge \theta$ for all distinct $y, y' \in Y$ (where $d$ is the
metric of $\mathcal{T}$), then either:
1. there is a $\Sigma'$-span of order $\ge \phi$ for some surface $\Sigma'$ obtained from $\Sigma$
   by adding a handle, or
2. there is an $H$-path in $G$ with ends $s, t$, such that $d(s, t) \ge \psi$ and
   $d(s, y) \ge \psi$ for all $y \in Y$, or
3. there is a $\gamma$-envelope $(\Lambda_y\colon y \in Y)$ around $Y$, and there exists
   $Z \subseteq V(G) \setminus V(H')$ with $|Z| \le \frac{1}{2}\delta^2\phi^2$, such that $Z$ meets
   every $H'$-path in $G$ with ends $s, t$, satisfying $d'(s, t) \ge 2\psi$, where
   $H' = H \cap (\Sigma \setminus \cup (\Lambda_y\colon y \in Y))$ and $d'$ is the metric of the
   $(4\gamma + 2)\delta$-compression of $\mathcal{T}$ in $H'$." -/
def GM16Theorem81Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ δ φ ψ : ℕ, 3 ≤ φ → 3 ≤ ψ →
      ∃ γ θ : ℕ, (4 * γ + 2) * δ < θ ∧
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star θ_span : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (H : Drawing S) (η : SpanEmbedding H G)
          (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (d : Set S → Set S → ℕ) (Y : Set S),
          θ ≤ θ_span →
          IsSigmaSpan G H η θ_star θ_span T_star T →
          HasTangleMetric H θ_span T d →
          Y ⊆ H.V → Y.ncard = δ →
          (∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ ≠ y₂ → θ ≤ d {y₁} {y₂}) →
          (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S')
            (H' : Drawing S') (η' : SpanEmbedding H' G) (θ_span' : ℕ)
            (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
            IsObtainedByAddingHandle S S' ∧
            φ ≤ θ_span' ∧ IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨
          (∃ (P : Graph α β) (s t : S),
            s ∈ H.V ∧ t ∈ H.V ∧
            IsHPathWithEnds G η.imageGraph P (η.vMap s) (η.vMap t) ∧
            ψ ≤ d {s} {t} ∧ ∀ y ∈ Y, ψ ≤ d {s} {y}) ∨
          (∃ (Λ : S → Set S) (Z : Set α)
            (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
            (d' : Set S → Set S → ℕ),
            IsEnvelope H d Y γ Λ ∧
            Z ⊆ V(G) \ V((restrictCleared η (⋃ y ∈ Y, Λ y)).imageGraph) ∧
            Z.ncard ≤ (δ ^ 2 * φ ^ 2) / 2 ∧
            IsSigmaSpan G (clearEnvelopeDrawing H Y Λ)
              (restrictCleared η (⋃ y ∈ Y, Λ y)) θ_star (θ_span - (4 * γ + 2) * δ) T_star T' ∧
            IsLambdaCompression H (clearEnvelopeDrawing H Y Λ)
              θ_span ((4 * γ + 2) * δ) T T' d d' ∧
            ∀ (P : Graph α β) (s t : S),
              s ∈ (clearEnvelopeDrawing H Y Λ).V →
              t ∈ (clearEnvelopeDrawing H Y Λ).V →
              IsHPathWithEnds G (restrictCleared η (⋃ y ∈ Y, Λ y)).imageGraph P
                (η.vMap s) (η.vMap t) →
              2 * ψ ≤ d' {s} {t} →
              (Z ∩ V(P)).Nonempty)

/-- Statement of Graph Minors XVI, (8.2) (page 64):
"Let $\mathcal{T}^*$ be a tangle in a graph $G$, and let $H, \mathcal{T}$ be a $\Sigma$-span. Let
$Z \subseteq V(G) \setminus V(H)$ with $|Z| < ord(\mathcal{T})$, let
$1 \le \theta' \le ord(\mathcal{T}) - |Z|$, and let $\mathcal{T}'$ be the truncation of
$\mathcal{T}$ to order $\theta'$. Then $H, \mathcal{T}'$ is a $\Sigma$-span in $G \setminus Z$ with
respect to $\mathcal{T}^* \setminus Z$." -/
def GM16Theorem82Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    {α : Type u} {β : Type v} (G : Graph α β) (θ_star θ θ' : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (H : Drawing S) (η : SpanEmbedding H G)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (Z : Set α)
    (hSpan : IsSigmaSpan G H η θ_star θ T_star T)
    (_ : Z ⊆ V(G)) (hZ_disj : Disjoint V(η.imageGraph) Z)
    (_ : Z.ncard < θ) (_ : 1 ≤ θ') (_ : θ' ≤ θ - Z.ncard),
    IsSigmaSpan (GM09.deleteVertices G Z) H (restrictDeleteVertices η Z hZ_disj)
      (θ_star - Z.ncard) θ'
      (deleteGraphVerticesTangle G hSpan.isControlling.isTangle_star.finite_V
        hSpan.isControlling.isTangle_star.finite_E Z T_star θ_star)
      (GM10.truncation T θ')

/-- **Graph Minors XVI, (8.2)** (pages 64–65):
If `H, η, T` is a `Σ`-span of order `θ` in `G` with respect to `T*`, `Z ⊆ V(G) \ V(η(H))` has
`|Z| < θ`, and `1 ≤ θ' ≤ θ - |Z|`, then the truncation `GM10.truncation T θ'` is a `Σ`-span in
`G \ Z` with respect to `T* \ Z`. -/
theorem theorem_8_2_proof : GM16Theorem82Statement.{u, v, w} := by
  intro S _ _ α β G θ_star θ θ' T_star H η T Z hSpan hZ_sub hZ_disj hZ_lt hθ'_pos hθ'_le
  let hT_star := hSpan.isControlling.isTangle_star
  have hθ_le : θ ≤ θ_star := hSpan.isControlling.theta_le
  have hZ_lt_star : Z.ncard < θ_star := lt_of_lt_of_le hZ_lt hθ_le
  have hT_del : IsGraphTangle (GM09.deleteVertices G Z) (θ_star - Z.ncard)
      (deleteGraphVerticesTangle G hT_star.finite_V hT_star.finite_E Z T_star θ_star) :=
    isGraphTangle_deleteGraphVerticesTangle hT_star hZ_sub hZ_lt_star
  have hResp' : IsRespectfulDrawingTangle H θ' (GM10.truncation T θ') :=
    IsRespectfulDrawingTangle.truncation hSpan.isRespectful hθ'_pos (hθ'_le.trans
      (Nat.sub_le θ Z.ncard))
  refine ⟨hSpan.isSurface, hSpan.isConnected, hSpan.bd_empty, hSpan.isRigid, hResp',
    ⟨by omega, hT_del, hResp'.2.1, ?_⟩⟩
  intro A B hsep hord A_H B_H hRestr
  -- Any restricted separation `(A_H, B_H)` of `(A, B)` has order `≤ separationOrder A B < θ'`.
  have hord_H : separationOrder A_H B_H < θ' := by
    have hinj : InjOn η.vMap (A_H ∩ B_H).vertexSet :=
      η.bijOn_v.injOn.mono
        (inter_subset_left.trans hRestr.1.left_le.vertexSet_subset)
    have hsub_img : η.vMap '' (A_H ∩ B_H).vertexSet ⊆ (A ∩ B).vertexSet := by
      rintro v ⟨u, ⟨huA, huB⟩, rfl⟩
      have huA' : η.vMap u ∈ (restrictDeleteVertices η Z hZ_disj).vMap '' A_H.vertexSet :=
        ⟨u, huA, rfl⟩
      have huB' : η.vMap u ∈ (restrictDeleteVertices η Z hZ_disj).vMap '' B_H.vertexSet :=
        ⟨u, huB, rfl⟩
      rw [hRestr.2.1] at huA'
      rw [hRestr.2.2.2.1] at huB'
      exact ⟨huA'.1, huB'.1⟩
    have hcard_eq : (η.vMap '' (A_H ∩ B_H).vertexSet).ncard = separationOrder A_H B_H :=
      hinj.ncard_image
    have hcard_le : (η.vMap '' (A_H ∩ B_H).vertexSet).ncard ≤ separationOrder A B :=
      ncard_le_ncard hsub_img (A ∩ B).vertexSet_finite
    omega
  -- Forward direction on any `(X, Y) ∈ T* \ Z` of order `< θ'`:
  have hfwd : ∀ {X Y : Hypergraph α β} {X_H Y_H : Hypergraph S (Set S)},
      separationOrder X Y < θ' →
      IsRestrictedSeparation H (GM09.deleteVertices G Z) (restrictDeleteVertices η Z hZ_disj)
        X Y X_H Y_H →
      (X, Y) ∈ deleteGraphVerticesTangle G hT_star.finite_V hT_star.finite_E Z T_star θ_star →
      (X_H, Y_H) ∈ T := by
    intro X Y X_H Y_H hordXY hRestrXY hmem_del
    rcases hmem_del.2.2 with ⟨⟨A_star, B_star⟩, hm, hZ_AB, hA_eq, hB_eq⟩
    dsimp only at hm hZ_AB hA_eq hB_eq
    have hsep_star : (Hypergraph.ofGraph G hT_star.finite_V hT_star.finite_E).IsSeparation
        A_star B_star := hT_star.isTangle.isSeparation hm
    have hAB_union : (A_star ∩ B_star).vertexSet = (X ∩ Y).vertexSet ∪ Z := by
      ext v
      simp only [inter_vertexSet, mem_inter_iff, mem_union]
      constructor
      · intro ⟨hvA, hvB⟩
        by_cases hvZ : v ∈ Z
        · exact Or.inr hvZ
        · left
          have hvX : v ∈ (A_star.deleteVertices Z).vertexSet := ⟨hvA, hvZ⟩
          have hvY : v ∈ (B_star.deleteVertices Z).vertexSet := ⟨hvB, hvZ⟩
          rw [hA_eq] at hvX
          rw [hB_eq] at hvY
          exact ⟨hvX, hvY⟩
      · rintro (⟨hvX, hvY⟩ | hvZ)
        · rw [← hA_eq] at hvX
          rw [← hB_eq] at hvY
          exact ⟨hvX.1, hvY.1⟩
        · exact hZ_AB hvZ
    have hZ_fin : Z.Finite := hT_star.finite_V.subset hZ_sub
    have hord_star : separationOrder A_star B_star < θ := by
      have hle_sum : separationOrder A_star B_star ≤ separationOrder X Y + Z.ncard := by
        change (A_star ∩ B_star).vertexSet.ncard ≤ _
        rw [hAB_union]
        exact ncard_union_le (X ∩ Y).vertexSet Z
      omega
    have hRestr_star : IsRestrictedSeparation H G η A_star B_star X_H Y_H := by
      rcases hRestrXY with ⟨hsepH, hVX, hEX, hVY, hEY⟩
      change η.vMap '' X_H.vertexSet = X.vertexSet ∩ V(η.imageGraph) at hVX
      change η.eMap '' X_H.edgeSet = X.edgeSet ∩ E(η.imageGraph) at hEX
      change η.vMap '' Y_H.vertexSet = Y.vertexSet ∩ V(η.imageGraph) at hVY
      change η.eMap '' Y_H.edgeSet = Y.edgeSet ∩ E(η.imageGraph) at hEY
      refine ⟨hsepH, ?_, ?_, ?_, ?_⟩
      · rw [hVX, ← hA_eq]
        ext v
        simp only [Hypergraph.deleteVertices, mem_inter_iff, mem_sdiff]
        exact ⟨fun ⟨⟨hvA, _⟩, hvI⟩ => ⟨hvA, hvI⟩,
          fun ⟨hvA, hvI⟩ => ⟨⟨hvA, hZ_disj.notMem_of_mem_left hvI⟩, hvI⟩⟩
      · rw [hEX, ← hA_eq]
        ext e
        simp only [Hypergraph.deleteVertices, mem_inter_iff, mem_ofPred_eq]
        refine ⟨fun ⟨⟨heA, _⟩, heI⟩ => ⟨heA, heI⟩,
          fun ⟨heA, heI⟩ => ⟨⟨heA, fun v hvZ hincA => ?_⟩, heI⟩⟩
        have hincG : (Hypergraph.ofGraph G hT_star.finite_V hT_star.finite_E).Inc e v :=
          (inc_iff_of_le hsep_star.left_le heA).mp hincA
        obtain ⟨w, hlinkG⟩ := hincG
        have heI_save := heI
        rw [η.imageGraph.edge_mem_iff_exists_isLink] at heI
        obtain ⟨x, y, hlinkI⟩ := heI
        have hlinkG' : G.IsLink e x y := (η.imageGraph_le.isLink_iff heI_save).mp hlinkI
        rcases G.eq_or_eq_of_isLink_of_isLink hlinkG hlinkG' with rfl | rfl
        · exact hZ_disj.notMem_of_mem_left (η.imageGraph.left_mem_of_isLink hlinkI) hvZ
        · exact hZ_disj.notMem_of_mem_left (η.imageGraph.left_mem_of_isLink hlinkI.symm) hvZ
      · rw [hVY, ← hB_eq]
        ext v
        simp only [Hypergraph.deleteVertices, mem_inter_iff, mem_sdiff]
        exact ⟨fun ⟨⟨hvB, _⟩, hvI⟩ => ⟨hvB, hvI⟩,
          fun ⟨hvB, hvI⟩ => ⟨⟨hvB, hZ_disj.notMem_of_mem_left hvI⟩, hvI⟩⟩
      · rw [hEY, ← hB_eq]
        ext e
        simp only [Hypergraph.deleteVertices, mem_inter_iff, mem_ofPred_eq]
        refine ⟨fun ⟨⟨heB, _⟩, heI⟩ => ⟨heB, heI⟩,
          fun ⟨heB, heI⟩ => ⟨⟨heB, fun v hvZ hincB => ?_⟩, heI⟩⟩
        have hincG : (Hypergraph.ofGraph G hT_star.finite_V hT_star.finite_E).Inc e v :=
          (inc_iff_of_le hsep_star.right_le heB).mp hincB
        obtain ⟨w, hlinkG⟩ := hincG
        have heI_save := heI
        rw [η.imageGraph.edge_mem_iff_exists_isLink] at heI
        obtain ⟨x, y, hlinkI⟩ := heI
        have hlinkG' : G.IsLink e x y := (η.imageGraph_le.isLink_iff heI_save).mp hlinkI
        rcases G.eq_or_eq_of_isLink_of_isLink hlinkG hlinkG' with rfl | rfl
        · exact hZ_disj.notMem_of_mem_left (η.imageGraph.left_mem_of_isLink hlinkI) hvZ
        · exact hZ_disj.notMem_of_mem_left (η.imageGraph.left_mem_of_isLink hlinkI.symm) hvZ
    exact (hSpan.isControlling.controls hsep_star hord_star hRestr_star).mp hm
  constructor
  · intro hAB
    exact ⟨hfwd hord hRestr hAB, hord_H⟩
  · rintro ⟨hAB_H, _⟩
    by_contra hnot_AB
    have hord_lt_del : separationOrder A B < θ_star - Z.ncard := by omega
    have hBA : (B, A) ∈
        deleteGraphVerticesTangle G hT_star.finite_V hT_star.finite_E Z T_star θ_star :=
      (hT_del.isTangle.axiom1 hsep hord_lt_del).resolve_left hnot_AB
    have hord_BA : separationOrder B A < θ' := by
      rwa [separationOrder_comm]
    have hRestr_BA : IsRestrictedSeparation H (GM09.deleteVertices G Z)
        (restrictDeleteVertices η Z hZ_disj) B A B_H A_H :=
      ⟨hRestr.1.symm, hRestr.2.2.2.1, hRestr.2.2.2.2, hRestr.2.1, hRestr.2.2.1⟩
    have hBA_H : (B_H, A_H) ∈ T := hfwd hord_BA hRestr_BA hBA
    exact GM10.theorem_2_1_proof hSpan.isControlling.isTangle_H hAB_H hBA_H

/-- Statement of Graph Minors XVI, (8.3) (page 65):
"Let $\Sigma$ be a surface, and let $\tau, \chi, \delta, \lambda, \zeta \ge 0$ and $\psi \ge 3$.
Then there exists $\theta > \zeta$ such that if $\mathcal{T}^*$ is a tangle in a graph $G$, and
$(H, \mathcal{T}, X, Y)$ is an animal with $\chi$ horns and $\delta$ hairs, of strength
$\ge (\theta, \zeta + \tau)$, and $Z \subseteq V(G) \setminus V(H)$ with $X \subseteq Z$ and
$|Z| \le \zeta$, then either:
- there is an animal with $\chi$ horns and $\delta + 1$ hairs of strength $\ge (\psi, \tau)$, or
- there is an $H$-path in $G \setminus Z$ with ends $s_1, s_2$ and there are distinct
  $y_1, y_2 \in Y$ with $d(s_1, y_1), d(s_2, y_2) < \psi$, where $d$ is the metric of
  $\mathcal{T}$, or
- $H, \mathcal{T}_0$ is a $(\lambda, 2\psi)$-level $\Sigma$-span of order $\theta - |Z|$ in
  $G \setminus Z$ with respect to $\mathcal{T}^* \setminus Z$, where $\mathcal{T}_0$ is the
  truncation of $\mathcal{T}$ to order $\theta - |Z|$." -/
def GM16Theorem83Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ τ χ δ lam ζ ψ : ℕ, 3 ≤ ψ →
      ∃ θ : ℕ, ζ < θ ∧
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star θ_span : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (H : Drawing S) (η : SpanEmbedding H G)
          (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (d : Set S → Set S → ℕ) (X : Set α) (Y : Set S) (Z : Set α)
          (hAnim : IsAnimal G T_star θ_star H η θ_span T d X Y χ δ θ (ζ + τ))
          (_ : Z ⊆ V(G)) (hZ_disj : Disjoint V(η.imageGraph) Z)
          (_ : X ⊆ Z) (_ : Z.ncard ≤ ζ),
          HasAnimal S G T_star θ_star χ (δ + 1) ψ τ ∨
          (∃ (P : Graph α β) (s₁ s₂ y₁ y₂ : S),
            s₁ ∈ H.V ∧ s₂ ∈ H.V ∧ y₁ ∈ Y ∧ y₂ ∈ Y ∧ y₁ ≠ y₂ ∧
            IsHPathWithEnds (GM09.deleteVertices G Z) η.imageGraph P
              (η.vMap s₁) (η.vMap s₂) ∧
            d {s₁} {y₁} < ψ ∧ d {s₂} {y₂} < ψ) ∨
          (∃ d₀ : Set S → Set S → ℕ,
            IsLevelSpan (GM09.deleteVertices G Z) H (restrictDeleteVertices η Z hZ_disj)
              (θ_star - Z.ncard) (θ - Z.ncard) lam (2 * ψ)
              (deleteGraphVerticesTangle G hAnim.2.2.1.isControlling.isTangle_star.finite_V
                hAnim.2.2.1.isControlling.isTangle_star.finite_E Z T_star θ_star)
              (GM10.truncation T (θ - Z.ncard)) d₀)

/-! ## Hairs away from a rearrangement -/

omit [T2Space S] in
/-- Graph Minors XVI, proof of (8.3), Claim (10), page 67, cardinality part.
At most one hair can be close to the centre of the rearrangement: otherwise the triangle
inequality contradicts the distance between distinct hairs. -/
theorem theorem_8_3_claim_10_card
    {H : Drawing S} {d : Set S → Set S → ℕ} {Y : Set S} {z : Set S}
    {θ r : ℕ} (hY : Y ⊆ H.V) (hz : z ∈ H.A) (hr : 2 * r ≤ θ)
    (hsep : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ ≠ y₂ → θ ≤ d {y₁} {y₂})
    (hsymm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (htri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A,
      d a c ≤ d a b + d b c) :
    Y.ncard - 1 ≤ {y ∈ Y | r ≤ d z {y}}.ncard := by
  let far : Set S := {y ∈ Y | r ≤ d z {y}}
  have hfin : Y.Finite := H.toHypergraph.vertexSet_finite.subset hY
  have hsub : far ⊆ Y := fun _ h => h.1
  have hsmall : (Y \ far).ncard ≤ 1 := by
    apply (Set.ncard_le_one (hfin.sdiff)).2
    intro a ha b hb
    by_contra hne
    have haA := singleton_mem_A_of_mem_V (hY ha.1)
    have hbA := singleton_mem_A_of_mem_V (hY hb.1)
    have ha_near : d z {a} < r := by
      by_contra hn
      exact ha.2 ⟨ha.1, Nat.le_of_not_gt hn⟩
    have hb_near : d z {b} < r := by
      by_contra hn
      exact hb.2 ⟨hb.1, Nat.le_of_not_gt hn⟩
    have hab := htri {a} haA z hz {b} hbA
    rw [hsymm {a} haA z hz] at hab
    have hdist := hsep a ha.1 b hb.1 hne
    omega
  have hcount := Set.ncard_sdiff' hsub hfin
  change Y.ncard - 1 ≤ far.ncard
  omega

/-! ## Subproofs in the Proof of (7.1) (page 69) -/

omit [T2Space S] in
/-- **Graph Minors XVI, Proof of (7.1), Claim (1)** (page 69):
"(1) *If there is a $\Sigma'$-span of order $\ge \phi$ in $G \setminus X$, for some surface
$\Sigma'$ obtained from $\Sigma$ by adding a handle, then 7.1.1 holds.*" -/
theorem theorem_7_1_claim_1
    {G : Graph α β} {θ_star φ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    (hT : IsGraphTangle G θ_star T_star)
    {X : Set α} (hX_sub : X ⊆ V(G)) (hX_lt : X.ncard < θ_star)
    (hSpan_del : ∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S')
      (H' : Drawing S') (η' : SpanEmbedding H' (GM09.deleteVertices G X)) (θ_span' : ℕ)
      (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
      IsObtainedByAddingHandle S S' ∧
      φ ≤ θ_span' ∧
      IsSigmaSpan (GM09.deleteVertices G X) H' η' (θ_star - X.ncard) θ_span'
        (deleteGraphVerticesTangle G hT.finite_V hT.finite_E X T_star θ_star) T') :
    ∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S')
      (H' : Drawing S') (η' : SpanEmbedding H' G) (θ_span' : ℕ)
      (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
      IsObtainedByAddingHandle S S' ∧
      φ ≤ θ_span' ∧ IsSigmaSpan G H' η' θ_star θ_span' T_star T' := by
  rcases hSpan_del with ⟨S', tS', hT2', H', η', θ_span', T', hHandle, hφ, hSpan'⟩
  exact ⟨S', tS', hT2', H', liftSpanEmbedding η' (G.induce_le sdiff_subset), θ_span', T',
    hHandle, hφ, theorem_7_4_proof G θ_star θ_span' T_star hT X H' η' T' hX_sub hX_lt hSpan'⟩

/-- **Graph Minors XVI, Proof of (7.1), Claim (2)** (page 69):
"(2) *If there is an $H$-path in $G \setminus X$ with ends $s, t$ such that $d'(s, t) \ge \psi$
and $d'(s, y) \ge \psi$ for all $y \in Y$, then 7.1.2 holds.*
*Subproof.* Then $d(s, t) \ge d'(s, t)$, and $d(s, y) \ge d'(s, y)$ for all $y \in Y$, and so
$(H, \mathscr{T}, X, Y \cup \{s\})$ is an animal (in $G$, with respect to $\mathscr{T}^*$) with
$\chi$ horns and $\delta + 1$ hairs, of strength $\ge (\psi, \sigma) \ge (\psi, \tau)$." -/
theorem theorem_7_1_claim_2
    {G : Graph α β} {θ_star θ_span θ ψ τ σ χ δ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {H : Drawing S} {η : SpanEmbedding H G}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {X : Set α} {Y : Set S}
    (hAnim : IsAnimal G T_star θ_star H η θ_span T d X Y χ δ θ σ)
    (hψ_pos : 1 ≤ ψ) (hψ_le : ψ ≤ θ) (hτ_le : τ ≤ σ)
    (hd_le : ∀ a ∈ H.A, ∀ b ∈ H.A, d' a b ≤ d a b)
    (hd_symm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (hd_self : ∀ a ∈ H.A, d a a = 0)
    {P : Graph α β} {s t : S}
    (hs : s ∈ H.V) (ht : t ∈ H.V)
    (hst_ne : s ≠ t)
    (hP : IsHPathWithEnds G η.imageGraph P (η.vMap s) (η.vMap t))
    (hP_disj : Disjoint X V(P))
    (hst : ψ ≤ d' {s} {t})
    (hsy : ∀ y ∈ Y, ψ ≤ d' {s} {y}) :
    HasAnimal S G T_star θ_star χ (δ + 1) ψ τ := by
  rcases hAnim with
    ⟨_, hθ_span, hSpan, hMet, hX_sub, hX_card, hY_sub, hY_card, hHorns, hHairs, hY_dist⟩
  have hs_A : ({s} : Set S) ∈ H.A := singleton_mem_A_of_mem_V hs
  have ht_A : ({t} : Set S) ∈ H.A := singleton_mem_A_of_mem_V ht
  have hs_not_Y : s ∉ Y := by
    intro hsY
    have h1 : ψ ≤ d {s} {s} := (hsy s hsY).trans (hd_le {s} hs_A {s} hs_A)
    rw [hd_self {s} hs_A] at h1
    omega
  have hY_fin : Y.Finite := H.toHypergraph.vertexSet_finite.subset hY_sub
  have hYs_card : (insert s Y).ncard = δ + 1 := by
    rw [ncard_insert_of_notMem hs_not_Y hY_fin, hY_card]
  refine ⟨H, η, θ_span, T, d, X, insert s Y,
    hψ_pos, hψ_le.trans hθ_span, hSpan, hMet, hX_sub, hX_card,
    insert_subset hs hY_sub, hYs_card, ?_, ?_, ?_⟩
  · intro v hvX
    obtain ⟨P_v, u_v, hHorn_v⟩ := hHorns v hvX
    exact ⟨_, _, hHorn_v.mono hψ_le hτ_le⟩
  · intro y hy
    rcases mem_insert_iff.mp hy with rfl | hyY
    · exact ⟨t, P, ht, hst_ne, hP, hP_disj, hst.trans (hd_le {y} hs_A {t} ht_A)⟩
    · obtain ⟨v, Q, hv, hy_ne, hQ, hdisj, hdist⟩ := hHairs y hyY
      exact ⟨v, Q, hv, hy_ne, hQ, hdisj, hψ_le.trans hdist⟩
  · intro y₁ hy₁ y₂ hy₂ hne
    rcases mem_insert_iff.mp hy₁ with rfl | hy₁Y
    · rcases mem_insert_iff.mp hy₂ with rfl | hy₂Y
      · exact absurd rfl hne
      · have hy₂_A : ({y₂} : Set S) ∈ H.A := singleton_mem_A_of_mem_V (hY_sub hy₂Y)
        exact (hsy y₂ hy₂Y).trans (hd_le {y₁} hs_A {y₂} hy₂_A)
    · rcases mem_insert_iff.mp hy₂ with rfl | hy₂Y
      · have hy₁_A : ({y₁} : Set S) ∈ H.A := singleton_mem_A_of_mem_V (hY_sub hy₁Y)
        rw [hd_symm {y₁} hy₁_A {y₂} hs_A]
        exact (hsy y₁ hy₁Y).trans (hd_le {y₂} hs_A {y₁} hy₁_A)
      · exact hψ_le.trans (hY_dist y₁ hy₁Y y₂ hy₂Y hne)

/-- Graph Minors XVI, proof of (8.3), Claim (2), page 65.
A long path either supplies a new hair or has its ends near two distinct existing hairs.
The path is assumed disjoint from the horns, as follows in the paper from `X ⊆ Z`. -/
theorem theorem_8_3_claim_2
    {G : Graph α β} {θ_star θ_span θ ψ τ σ χ δ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {H : Drawing S} {η : SpanEmbedding H G}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {X : Set α} {Y : Set S}
    (hAnim : IsAnimal G T_star θ_star H η θ_span T d X Y χ δ θ σ)
    (hψ : 1 ≤ ψ) (hψθ : ψ ≤ θ) (hτσ : τ ≤ σ)
    (hsymm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (hself : ∀ a ∈ H.A, d a a = 0)
    (htri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A,
      d a c ≤ d a b + d b c)
    {P : Graph α β} {s t : S} (hs : s ∈ H.V) (ht : t ∈ H.V)
    (hP : IsHPathWithEnds G η.imageGraph P (η.vMap s) (η.vMap t))
    (hdisj : Disjoint X V(P)) (hdist : 2 * ψ ≤ d {s} {t}) :
    HasAnimal S G T_star θ_star χ (δ + 1) ψ τ ∨
      ∃ y₁ ∈ Y, ∃ y₂ ∈ Y, y₁ ≠ y₂ ∧ d {s} {y₁} < ψ ∧ d {t} {y₂} < ψ := by
  classical
  have hsA := singleton_mem_A_of_mem_V hs
  have htA := singleton_mem_A_of_mem_V ht
  have hst : s ≠ t := fun h => hP.2.2.1 (congrArg η.vMap h)
  by_cases hfar : ∀ y ∈ Y, ψ ≤ d {s} {y}
  · exact Or.inl (theorem_7_1_claim_2 hAnim hψ hψθ hτσ
      (fun _ _ _ _ => le_rfl) hsymm hself hs ht hst hP hdisj
      (by omega) hfar)
  push Not at hfar
  obtain ⟨y₁, hy₁, hnear₁⟩ := hfar
  by_cases hfar : ∀ y ∈ Y, ψ ≤ d {t} {y}
  · have hrev : IsHPathWithEnds G η.imageGraph P (η.vMap t) (η.vMap s) := by
      rcases hP with ⟨hle, hp, hne, ha, hb, hv, he⟩
      refine ⟨hle, GM09.IsGraphPathWithEnds.symm hp, hne.symm, hb, ha, ?_, he⟩
      rw [hv, Set.pair_comm]
    have hdist' : ψ ≤ d {t} {s} := by
      rw [hsymm {t} htA {s} hsA]
      omega
    exact Or.inl (theorem_7_1_claim_2 hAnim hψ hψθ hτσ
      (fun _ _ _ _ => le_rfl) hsymm hself ht hs hst.symm hrev hdisj hdist' hfar)
  push Not at hfar
  obtain ⟨y₂, hy₂, hnear₂⟩ := hfar
  refine Or.inr ⟨y₁, hy₁, y₂, hy₂, ?_, hnear₁, hnear₂⟩
  intro heq
  subst y₂
  have hyA := singleton_mem_A_of_mem_V (hAnim.2.2.2.2.2.2.1 hy₁)
  have hbound := htri {s} hsA {y₁} hyA {t} htA
  rw [hsymm {y₁} hyA {t} htA] at hbound
  omega

end GraphMinor.GM16
