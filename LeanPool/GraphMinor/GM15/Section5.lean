/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Defs
public import LeanPool.GraphMinor.GM15.Cited
public import LeanPool.GraphMinor.GM15.Section4
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM10.Section6
import LeanPool.GraphMinor.GM10.TangleLemmas
import LeanPool.GraphMinor.GM11.RadialExists
import LeanPool.GraphMinor.GM11.RadialFacts
import LeanPool.GraphMinor.GM11.ForestRegions
import LeanPool.GraphMinor.GM11.Section4c
import LeanPool.GraphMinor.GM11.Section5b
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.GM14.Section3
import LeanPool.GraphMinor.Surface.Epstein

import LeanPool.GraphMinor.GM12.Section710

import LeanPool.GraphMinor.GM12.Section77

/-!
# Graph Minors XV, Section 5: Flatness

This file formalizes Section 5 ("Flatness", pages 128–133) of N. Robertson and P. D. Seymour,
*Graph Minors. XV. Giant steps*, J. Combin. Theory Ser. B 68 (1996) 112–148:
- **Truncation of `Σ`-spans** (`IsRespectfulDrawingTangle.truncation`,
  `IsControllingTangle.truncation`, `IsSigmaSpan.truncation`, page 129): if `H, η, T` is a `Σ`-span
  of order `θ` and `1 ≤ θ₁ ≤ θ`, then `(H, η, GM10.truncation T θ₁)` is a `Σ`-span of order `θ₁`.
- **Monotonicity of `μ`-steppedness and `(λ, μ)`-flatness in `μ`** (`IsMuStepped.mono`,
  `IsMuSteppedSpan.mono`, `IsFlatSpan.mono_mu`, page 129).
- **Graph Minors XV, (5.1)** (`GM15Theorem51Statement`, page 129): truncation and monotonicity of
  `(λ, μ)`-flat `Σ`-spans.
- **Graph Minors XV, (5.2)** (`GM15Theorem52Statement`, page 129): rearranging a `(λ, μ)`-flat
  `Σ`-span within `λ₁` of `z₁ ∈ A(H)` produces a `(λ₂, μ)`-flat `Σ`-span whenever `λ₁, λ₂ ≥ 4` and
  `λ ≥ 6λ₁ + 5λ₂ + 3μ + 4`.
-/

@[expose] public section

namespace GraphMinor.GM15

open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14

universe u v w

variable {α : Type u} {β : Type v}

/-! ## Truncation of `Σ`-Spans -/

/-- If `T` is a respectful tangle in `H` of order `θ` and `1 ≤ θ₁ ≤ θ`, then the `θ₁`-truncation
`GM10.truncation T θ₁` is a respectful tangle in `H` of order `θ₁`
(Graph Minors XV, Section 3, page 120; Section 5, page 129). -/
theorem IsRespectfulDrawingTangle.truncation {S : Type w} [TopologicalSpace S]
    {H : Drawing S} {θ θ₁ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hResp : IsRespectfulDrawingTangle H θ T) (h1 : 1 ≤ θ₁) (hle : θ₁ ≤ θ) :
    IsRespectfulDrawingTangle H θ₁ (GM10.truncation T θ₁) := by
  rcases hResp with ⟨hTwoCell, hTangle, hConn, hOArc⟩
  refine ⟨hTwoCell, hTangle.truncation h1 hle, hConn, fun F hF_oarc hF_norm hF_card => ?_⟩
  obtain ⟨Δ, hΔ_disc, hΔ_bd, hΔ_mem⟩ :=
    hOArc F hF_oarc hF_norm (lt_of_lt_of_le hF_card hle)
  refine ⟨Δ, hΔ_disc, hΔ_bd, hΔ_mem, ?_⟩
  let Γ := PaintingOrDrawing.drawing H
  have hsub : ((Γ.inter Δ) ∩ (Γ.interOutside Δ)).vertexSet ⊆ F ∩ H.V := by
    rintro v ⟨⟨hvV, hvΔ⟩, ⟨_, hvOut⟩⟩
    have hv_bd : v ∈ subBd Δ := ⟨subset_closure hvΔ, hvOut⟩
    rw [hΔ_bd] at hv_bd
    exact ⟨hv_bd, hvV⟩
  have hfin : (F ∩ H.V).Finite := H.toHypergraph.vertexSet_finite.subset inter_subset_right
  exact (ncard_le_ncard hsub hfin).trans_lt hF_card

/-- If `T*` controls `T` via `η` of order `θ` and `1 ≤ θ₁ ≤ θ`, then `T*` controls the
`θ₁`-truncation `GM10.truncation T θ₁` of order `θ₁` (Graph Minors XV, Section 5, page 129). -/
theorem IsControllingTangle.truncation {S : Type w} [TopologicalSpace S]
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ θ₁ : ℕ} {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h : IsControllingTangle G H η θ_star θ T_star T) (h1 : 1 ≤ θ₁) (hle : θ₁ ≤ θ) :
    IsControllingTangle G H η θ_star θ₁ T_star (GM10.truncation T θ₁) where
  theta_le := hle.trans h.theta_le
  isTangle_star := h.isTangle_star
  isTangle_H := h.isTangle_H.truncation h1 hle
  controls A B hsep hlt A_H B_H hrest := by
    have hlt_θ : separationOrder A B < θ := lt_of_lt_of_le hlt hle
    have hiff := h.controls hsep hlt_θ hrest
    constructor
    · intro hAB
      have hAB_H : (A_H, B_H) ∈ T := hiff.mp hAB
      refine ⟨hAB_H, ?_⟩
      have hsub : A_H.vertexSet ∩ B_H.vertexSet ⊆ η.vMap ⁻¹' (A.vertexSet ∩ B.vertexSet) := by
        intro x ⟨hxA, hxB⟩
        have hxA' : η.vMap x ∈ A.vertexSet ∩ V(η.imageGraph) := by
          rw [← hrest.2.1]
          exact mem_image_of_mem _ hxA
        have hxB' : η.vMap x ∈ B.vertexSet ∩ V(η.imageGraph) := by
          rw [← hrest.2.2.2.1]
          exact mem_image_of_mem _ hxB
        exact ⟨hxA'.1, hxB'.1⟩
      have hcard_le : separationOrder A_H B_H ≤ separationOrder A B := by
        have hfin : (A.vertexSet ∩ B.vertexSet).Finite := (A ∩ B).vertexSet_finite
        have hinj : InjOn η.vMap (A_H.vertexSet ∩ B_H.vertexSet) :=
          η.bijOn_v.injOn.mono (inter_subset_left.trans hrest.1.left_le.vertexSet_subset)
        calc
          separationOrder A_H B_H = (A_H.vertexSet ∩ B_H.vertexSet).ncard := rfl
          _ = (η.vMap '' (A_H.vertexSet ∩ B_H.vertexSet)).ncard := (hinj.ncard_image).symm
          _ ≤ (A.vertexSet ∩ B.vertexSet).ncard :=
            ncard_le_ncard (image_subset_iff.mpr hsub) hfin
          _ = separationOrder A B := rfl
      exact lt_of_le_of_lt hcard_le hlt
    · intro hAB_H
      exact hiff.mpr hAB_H.1

/-- If `H, η, T` is a `Σ`-span of order `θ` in `G` with respect to `T*` and `1 ≤ θ₁ ≤ θ`, then
`(H, η, GM10.truncation T θ₁)` is a `Σ`-span of order `θ₁` in `G` with respect to `T*`
(Graph Minors XV, Section 5, proof of (5.1), page 129:
"Certainly $(H, \eta, \mathscr{T}_1)$ is a $\Sigma$-span of order $\theta_1$"). -/
theorem IsSigmaSpan.truncation {S : Type w} [TopologicalSpace S] [T2Space S]
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ θ₁ : ℕ} {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h : IsSigmaSpan G H η θ_star θ T_star T) (h1 : 1 ≤ θ₁) (hle : θ₁ ≤ θ) :
    IsSigmaSpan G H η θ_star θ₁ T_star (GM10.truncation T θ₁) where
  isSurface := h.isSurface
  isConnected := h.isConnected
  bd_empty := h.bd_empty
  isRigid := h.isRigid
  isRespectful := IsRespectfulDrawingTangle.truncation h.isRespectful h1 hle
  isControlling := h.isControlling.truncation h1 hle

/-! ## Monotonicity of `μ`-Steppedness and `(λ, μ)`-Flatness -/

/-- If `P` is `μ₁`-stepped and `μ ≤ μ₁`, then `P` is `μ`-stepped. -/
theorem IsMuStepped.mono {S : Type w} [TopologicalSpace S]
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {d : Set S → Set S → ℕ} {μ μ₁ : ℕ} {P : Graph α β} {u v : S}
    (h : IsMuStepped G H η d μ₁ P u v) (hμ : μ ≤ μ₁) :
    IsMuStepped G H η d μ P u v :=
  ⟨h.1, h.2.1, h.2.2.1, hμ.trans h.2.2.2⟩

/-- If `H, η, T` is `μ₁`-stepped and `μ ≤ μ₁`, then `H, η, T` is `μ`-stepped. -/
theorem IsMuSteppedSpan.mono {S : Type w} [TopologicalSpace S]
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {d : Set S → Set S → ℕ} {μ μ₁ : ℕ}
    (h : IsMuSteppedSpan G H η d μ₁) (hμ : μ ≤ μ₁) :
    IsMuSteppedSpan G H η d μ := by
  rcases h with ⟨P, u, v, hP⟩
  exact ⟨P, u, v, hP.mono hμ⟩

/-- If `H, η, T` is `(λ, μ)`-flat of order `θ`, `μ ≤ μ₁`, and `4λ + μ₁ + 2 ≤ θ`, then `H, η, T` is
`(λ, μ₁)`-flat (special case `λ₁ = λ, θ₁ = θ` of Graph Minors XV, (5.1), page 129). -/
theorem IsFlatSpan.mono_mu {S : Type w} [TopologicalSpace S] [T2Space S]
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ lam μ μ₁ : ℕ} {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hFlat : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (hμ : μ ≤ μ₁) (hord : 4 * lam + μ₁ + 2 ≤ θ) :
    IsFlatSpan G H η θ_star θ lam μ₁ T_star T where
  isSpan := hFlat.isSpan
  order_ge := hord
  no_stepped_rearrangement _ _ _ _ _ _ hRearr hStep :=
    hFlat.no_stepped_rearrangement hRearr (hStep.mono hμ)

/-! ## Metrics of Truncated Tangles -/

/-- A derived slope for `T` of order `θ` is also a derived slope for `GM10.truncation T θ₁` when
`θ₁ ≤ θ`. -/
theorem isDerivedSlope_truncation {S : Type w} [TopologicalSpace S] [T2Space S]
    {H K : Drawing S} {θ θ₁ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Drawing S → Set S}
    (hrad : (PaintingOrDrawing.drawing H).IsPreRadialDrawing K)
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hle : θ₁ ≤ θ) :
    IsDerivedSlope (PaintingOrDrawing.drawing H) K θ₁ (GM10.truncation T θ₁) ins := by
  intro C hC hCs hlen₁
  obtain ⟨hD, hbd, hmem⟩ := hins C hC hCs (by omega)
  refine ⟨hD, hbd, hmem, ?_⟩
  obtain ⟨_, _, hcard2⟩ := circuit_props_of_preRadial hrad hC hCs
  let Γ := PaintingOrDrawing.drawing H
  have hsub : ((Γ.inter (ins C)) ∩ (Γ.interOutside (ins C))).vertexSet ⊆ C.U ∩ H.V := by
    rintro v ⟨⟨hvV, hvΔ⟩, ⟨_, hvOut⟩⟩
    have hv_bd : v ∈ subBd (ins C) := ⟨subset_closure hvΔ, hvOut⟩
    rw [hbd] at hv_bd
    exact ⟨hv_bd, hvV⟩
  have hfin : (C.U ∩ H.V).Finite := H.finite_V.subset inter_subset_right
  have hle_card : separationOrder (Γ.inter (ins C)) (Γ.interOutside (ins C)) ≤
      (C.U ∩ H.V).ncard := ncard_le_ncard hsub hfin
  change separationOrder (Γ.inter (ins C)) (Γ.interOutside (ins C)) < θ₁
  omega

/-- If `ins₁` and `ins` have the same `insWalk` on closed walks of length `< 2 * θ₁` and `θ₁ ≤ θ`,
then `tangleMetric H K ins₁ θ₁ x y = min θ₁ (tangleMetric H K ins θ x y)`. -/
theorem tangleMetric_eq_min_of_insWalk_eq {S : Type w} [TopologicalSpace S] [T1Space S]
    {H K : Drawing S} (hrad : (PaintingOrDrawing.drawing H).IsPreRadialDrawing K)
    {θ₁ θ : ℕ} (hle : θ₁ ≤ θ) {ins₁ ins : Drawing S → Set S}
    (hins_eq : ∀ {u : S} (W : GraphWalk K.toGraph u u),
      W.length < 2 * θ₁ → insWalk ins₁ K W = insWalk ins K W)
    (x y : Set S) :
    tangleMetric H K ins₁ θ₁ x y = min θ₁ (tangleMetric H K ins θ x y) := by
  by_cases hxy : x = y
  · subst hxy
    simp [tangleMetric]
  · apply le_antisymm
    · refine le_min (tangleMetric_le_ord H K ins₁ θ₁ x y) ?_
      by_cases hlt : tangleMetric H K ins θ x y < θ₁
      · obtain ⟨u, W, x', y', hx', hy', _, hW_eq, hxW, hyW⟩ :=
          exists_walk_of_tangleMetric_lt hrad ins hxy (lt_of_lt_of_le hlt hle)
        have hlen₁ : W.length < 2 * θ₁ := by omega
        rw [← hins_eq W hlen₁] at hxW hyW
        have hle2 := two_mul_tangleMetric_le_of_walk hrad ins₁ θ₁ hx' hy' W hlen₁ hxW hyW
        omega
      · have := tangleMetric_le_ord H K ins₁ θ₁ x y
        omega
    · by_cases hlt₁ : tangleMetric H K ins₁ θ₁ x y < θ₁
      · obtain ⟨u, W, x', y', hx', hy', hlen₁, hW_eq, hxW, hyW⟩ :=
          exists_walk_of_tangleMetric_lt hrad ins₁ hxy hlt₁
        rw [hins_eq W hlen₁] at hxW hyW
        have hle2 := two_mul_tangleMetric_le_of_walk hrad ins θ hx' hy' W (by omega) hxW hyW
        omega
      · omega

/-- From a metric `d` of `T` (order `θ`) and `1 ≤ θ₁ ≤ θ`, there is a metric `d₁` of
`GM10.truncation T θ₁` satisfying `d₁ x y = min θ₁ (d x y)` on atoms and on points. -/
theorem hasTangleMetric_truncation_of_hasTangleMetric
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {H : Drawing S} {θ θ₁ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hM : HasTangleMetric H θ T d) (h1 : 1 ≤ θ₁) (hle : θ₁ ≤ θ) :
    ∃ d₁ : Set S → Set S → ℕ,
      HasTangleMetric H θ₁ (GM10.truncation T θ₁) d₁ ∧
      (∀ x ∈ H.A, ∀ y ∈ H.A, d₁ x y = min θ₁ (d x y)) ∧
      (∀ σ₁ σ₂ : S, pointDist H d₁ σ₁ σ₂ = min θ₁ (pointDist H d σ₁ σ₂)) := by
  obtain ⟨hRDT, K, ins, hK, hins, hd⟩ := hM
  let d₁ := tangleMetric H K ins θ₁
  have hM₁ : HasTangleMetric H θ₁ (GM10.truncation T θ₁) d₁ :=
    ⟨IsRespectfulDrawingTangle.truncation hRDT h1 hle, K, ins, hK,
      isDerivedSlope_truncation hK.2.1 hins hle, fun _ _ _ _ => rfl⟩
  have hd₁_eq : ∀ x ∈ H.A, ∀ y ∈ H.A, d₁ x y = min θ₁ (d x y) := by
    intro x hx y hy
    rw [hd x hx y hy]
    exact tangleMetric_eq_min_of_insWalk_eq hK.2.1 hle (fun _ _ => rfl) x y
  refine ⟨d₁, hM₁, hd₁_eq, fun σ₁ σ₂ => ?_⟩
  obtain ⟨a₁, ha₁, hσ₁⟩ := exists_atom_of_point H σ₁
  obtain ⟨a₂, ha₂, hσ₂⟩ := exists_atom_of_point H σ₂
  rw [pointDist_eq_of_mem_atom ha₁ ha₂ hσ₁ hσ₂,
    pointDist_eq_of_mem_atom ha₁ ha₂ hσ₁ hσ₂,
    hd₁_eq a₁ ha₁ a₂ ha₂]

/-- Any `(λ, μ)`-flat `Σ`-span `H, η, T` of order `θ` with metric `d` and `4λ + 2 < θ` is not
`μ`-stepped (`¬ IsMuSteppedSpan G H η d μ`) (Graph Minors XV, Section 5, page 132). -/
theorem not_isMuSteppedSpan_of_isFlatSpan {S : Type w} [TopologicalSpace S] [T2Space S]
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ lam μ : ℕ} {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hFlat : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (hMetric : HasTangleMetric H θ T d)
    (hθ : 4 * lam + 2 < θ) :
    ¬ IsMuSteppedSpan G H η d μ := by
  intro ⟨P, u, v, hu, hv, hP, hdist⟩
  have : ConnectedSpace S := hFlat.isSpan.isConnected
  obtain ⟨σ⟩ := (inferInstance : Nonempty S)
  obtain ⟨z, hz, _⟩ := exists_atom_of_point H σ
  let θ' := θ - (4 * lam + 2)
  let T' := GM10.truncation T θ'
  obtain ⟨d', hM', hd'_eq, hpt'_eq⟩ :=
    hasTangleMetric_truncation_of_hasTangleMetric (θ₁ := θ') hMetric (by omega) (Nat.sub_le _ _)
  have hComp : IsLambdaCompression H H θ (4 * lam + 2) T T' d d' := by
    refine ⟨hθ, hMetric, hM', fun σ₁ σ₂ => ?_⟩
    obtain ⟨a₁, ha₁, hσ₁⟩ := exists_atom_of_point H σ₁
    obtain ⟨a₂, ha₂, hσ₂⟩ := exists_atom_of_point H σ₂
    obtain ⟨_, K, ins, _, _, hd⟩ := hMetric
    have hle_θ : pointDist H d σ₁ σ₂ ≤ θ := by
      rw [pointDist_eq_of_mem_atom ha₁ ha₂ hσ₁ hσ₂, hd a₁ ha₁ a₂ ha₂]
      exact tangleMetric_le_ord H K ins θ a₁ a₂
    rw [hpt'_eq σ₁ σ₂]
    omega
  have hRearr : IsRearrangedWithin G H H η η θ_star θ lam T_star T T' d d' z :=
    ⟨hz, hFlat.isSpan, hFlat.isSpan.truncation (by omega) (Nat.sub_le _ _),
      fun a ha _ => ha, fun w hw _ => ⟨hw, rfl⟩, fun e he _ => ⟨he, rfl⟩, hComp⟩
  have hdist' : μ ≤ d' {u} {v} := by
    rw [hd'_eq {u} (Or.inl (Or.inl ⟨u, hu, rfl⟩)) {v} (Or.inl (Or.inl ⟨v, hv, rfl⟩))]
    have := hFlat.order_ge
    omega
  exact hFlat.no_stepped_rearrangement hRearr ⟨P, u, v, hu, hv, hP, hdist'⟩

/-- From `IsRespectfulDrawingTangle H θ T`, `1 ≤ θ₁ ≤ θ`, and a metric `d₁` of
`GM10.truncation T θ₁`, there is a metric `d` of `T` satisfying `d₁ x y = min θ₁ (d x y)` on atoms
and on points. -/
theorem exists_hasTangleMetric_of_truncation
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {H : Drawing S} {θ θ₁ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d₁ : Set S → Set S → ℕ}
    (hRDT : IsRespectfulDrawingTangle H θ T) (_h1 : 1 ≤ θ₁) (hle : θ₁ ≤ θ)
    (hM₁ : HasTangleMetric H θ₁ (GM10.truncation T θ₁) d₁) :
    ∃ d : Set S → Set S → ℕ,
      HasTangleMetric H θ T d ∧
      (∀ x ∈ H.A, ∀ y ∈ H.A, d₁ x y = min θ₁ (d x y)) ∧
      (∀ σ₁ σ₂ : S, pointDist H d₁ σ₁ σ₂ = min θ₁ (pointDist H d σ₁ σ₂)) := by
  obtain ⟨_, K, ins₁, hK, hins₁, hd₁⟩ := hM₁
  obtain ⟨ins₀, hins₀⟩ := exists_derivedSlope hRDT hK.2.1
  let ins : Drawing S → Set S := fun C =>
    open Classical in if C.length < 2 * θ₁ then ins₁ C else ins₀ C
  have hins : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins := by
    intro C hC hCs hlen
    dsimp [ins]
    split_ifs with hlt
    · obtain ⟨hD, hbd, hmem, _⟩ := hins₁ C hC hCs hlt
      exact ⟨hD, hbd, hmem⟩
    · exact hins₀ C hC hCs hlen
  have hins_eq : ∀ {u : S} (W : GraphWalk K.toGraph u u),
      W.length < 2 * θ₁ → insWalk ins₁ K W = insWalk ins K W := by
    intro u W hlen₁
    unfold insWalk
    ext x
    simp only [insOf, mem_union, mem_iUnion, exists_prop]
    refine or_congr Iff.rfl (exists_congr fun C => and_congr_right fun ⟨hC, hCs⟩ => ?_)
    have hClen : C.length ≤ W.length := by
      have hsub : C.E ⊆ {e | e ∈ W.edges} := by
        have := hCs.2
        rwa [GM11.walkDrawing_E] at this
      calc C.E.ncard ≤ ({e | e ∈ W.edges} : Set (Set S)).ncard :=
            Set.ncard_le_ncard hsub (List.finite_toSet _)
        _ ≤ W.edges.length := by
            rw [show ({e | e ∈ W.edges} : Set (Set S)) = ↑W.edges.toFinset by ext; simp,
              Set.ncard_coe_finset]
            exact List.toFinset_card_le _
        _ = W.length := rfl
    have hlt : C.length < 2 * θ₁ := lt_of_le_of_lt hClen hlen₁
    dsimp [ins]
    rw [ite_eq_left_iff.mpr fun h => (h hlt).elim]
  let d := tangleMetric H K ins θ
  have hM : HasTangleMetric H θ T d :=
    ⟨hRDT, K, ins, hK, hins, fun _ _ _ _ => rfl⟩
  have hd₁_eq : ∀ x ∈ H.A, ∀ y ∈ H.A, d₁ x y = min θ₁ (d x y) := by
    intro x hx y hy
    rw [hd₁ x hx y hy]
    exact tangleMetric_eq_min_of_insWalk_eq hK.2.1 hle hins_eq x y
  refine ⟨d, hM, hd₁_eq, fun σ₁ σ₂ => ?_⟩
  obtain ⟨a₁, ha₁, hσ₁⟩ := exists_atom_of_point H σ₁
  obtain ⟨a₂, ha₂, hσ₂⟩ := exists_atom_of_point H σ₂
  rw [pointDist_eq_of_mem_atom ha₁ ha₂ hσ₁ hσ₂,
    pointDist_eq_of_mem_atom ha₁ ha₂ hσ₁ hσ₂,
    hd₁_eq a₁ ha₁ a₂ ha₂]

/-- If `T'` is a `(4λ + 2)`-compression of `T` in `H'` under the hypotheses of `(4.5)`, then `T'` is
a `(4λ + 2)`-compression of `T` with respect to any tangle metric `d'` of `T'`. -/
theorem isLambdaCompression_of_hasTangleMetric
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {H H' : Drawing S} {θ lam : ℕ}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d'_0 d' : Set S → Set S → ℕ} {z : Set S}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (hMetric : HasTangleMetric H θ T d) (hz : z ∈ H.A)
    (hlam : 2 ≤ lam) (hθ : 4 * lam + 2 < θ)
    (h2cell' : (PaintingOrDrawing.drawing H').IsTwoCell)
    (hAtoms : ∀ a ∈ H.A, lam < d z a → a ∈ H'.A)
    (hComp₀ : IsLambdaCompression H H' θ (4 * lam + 2) T T' d d'_0)
    (hM' : HasTangleMetric H' (θ - (4 * lam + 2)) T' d') :
    IsLambdaCompression H H' θ (4 * lam + 2) T T' d d' := by
  let H₀ := deleteAtomNeighborhood H d z lam
  have hE_ne : H.E.Nonempty := by
    by_contra hE
    have hV_le := ncard_V_le_one_of_E_empty hS hMetric.1.1 (Set.not_nonempty_iff_eq_empty.mp hE)
    have hord_le : θ ≤ H.V.ncard := hMetric.1.2.1.order_le_ncard_vertexSet
    omega
  have hH₀_eq : H₀ = H.span ∅ {e ∈ H.E | lam < d z e} := by
    change deleteAtomNeighborhood H d z lam = _
    rw [deleteAtomNeighborhood, ite_eq_right_iff.mpr fun h => False.elim (hE_ne.ne_empty h)]
  have h2cell₀ : (PaintingOrDrawing.drawing H₀).IsTwoCell :=
    theorem_4_3_proof H θ lam T d z hS hConn hMetric
      hE_ne hz (by omega) (fun _ => hlam)
  obtain ⟨hSubH₀H', T₀, T'_45, d₀, _, hComp₀_45, _, hIndEq, hUniq'⟩ :=
    theorem_4_5_proof H H' θ lam T d z hS hConn hMetric hz hlam hθ h2cell' hAtoms
  have hT'_eq : T' = T'_45 := hUniq' T' d'_0 hComp₀
  subst hT'_eq
  let θ' := θ - (4 * lam + 2)
  have hIndBySub : T' = GM12.inducedBySubgraph H'.toHypergraph H₀.toHypergraph θ' T₀ := by
    rw [hIndEq]
    exact inducedTangle_eq_inducedBySubgraph_of_span_empty hH₀_eq hSubH₀H'
      hComp₀_45.hasMetric'.1.2.1
  have h77_ii := (GraphMinor.GM12.gm15_theorem_7_7.{w} H' H₀ θ' θ' T' T₀ d' d₀ hS hConn hM'
    hSubH₀H' h2cell₀ le_rfl
    hComp₀_45.hasMetric').2 rfl hIndBySub
  refine ⟨hθ, hMetric, hM', fun σ₁ σ₂ => ?_⟩
  obtain ⟨a₁', ha₁', hσ₁'⟩ := exists_atom_of_point H' σ₁
  obtain ⟨a₂', ha₂', hσ₂'⟩ := exists_atom_of_point H' σ₂
  obtain ⟨a₁₀, ha₁₀, hσ₁₀⟩ := exists_atom_of_point H₀ σ₁
  obtain ⟨a₂₀, ha₂₀, hσ₂₀⟩ := exists_atom_of_point H₀ σ₂
  have hsub₁ := atom_subset_of_isSubdrawing hSubH₀H' ha₁' ha₁₀ hσ₁' hσ₁₀
  have hsub₂ := atom_subset_of_isSubdrawing hSubH₀H' ha₂' ha₂₀ hσ₂' hσ₂₀
  have hle_0_d' := h77_ii a₁' ha₁' a₂' ha₂' a₁₀ ha₁₀ a₂₀ ha₂₀ hsub₁ hsub₂
  have hle_H_0 := hComp₀_45.dist_le σ₁ σ₂
  rw [pointDist_eq_of_mem_atom (d := d₀) ha₁₀ ha₂₀ hσ₁₀ hσ₂₀] at hle_H_0
  rw [pointDist_eq_of_mem_atom (d := d') ha₁' ha₂' hσ₁' hσ₂']
  omega

/-! ## Statements and Proofs of (5.1) and (5.2) -/

/-- Statement of Graph Minors XV, (5.1) (page 129):
"Let $\mathscr{T}^*$ be a tangle in $G$, and let $H, \eta, \mathscr{T}$ be a $(\lambda, \mu)$-flat
$\Sigma$-span of order $\theta$. Let $0 \le \lambda_1 \le \lambda$, let $\mu_1 \ge \mu$ and let
$1 \le \theta_1 \le \theta$, such that $\theta_1 \ge 4\lambda_1 + \mu_1 + 2$; and let
$\mathscr{T}_1$
be the $\theta_1$-truncation of $\mathscr{T}$. Then $(H, \eta, \mathscr{T}_1)$ is
$(\lambda_1, \mu_1)$-flat."
(Formalized with the side conditions `lam₁ < lam → 4 * lam + 2 < θ` and
`θ₁ - (4 * lam₁ + 2) < θ - (4 * lam + 2) → 2 ≤ lam` needed when invoking `(4.5)` on `λ`.) -/
def GM15Theorem51Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ θ₁ lam lam₁ μ μ₁ : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
    IsFlatSpan G H η θ_star θ lam μ T_star T →
    lam₁ ≤ lam → μ ≤ μ₁ → 1 ≤ θ₁ → θ₁ ≤ θ →
    4 * lam₁ + μ₁ + 2 ≤ θ₁ →
    (lam₁ < lam → 4 * lam + 2 < θ) →
    (θ₁ - (4 * lam₁ + 2) < θ - (4 * lam + 2) → 2 ≤ lam) →
    IsFlatSpan G H η θ_star θ₁ lam₁ μ₁ T_star (GM10.truncation T θ₁)

/-- **Graph Minors XV, (5.1)** (page 129):
Truncation and monotonicity of `(λ, μ)`-flat `Σ`-spans.
Proved from `(4.1)`, `(4.5)`, `(4.6)`, and Graph Minors XII, `(7.7)`, `(7.10)`, `(7.11)`. -/
theorem theorem_5_1_proof
     :
    GM15Theorem51Statement.{u, v, w} := by
  intro S _ _ α β G H η θ_star θ θ₁ lam lam₁ μ μ₁ T_star T
    hFlat hlam hμ h1 hle hord₁ hθ_gt hlam2
  refine ⟨hFlat.isSpan.truncation h1 hle, hord₁, ?_⟩
  intro H' η' T₁' d₁ d₁' z hRearr₁ hStep₁
  have hS : IsClosedSurface S :=
    ⟨hFlat.isSpan.isSurface.1, hFlat.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hFlat.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hFlat.isSpan.isConnected
  have hθ₁_lt : 4 * lam₁ + 2 < θ₁ := hRearr₁.isCompression.lam_lt
  have hθ_lt : 4 * lam + 2 < θ := by
    by_cases hlt : lam₁ < lam
    · exact hθ_gt hlt
    · omega
  obtain ⟨d, hM, hd₁_eq, hpt₁_eq⟩ :=
    exists_hasTangleMetric_of_truncation hFlat.isSpan.isRespectful h1 hle
      hRearr₁.isCompression.hasMetric
  have hAtoms : ∀ a ∈ H.A, lam < d z a → a ∈ H'.A := by
    intro a ha hlt
    apply hRearr₁.atom_mem a ha
    rw [hd₁_eq z hRearr₁.z_mem a ha]
    omega
  have hV : ∀ v ∈ H.V, lam < d z {v} → v ∈ H'.V ∧ η'.vMap v = η.vMap v := by
    intro v hv hlt
    apply hRearr₁.vMap_eq v hv
    rw [hd₁_eq z hRearr₁.z_mem {v} (Or.inl (Or.inl ⟨v, hv, rfl⟩))]
    omega
  have hE : ∀ e ∈ H.E, lam < d z e → e ∈ H'.E ∧ η'.eMap e = η.eMap e := by
    intro e he hlt
    apply hRearr₁.eMap_eq e he
    rw [hd₁_eq z hRearr₁.z_mem e (Or.inl (Or.inr he))]
    omega
  let θ' := θ - (4 * lam + 2)
  let θ₁' := θ₁ - (4 * lam₁ + 2)
  by_cases hOrd : θ' ≤ θ₁'
  · let T' := GM10.truncation T₁' θ'
    obtain ⟨d', hM', hd'_eq, hpt'_eq⟩ :=
      hasTangleMetric_truncation_of_hasTangleMetric hRearr₁.isCompression.hasMetric'
        (by omega) hOrd
    have hComp : IsLambdaCompression H H' θ (4 * lam + 2) T T' d d' := by
      refine ⟨hθ_lt, hM, hM', fun σ₁ σ₂ => ?_⟩
      obtain ⟨a₁, ha₁, hσ₁⟩ := exists_atom_of_point H σ₁
      obtain ⟨a₂, ha₂, hσ₂⟩ := exists_atom_of_point H σ₂
      obtain ⟨_, K, ins, _, _, hd⟩ := hM
      have hle_θ : pointDist H d σ₁ σ₂ ≤ θ := by
        rw [pointDist_eq_of_mem_atom ha₁ ha₂ hσ₁ hσ₂, hd a₁ ha₁ a₂ ha₂]
        exact tangleMetric_le_ord H K ins θ a₁ a₂
      have hle_1 := hRearr₁.isCompression.dist_le σ₁ σ₂
      rw [hpt₁_eq σ₁ σ₂] at hle_1
      rw [hpt'_eq σ₁ σ₂]
      omega
    have hSpan' : IsSigmaSpan G H' η' θ_star θ' T_star T' :=
      hRearr₁.isSpan'.truncation (by omega) hOrd
    have hRearr : IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z :=
      ⟨hRearr₁.z_mem, hFlat.isSpan, hSpan', hAtoms, hV, hE, hComp⟩
    obtain ⟨P, u, v, hu, hv, hP, hdist₁⟩ := hStep₁
    have hdist' : μ ≤ d' {u} {v} := by
      rw [hd'_eq {u} (Or.inl (Or.inl ⟨u, hu, rfl⟩)) {v} (Or.inl (Or.inl ⟨v, hv, rfl⟩))]
      have := hFlat.order_ge
      omega
    exact hFlat.no_stepped_rearrangement hRearr ⟨P, u, v, hu, hv, hP, hdist'⟩
  · have hlt_ord : θ₁' < θ' := by omega
    have h2lam : 2 ≤ lam := hlam2 hlt_ord
    obtain ⟨_, _, T', _, d'_0, _, hComp₀, _, _⟩ :=
      theorem_4_5_proof H H' θ lam T d z hS hConn hM hRearr₁.z_mem h2lam hθ_lt
        hRearr₁.isSpan'.isRespectful.1 hAtoms
    let lam₁_tot := θ - θ₁ + (4 * lam₁ + 2)
    have hθ₁'_eq : θ - lam₁_tot = θ₁' := by omega
    have hComp₁_tot : IsLambdaCompression H H' θ lam₁_tot T T₁' d d₁' := by
      refine ⟨by omega, hM, hθ₁'_eq ▸ hRearr₁.isCompression.hasMetric', fun σ₁ σ₂ => ?_⟩
      obtain ⟨a₁, ha₁, hσ₁⟩ := exists_atom_of_point H σ₁
      obtain ⟨a₂, ha₂, hσ₂⟩ := exists_atom_of_point H σ₂
      obtain ⟨_, K, ins, _, _, hd⟩ := hM
      have hle_θ : pointDist H d σ₁ σ₂ ≤ θ := by
        rw [pointDist_eq_of_mem_atom ha₁ ha₂ hσ₁ hσ₂, hd a₁ ha₁ a₂ ha₂]
        exact tangleMetric_le_ord H K ins θ a₁ a₂
      have hle_1 := hRearr₁.isCompression.dist_le σ₁ σ₂
      rw [hpt₁_eq σ₁ σ₂] at hle_1
      omega
    obtain ⟨hRDT₁', K₁', ins₁', hK₁', hins₁', hd₁'_tm⟩ := hRearr₁.isCompression.hasMetric'
    obtain ⟨ins'_0, hins'_0⟩ := exists_derivedSlope hComp₀.hasMetric'.1 hK₁'.2.1
    let d'_K₁' := tangleMetric H' K₁' ins'_0 θ'
    have hM'_K₁' : HasTangleMetric H' θ' T' d'_K₁' :=
      ⟨hComp₀.hasMetric'.1, K₁', ins'_0, hK₁', hins'_0, fun _ _ _ _ => rfl⟩
    have hComp_K₁' : IsLambdaCompression H H' θ (4 * lam + 2) T T' d d'_K₁' :=
      isLambdaCompression_of_hasTangleMetric hS hConn hM hRearr₁.z_mem
        h2lam hθ_lt hRearr₁.isSpan'.isRespectful.1 hAtoms hComp₀ hM'_K₁'
    have hSub_T : T₁' ⊆ T' :=
      (theorem_4_1_proof H H' H' K₁' K₁' θ lam₁_tot (4 * lam + 2) T T₁' T' d d₁' d'_K₁'
        ins₁' ins'_0 hS hComp₁_tot hComp_K₁' hK₁' (hθ₁'_eq ▸ hins₁')
        (by intro x hx y hy; rw [hd₁'_tm x hx y hy, hθ₁'_eq])
        hK₁' hins'_0 (fun _ _ _ _ => rfl)).2 rfl rfl (by omega)
    have hTrunc_eq : T₁' = GM10.truncation T' θ₁' :=
      ((GM10.subset_iff_truncation hComp₀.hasMetric'.1.2.1 hRDT₁'.2.1).mp hSub_T).2
    have hM₁'_trunc : HasTangleMetric H' θ₁' (GM10.truncation T' θ₁') d₁' :=
      hTrunc_eq ▸ hRearr₁.isCompression.hasMetric'
    obtain ⟨d', hM', hd₁'_eq, _⟩ :=
      exists_hasTangleMetric_of_truncation hComp₀.hasMetric'.1 hRDT₁'.2.1.one_le
        (by omega) hM₁'_trunc
    have hComp' : IsLambdaCompression H H' θ (4 * lam + 2) T T' d d' :=
      isLambdaCompression_of_hasTangleMetric hS hConn hM hRearr₁.z_mem
        h2lam hθ_lt hRearr₁.isSpan'.isRespectful.1 hAtoms hComp₀ hM'
    have hRearr : IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z :=
      theorem_4_6_proof G H H' η η' θ_star θ lam T_star T T' d d' z
        hFlat.isSpan hM hRearr₁.z_mem h2lam hθ_lt hRearr₁.isSpan'.isRigid
        hRearr₁.isSpan'.isRespectful.1 hAtoms hV hE hComp'
    obtain ⟨P, u, v, hu, hv, hP, hdist₁⟩ := hStep₁
    have hdist' : μ ≤ d' {u} {v} := by
      have heq := hd₁'_eq {u} (Or.inl (Or.inl ⟨u, hu, rfl⟩)) {v} (Or.inl (Or.inl ⟨v, hv, rfl⟩))
      omega
    exact hFlat.no_stepped_rearrangement hRearr ⟨P, u, v, hu, hv, hP, hdist'⟩

/-! ## Helper Lemmas on Truncating Rearrangements, Paths, and 2-Cell Connectivity -/

/-- If `H', η', T'` is obtained from `H, η, T` by rearranging within `λ₁` of `z₁ ∈ A(H)`, and
`z₃ ∈ A(H)` satisfies `d(z₁, z₃) ≤ λ₂ - λ₁` with `λ₁ ≤ λ₂` and `4λ₂ + 2 < θ`, then the
`(θ - (4λ₂ + 2))`-truncation `T''` of `T'` makes `H', η', T''` a `Σ`-span obtained from `H, η, T`
by rearranging within `λ₂` of `z₃`. -/
theorem IsRearrangedWithin.truncation_of_dist_le
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {G : Graph α β} {H H' : Drawing S} {η : SpanEmbedding H G} {η' : SpanEmbedding H' G}
    {θ_star θ lam₁ lam₂ : ℕ} {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {z₁ z₃ : Set S}
    (hRearr : IsRearrangedWithin G H H' η η' θ_star θ lam₁ T_star T T' d d' z₁)
    (hz₃ : z₃ ∈ H.A) (hlam : lam₁ ≤ lam₂) (hdist_z : d z₁ z₃ ≤ lam₂ - lam₁)
    (hθ_lt : 4 * lam₂ + 2 < θ) :
    ∃ d'' : Set S → Set S → ℕ,
      IsRearrangedWithin G H H' η η' θ_star θ lam₂ T_star T
        (GM10.truncation T' (θ - (4 * lam₂ + 2))) d d'' z₃ ∧
      (∀ a ∈ H'.A, ∀ b ∈ H'.A, d'' a b = min (θ - (4 * lam₂ + 2)) (d' a b)) ∧
      (∀ σ₁ σ₂ : S,
        pointDist H' d'' σ₁ σ₂ = min (θ - (4 * lam₂ + 2)) (pointDist H' d' σ₁ σ₂)) := by
  have hS : IsClosedSurface S :=
    ⟨hRearr.isSpan.isSurface.1, hRearr.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hRearr.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hRearr.isSpan.isConnected
  obtain ⟨_, _, _, hd_symm, hd_tri, _⟩ :=
    gm11_theorem_9_1 H θ T d hS hConn hRearr.isCompression.hasMetric
  have hsymm_z : d z₃ z₁ = d z₁ z₃ := hd_symm z₃ hz₃ z₁ hRearr.z_mem
  let θ₂' := θ - (4 * lam₂ + 2)
  have h1 : 1 ≤ θ₂' := by omega
  have hle : θ₂' ≤ θ - (4 * lam₁ + 2) := by omega
  obtain ⟨d'', hM'', hd''_eq, hpt''_eq⟩ :=
    hasTangleMetric_truncation_of_hasTangleMetric hRearr.isCompression.hasMetric' h1 hle
  refine ⟨d'', ⟨hz₃, hRearr.isSpan, hRearr.isSpan'.truncation h1 hle, ?_, ?_, ?_, ?_⟩,
    hd''_eq, hpt''_eq⟩
  · intro a ha hlt
    have htri := hd_tri z₃ hz₃ z₁ hRearr.z_mem a ha
    have hlt₁ : lam₁ < d z₁ a := by omega
    exact hRearr.atom_mem a ha hlt₁
  · intro v hv hlt
    have htri := hd_tri z₃ hz₃ z₁ hRearr.z_mem {v} (Or.inl (Or.inl ⟨v, hv, rfl⟩))
    have hlt₁ : lam₁ < d z₁ {v} := by omega
    exact hRearr.vMap_eq v hv hlt₁
  · intro e he hlt
    have htri := hd_tri z₃ hz₃ z₁ hRearr.z_mem e (Or.inl (Or.inr he))
    have hlt₁ : lam₁ < d z₁ e := by omega
    exact hRearr.eMap_eq e he hlt₁
  · refine ⟨hθ_lt, hRearr.isCompression.hasMetric, hM'', fun σ₁ σ₂ => ?_⟩
    obtain ⟨a₁, ha₁, hσ₁⟩ := exists_atom_of_point H σ₁
    obtain ⟨a₂, ha₂, hσ₂⟩ := exists_atom_of_point H σ₂
    obtain ⟨_, K, ins, _, _, hd⟩ := hRearr.isCompression.hasMetric
    have hle_θ : pointDist H d σ₁ σ₂ ≤ θ := by
      rw [pointDist_eq_of_mem_atom ha₁ ha₂ hσ₁ hσ₂, hd a₁ ha₁ a₂ ha₂]
      exact tangleMetric_le_ord H K ins θ a₁ a₂
    have hle_1 := hRearr.isCompression.dist_le σ₁ σ₂
    rw [hpt''_eq σ₁ σ₂]
    omega

/-- Any walk `W` from `u` to `v` that meets a set `X` can be split at the first vertex `x ∈ X`
along `W`. -/
theorem exists_first_append_of_mem_set {G : Graph α β} {u v : α} (W : GraphWalk G u v)
    {X : Set α} (hne : ∃ z ∈ W.support, z ∈ X) :
    ∃ (x : α) (W₁ : GraphWalk G u x) (W₂ : GraphWalk G x v),
      x ∈ X ∧ W = W₁.append W₂ ∧ ∀ y ∈ W₁.support, y ∈ X → y = x := by
  induction W with
  | @nil u₀ h =>
    obtain ⟨z, hz, hzX⟩ := hne
    simp only [GraphWalk.support_nil, List.mem_singleton] at hz
    subst hz
    refine ⟨z, .nil h, .nil h, hzX, rfl, fun y hy _ => ?_⟩
    simpa [GraphWalk.support_nil] using hy
  | cons h r ih =>
    rename_i u₁ v₁ w₁ e
    by_cases huX : u₁ ∈ X
    · refine ⟨u₁, .nil h.left_mem, .cons h r, huX, rfl, fun y hy _ => ?_⟩
      simpa [GraphWalk.support_nil] using hy
    · have hne' : ∃ z ∈ r.support, z ∈ X := by
        obtain ⟨z, hz, hzX⟩ := hne
        rcases List.mem_cons.mp hz with rfl | hz
        · exact absurd hzX huX
        · exact ⟨z, hz, hzX⟩
      obtain ⟨x, W₁, W₂, hxX, rfl, hfirst⟩ := ih hne'
      refine ⟨x, .cons h W₁, W₂, hxX, rfl, fun y hy hyX => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact absurd hyX huX
      · exact hfirst y hy hyX

/-- If `P` is a path in `G` from `a` to `b` and `(V(P) ∩ X).Nonempty`, then `P` splits at the first
vertex `x ∈ V(P) ∩ X` into `P₁` (from `a` to `x`) and `P₂` (from `x` to `b`) with
`V(P₁) ∩ X = {x}`. -/
theorem _root_.GraphMinor.GM09.IsGraphPathWithEnds.exists_first_split_of_nonempty
    {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) {X : Set α} (hne : (V(P) ∩ X).Nonempty) :
    ∃ (x : α) (P₁ P₂ : Graph α β),
      x ∈ V(P) ∧ x ∈ X ∧
      P₁ ≤ P ∧ P₂ ≤ P ∧
      IsGraphPathWithEnds P P₁ a x ∧ IsGraphPathWithEnds P P₂ x b ∧
      subgraphUnion P P₁ P₂ = P ∧
      V(P₁) ∩ V(P₂) = {x} ∧ Disjoint E(P₁) E(P₂) ∧
      V(P₁) ∩ X = {x} := by
  obtain ⟨_, W, hW, hVP, hEP⟩ := id hP
  obtain ⟨z, hzP, hzX⟩ := hne
  have hzW : z ∈ W.support := by rwa [hVP] at hzP
  obtain ⟨x, W₁, W₂, hxX, rfl, hfirst⟩ := exists_first_append_of_mem_set W ⟨z, hzW, hzX⟩
  have hxP : x ∈ V(P) := by
    rw [hVP, mem_ofPred_eq, GraphWalk.mem_support_append]
    exact Or.inl W₁.end_mem_support
  have hsp := isSimple_of_append hW
  let P₁ := walkSubgraph W₁
  let P₂ := walkSubgraph W₂
  have hP₁P : P₁ ≤ P := walkSubgraph_le W₁
  have hP₂P : P₂ ≤ P := walkSubgraph_le W₂
  have hP₁ : IsGraphPathWithEnds P P₁ a x := isGraphPathWithEnds_walkSubgraph hsp.1
  have hP₂ : IsGraphPathWithEnds P P₂ x b := isGraphPathWithEnds_walkSubgraph hsp.2
  have hnd_V : (W₁.support ++ W₂.support.tail).Nodup := by
    have h' : (W₁.append W₂).support.Nodup := hW
    rwa [GraphWalk.support_append] at h'
  have hd_V := List.nodup_append.mp hnd_V
  have hnd_E : (W₁.edges ++ W₂.edges).Nodup := by
    have h' : (W₁.append W₂).edges.Nodup := hW.edges_nodup
    rwa [GraphWalk.edges_append] at h'
  have hd_E := List.nodup_append.mp hnd_E
  refine ⟨x, P₁, P₂, hxP, hxX, hP₁P, hP₂P, hP₁, hP₂, ?_, ?_, ?_, ?_⟩
  · refine (Compatible.of_le_le (subgraphUnion_le hP₁P hP₂P) le_rfl).ext ?_ ?_
    · rw [vertexSet_subgraphUnion, vertexSet_walkSubgraph, vertexSet_walkSubgraph, hVP]
      ext y
      simp [GraphWalk.mem_support_append]
    · rw [edgeSet_subgraphUnion hP₁P hP₂P, edgeSet_walkSubgraph, edgeSet_walkSubgraph, hEP]
      ext e
      simp [GraphWalk.edges_append]
  · rw [vertexSet_walkSubgraph, vertexSet_walkSubgraph]
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨hy₁, hy₂⟩
      rw [W₂.support_eq_cons] at hy₂
      rcases List.mem_cons.mp hy₂ with rfl | hy₂
      · rfl
      · exact False.elim (hd_V.2.2 y hy₁ y hy₂ rfl)
    · rintro rfl
      exact ⟨W₁.end_mem_support, W₂.start_mem_support⟩
  · rw [edgeSet_walkSubgraph, edgeSet_walkSubgraph]
    exact disjoint_left.mpr fun e he₁ he₂ => hd_E.2.2 e he₁ e he₂ rfl
  · rw [vertexSet_walkSubgraph]
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
    refine ⟨fun ⟨hy₁, hyX⟩ => hfirst y hy₁ hyX, ?_⟩
    rintro rfl
    exact ⟨W₁.end_mem_support, hxX⟩

/-- A path in a graph contains no loop edge. -/
theorem _root_.GraphMinor.GM09.IsGraphPathWithEnds.not_isLink_self
    {G P : Graph α β} {a b x : α} {e : β}
    (hP : IsGraphPathWithEnds G P a b) : ¬ P.IsLink e x x := by
  obtain ⟨_, W, hW, hVP, hEP⟩ := hP
  intro hlink
  have he : e ∈ W.edges := by
    have : e ∈ E(P) := hlink.edge_mem
    rwa [hEP] at this
  have hnd : W.support.Nodup := hW
  clear hW hVP hEP
  induction W with
  | nil _ => simp at he
  | cons h r ih =>
    rcases List.mem_cons.mp he with rfl | he
    · rcases h.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (List.nodup_cons.mp hnd).1 r.start_mem_support
      · exact (List.nodup_cons.mp hnd).1 r.start_mem_support
    · exact ih he (List.nodup_cons.mp hnd).2

/-- If `R₁` is an `H_sub`-path with ends `a₁, b₁` and `R₂` is an `H_sub`-path with ends `a₂, b₂`,
`{a₁, b₁}` and `{a₂, b₂}` are disjoint, and `(V(R₁) ∩ V(R₂)).Nonempty`, then there is an
`H_sub`-path `P` in `G` with ends `a₁` and `b₂` such that `V(P) ⊆ V(R₁) ∪ V(R₂)` and
`E(P) ⊆ E(R₁) ∪ E(R₂)`. -/
theorem exists_isHPathWithEnds_of_inter_nonempty {G H_sub R₁ R₂ : Graph α β} {a₁ b₁ a₂ b₂ : α}
    (hR₁ : IsHPathWithEnds G H_sub R₁ a₁ b₁) (hR₂ : IsHPathWithEnds G H_sub R₂ a₂ b₂)
    (hdisj_ends : Disjoint ({a₁, b₁} : Set α) {a₂, b₂})
    (hne : (V(R₁) ∩ V(R₂)).Nonempty) :
    ∃ P : Graph α β,
      IsHPathWithEnds G H_sub P a₁ b₂ ∧
      V(P) ⊆ V(R₁) ∪ V(R₂) ∧ E(P) ⊆ E(R₁) ∪ E(R₂) := by
  obtain ⟨x, P₁, P₂, hxR₁, hxR₂, hP₁_le, hP₂_le, hP₁, hP₂, hunion₁, hinter₁, _, hP₁_R₂⟩ :=
    hR₁.2.1.exists_first_split_of_nonempty hne
  obtain ⟨Q₁, Q₂, hQ₁_le, hQ₂_le, hQ₁, hQ₂, hunion₂, hinter₂, _⟩ :=
    hR₂.2.1.exists_split_at hxR₂
  have hx_notH : x ∉ V(H_sub) := by
    intro hxH
    have hx₁ : x ∈ ({a₁, b₁} : Set α) := hR₁.2.2.2.2.2.1 ▸ ⟨hxR₁, hxH⟩
    have hx₂ : x ∈ ({a₂, b₂} : Set α) := hR₂.2.2.2.2.2.1 ▸ ⟨hxR₂, hxH⟩
    exact Set.disjoint_left.mp hdisj_ends hx₁ hx₂
  have hP₁G : P₁ ≤ G := hP₁_le.trans hR₁.2.1.le
  have hQ₂G : Q₂ ≤ G := hQ₂_le.trans hR₂.2.1.le
  have hVQ : V(P₁) ∩ V(Q₂) = {x} := by
    apply Set.Subset.antisymm
    · rw [← hP₁_R₂]
      exact inter_subset_inter_right _ hQ₂_le.vertexSet_mono
    · rw [singleton_subset_iff]
      exact ⟨hP₁.right_mem, hQ₂.left_mem⟩
  let P := subgraphUnion G P₁ Q₂
  have hP_path : IsGraphPathWithEnds G P a₁ b₂ :=
    (hP₁.mono hR₁.2.1.le).subgraphUnion (hQ₂.mono hR₂.2.1.le) hVQ
  have hb₁_not : b₁ ∉ V(P₁) := by
    intro hb₁P₁
    have hb₁_x : b₁ = x := by
      have : b₁ ∈ V(P₁) ∩ V(P₂) := ⟨hb₁P₁, hP₂.right_mem⟩
      rwa [hinter₁, mem_singleton_iff] at this
    exact hx_notH (hb₁_x ▸ hR₁.2.2.2.2.1)
  have ha₂_not : a₂ ∉ V(Q₂) := by
    intro ha₂Q₂
    have ha₂_x : a₂ = x := by
      have : a₂ ∈ V(Q₁) ∩ V(Q₂) := ⟨hQ₁.left_mem, ha₂Q₂⟩
      rwa [hinter₂, mem_singleton_iff] at this
    exact hx_notH (ha₂_x ▸ hR₂.2.2.2.1)
  have hVP : V(P) ∩ V(H_sub) = {a₁, b₂} := by
    rw [vertexSet_subgraphUnion]
    apply Set.Subset.antisymm
    · rintro y ⟨hy₁ | hy₂, hyH⟩
      · have hy_ab : y ∈ ({a₁, b₁} : Set α) :=
          hR₁.2.2.2.2.2.1 ▸ ⟨hP₁_le.vertexSet_mono hy₁, hyH⟩
        rcases hy_ab with rfl | rfl
        · exact Or.inl rfl
        · exact (hb₁_not hy₁).elim
      · have hy_ab : y ∈ ({a₂, b₂} : Set α) :=
          hR₂.2.2.2.2.2.1 ▸ ⟨hQ₂_le.vertexSet_mono hy₂, hyH⟩
        rcases hy_ab with rfl | rfl
        · exact (ha₂_not hy₂).elim
        · exact Or.inr rfl
    · rintro y (rfl | rfl)
      · exact ⟨Or.inl hP₁.left_mem, hR₁.2.2.2.1⟩
      · exact ⟨Or.inr hQ₂.right_mem, hR₂.2.2.2.2.1⟩
  have hEP_sub : E(P) ⊆ E(R₁) ∪ E(R₂) := by
    rw [edgeSet_subgraphUnion hP₁G hQ₂G]
    exact union_subset_union hP₁_le.edgeSet_mono hQ₂_le.edgeSet_mono
  have hEP_disj : Disjoint E(P) E(H_sub) := by
    rw [edgeSet_subgraphUnion hP₁G hQ₂G, disjoint_union_left]
    exact ⟨hR₁.2.2.2.2.2.2.mono_left hP₁_le.edgeSet_mono,
      hR₂.2.2.2.2.2.2.mono_left hQ₂_le.edgeSet_mono⟩
  have ha₁_ne_b₂ : a₁ ≠ b₂ := fun h =>
    Set.disjoint_left.mp hdisj_ends (Or.inl rfl) (h ▸ Or.inr rfl)
  refine ⟨P, ⟨hR₁.1, hP_path, ha₁_ne_b₂, hR₁.2.2.2.1, hR₂.2.2.2.2.1, hVP, hEP_disj⟩, ?_, hEP_sub⟩
  rw [vertexSet_subgraphUnion]
  exact union_subset_union hP₁_le.vertexSet_mono hQ₂_le.vertexSet_mono

/-- In a drawing `H` on a connected closed surface `S`, every point of `S` lies in the closure of
some region of `H`. -/
theorem exists_region_closure_mem_of_closedSurface {S : Type w} [TopologicalSpace S] [T2Space S]
    [ConnectedSpace S] (hS : IsClosedSurface S) (H : Drawing S) (x : S) :
    ∃ r ∈ H.R, x ∈ closure r := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hfin : H.R.Finite := GM11.finite_R hS H
  by_contra hnot
  push Not at hnot
  have hcl : IsClosed (⋃ r ∈ H.R, closure r) :=
    hfin.isClosed_biUnion fun r _ => isClosed_closure
  have hx : x ∈ (⋃ r ∈ H.R, closure r)ᶜ := by
    simp only [mem_compl_iff, mem_iUnion, not_exists]
    exact hnot
  obtain ⟨y, hyO, hyU⟩ :=
    GM11.exists_notMem_U (Γ := H) hS hcl.isOpen_compl ⟨x, hx⟩
  obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem hyU
  exact hyO (mem_iUnion₂.mpr ⟨r, hr, subset_closure hyr⟩)

/-- If `Γ` is a 2-cell drawing in a connected closed surface `S` with `Γ.E.Nonempty`, then
`Γ.toGraph` is connected: between any two vertices `a, b ∈ Γ.V`, there is a walk in `Γ.toGraph`. -/
theorem twoCell_toGraph_connected {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} (h2cell : (PaintingOrDrawing.drawing Γ).IsTwoCell)
    (hE : Γ.E.Nonempty) {a b : S} (ha : a ∈ Γ.V) (hb : b ∈ Γ.V) :
    Nonempty (GraphWalk Γ.toGraph a b) := by
  classical
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  by_contra hno
  let V₁ : Set S := {u ∈ Γ.V | Nonempty (GraphWalk Γ.toGraph a u)}
  let V₂ : Set S := Γ.V \ V₁
  have haV₁ : a ∈ V₁ := ⟨ha, ⟨.nil ha⟩⟩
  have hbV₂ : b ∈ V₂ := ⟨hb, fun ⟨_, hW⟩ => hno hW⟩
  have hEnds : ∀ e ∈ Γ.E, ∀ u ∈ Γ.V, ∀ v ∈ Γ.V,
      u ∈ closure e → v ∈ closure e → u ∈ V₁ → v ∈ V₁ := by
    intro e he u hu v hv hue hve ⟨_, ⟨W⟩⟩
    by_cases huv : u = v
    · exact huv ▸ ⟨hu, ⟨W⟩⟩
    · have hpair : closure e ∩ Γ.V = {u, v} := by
        rcases Γ.edge_cond e he with ⟨x, y, _, hcl, _⟩ | ⟨x, hcl, _⟩
        · have hu_xy : u ∈ ({x, y} : Set S) := hcl ▸ ⟨hue, hu⟩
          have hv_xy : v ∈ ({x, y} : Set S) := hcl ▸ ⟨hve, hv⟩
          rw [hcl]
          rcases hu_xy with rfl | rfl <;> rcases hv_xy with rfl | rfl
          · exact False.elim (huv rfl)
          · rfl
          · exact Set.pair_comm _ _
          · exact False.elim (huv rfl)
        · have hu_x : u = x := by
            have : u ∈ ({x} : Set S) := hcl ▸ ⟨hue, hu⟩
            simpa using this
          have hv_x : v = x := by
            have : v ∈ ({x} : Set S) := hcl ▸ ⟨hve, hv⟩
            simpa using this
          exact False.elim (huv (hu_x.trans hv_x.symm))
      have hlink : Γ.toGraph.IsLink e u v := ⟨he, hu, hv, hpair⟩
      exact ⟨hv, ⟨W.append (.cons hlink (.nil hv))⟩⟩
  let E₁ : Set (Set S) := {e ∈ Γ.E | ∃ u ∈ V₁, u ∈ closure e}
  let E₂ : Set (Set S) := Γ.E \ E₁
  obtain ⟨K, hK⟩ := GM11.exists_radialDrawing hS h2cell
  have hrad : GM11.PreRad (PaintingOrDrawing.drawing Γ) K := ⟨hK.1, hK.2.1⟩
  have hmax : GM11.RadMax (PaintingOrDrawing.drawing Γ) K := hK.2.2
  let H_rad := GM11.radialUnion hrad
  have hfinR : H_rad.R.Finite := GM11.finite_R hS H_rad
  let P₁ : Set (Set S) := {p ∈ H_rad.R | ∃ e ∈ E₁, e ⊆ closure p}
  let P₂ : Set (Set S) := {p ∈ H_rad.R | ∃ e ∈ E₂, e ⊆ closure p}
  have hP_union : ∀ p ∈ H_rad.R, p ∈ P₁ ∨ p ∈ P₂ := by
    intro p hp
    obtain ⟨e, he, hep, _, _⟩ := GM11.face_edge hrad hS hmax hE hp
    by_cases he₁ : e ∈ E₁
    · exact Or.inl ⟨hp, e, he₁, hep⟩
    · exact Or.inr ⟨hp, e, ⟨he, he₁⟩, hep⟩
  let W₁ : Set S := ⋃ p ∈ P₁, closure p
  let W₂ : Set S := ⋃ p ∈ P₂, closure p
  have hP₁fin : P₁.Finite := hfinR.subset fun _ h => h.1
  have hP₂fin : P₂.Finite := hfinR.subset fun _ h => h.1
  have hW₁_cl : IsClosed W₁ := hP₁fin.isClosed_biUnion fun _ _ => isClosed_closure
  have hW₂_cl : IsClosed W₂ := hP₂fin.isClosed_biUnion fun _ _ => isClosed_closure
  let Hubs : Set S := K.V \ Γ.V
  have hHubs_fin : Hubs.Finite := K.finite_V.subset sdiff_subset
  have hConn_compl : IsPreconnected Hubsᶜ := GM11.isPreconnected_compl_finite hS hHubs_fin
  have hcov : Hubsᶜ ⊆ W₁ ∪ W₂ := by
    intro x _
    obtain ⟨p, hp, hxp⟩ := exists_region_closure_mem_of_closedSurface hS H_rad x
    rcases hP_union p hp with hp₁ | hp₂
    · exact Or.inl (mem_iUnion₂.mpr ⟨p, hp₁, hxp⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨p, hp₂, hxp⟩)
  have hdisj : Disjoint (Hubsᶜ ∩ W₁) (Hubsᶜ ∩ W₂) := by
    refine Set.disjoint_left.mpr ?_
    rintro x ⟨hxH, hx₁⟩ ⟨_, hx₂⟩
    obtain ⟨p₁, ⟨hp₁, e₁, he₁, he₁p₁⟩, hxp₁⟩ := mem_iUnion₂.mp hx₁
    obtain ⟨p₂, ⟨hp₂, e₂, he₂, he₂p₂⟩, hxp₂⟩ := mem_iUnion₂.mp hx₂
    obtain ⟨f₁, hf₁, hf₁p₁, huniq₁, hv₁⟩ := GM11.face_edge hrad hS hmax hE hp₁
    obtain ⟨f₂, hf₂, hf₂p₂, huniq₂, hv₂⟩ := GM11.face_edge hrad hS hmax hE hp₂
    have he₁_eq : e₁ = f₁ := huniq₁ e₁ he₁.1 he₁p₁
    have he₂_eq : e₂ = f₂ := huniq₂ e₂ he₂.1 he₂p₂
    have hp_ne : p₁ ≠ p₂ := by
      rintro rfl
      have hf_eq : f₁ = f₂ := (huniq₁ f₂ hf₂ hf₂p₂).symm
      have he_eq : e₂ = e₁ := he₂_eq.trans (hf_eq.symm.trans he₁_eq.symm)
      exact he₂.2 (he_eq ▸ he₁)
    have hxU : x ∈ H_rad.U := by
      by_contra hnotU
      obtain ⟨q, hq, hxq⟩ := exists_region_of_notMem hnotU
      obtain ⟨y₁, hy₁q, hy₁p₁⟩ := mem_closure_iff.mp hxp₁ q (region_isOpen hq) hxq
      obtain ⟨y₂, hy₂q, hy₂p₂⟩ := mem_closure_iff.mp hxp₂ q (region_isOpen hq) hxq
      have hqp₁ : q = p₁ := region_eq_of_mem hq hp₁ hy₁q hy₁p₁
      have hqp₂ : q = p₂ := region_eq_of_mem hq hp₂ hy₂q hy₂p₂
      exact hp_ne (hqp₁.symm.trans hqp₂)
    have hnot_V : ∀ v ∈ Γ.V, ¬ (v ∈ closure p₁ ∧ v ∈ closure p₂) := by
      rintro v hv ⟨hvp₁, hvp₂⟩
      have hve₁ : v ∈ closure e₁ := he₁_eq ▸ hv₁ v hv hvp₁
      have hve₂ : v ∈ closure e₂ := he₂_eq ▸ hv₂ v hv hvp₂
      obtain ⟨u₁, hu₁V₁, hu₁e₁⟩ := he₁.2
      have hvV₁ : v ∈ V₁ := hEnds e₁ he₁.1 u₁ hu₁V₁.1 v hv hu₁e₁ hve₁ hu₁V₁
      exact he₂.2 ⟨he₂.1, v, hvV₁, hve₂⟩
    by_cases hxKV : x ∈ K.V
    · have hxΓV : x ∈ Γ.V := by
        by_contra hxnot
        exact hxH ⟨hxKV, hxnot⟩
      exact hnot_V x hxΓV ⟨hxp₁, hxp₂⟩
    · have hxH_radV : x ∉ H_rad.V := by
        rw [GM11.radialUnion_V]
        exact hxKV
      rw [H_rad.U_eq, GM11.radialUnion_V] at hxU
      rcases hxU with hxKV' | hxE
      · exact hxKV hxKV'
      · obtain ⟨g, hg, hxg_cl⟩ := mem_iUnion₂.mp hxE
        have hxg : x ∈ g := (H_rad.closure_diff_V hg).subset ⟨hxg_cl, hxH_radV⟩
        have hgp₁ : g ⊆ closure p₁ :=
          GM11.edge_subset_closure_of_incident hS hg hp₁ ⟨x, hxg, hxp₁⟩
        have hgp₂ : g ⊆ closure p₂ :=
          GM11.edge_subset_closure_of_incident hS hg hp₂ ⟨x, hxg, hxp₂⟩
        rw [GM11.radialUnion_E] at hg
        rcases hg with hgΓ | hgK
        · have hg_f₁ : g = f₁ := huniq₁ g hgΓ hgp₁
          have hg_f₂ : g = f₂ := huniq₂ g hgΓ hgp₂
          exact he₂.2 (he₂_eq.trans (hg_f₂.symm.trans (hg_f₁.trans he₁_eq.symm)) ▸ he₁)
        · obtain ⟨v, hv, _, _, _, _, _, hcap, _⟩ := GM11.spoke_ends hrad hS hgK
          have hvg : v ∈ closure g := by
            have : v ∈ closure g ∩ K.V := by rw [hcap]; simp
            exact this.1
          exact hnot_V v hv ⟨closure_minimal hgp₁ isClosed_closure hvg,
            closure_minimal hgp₂ isClosed_closure hvg⟩
  have ha_mem : a ∈ Hubsᶜ ∩ W₁ := by
    refine ⟨fun h => h.2 ha, ?_⟩
    obtain ⟨p, hp, hap⟩ := exists_region_closure_mem_of_closedSurface hS H_rad a
    obtain ⟨f, hf, hfp, _, hvf⟩ := GM11.face_edge hrad hS hmax hE hp
    exact mem_iUnion₂.mpr ⟨p, ⟨hp, f, ⟨hf, a, haV₁, hvf a ha hap⟩, hfp⟩, hap⟩
  have hb_mem : b ∈ Hubsᶜ ∩ W₂ := by
    refine ⟨fun h => h.2 hb, ?_⟩
    obtain ⟨p, hp, hbp⟩ := exists_region_closure_mem_of_closedSurface hS H_rad b
    obtain ⟨f, hf, hfp, _, hvf⟩ := GM11.face_edge hrad hS hmax hE hp
    have hfE₂ : f ∈ E₂ := by
      refine ⟨hf, ?_⟩
      rintro ⟨_, u, huV₁, huf⟩
      exact hbV₂.2 (hEnds f hf u huV₁.1 b hb huf (hvf b hb hbp) huV₁)
    exact mem_iUnion₂.mpr ⟨p, ⟨hp, f, hfE₂, hfp⟩, hbp⟩
  have hcov' : Hubsᶜ ⊆ W₂ᶜ ∪ W₁ᶜ := by
    intro x hx
    rcases hcov hx with hx₁ | hx₂
    · exact Or.inl fun hx₂ => Set.disjoint_left.mp hdisj ⟨hx, hx₁⟩ ⟨hx, hx₂⟩
    · exact Or.inr fun hx₁ => Set.disjoint_left.mp hdisj ⟨hx, hx₁⟩ ⟨hx, hx₂⟩
  have hdisj' : Disjoint (Hubsᶜ ∩ W₂ᶜ) (Hubsᶜ ∩ W₁ᶜ) := by
    refine Set.disjoint_left.mpr ?_
    rintro x ⟨hx, hxnot₂⟩ ⟨_, hxnot₁⟩
    rcases hcov hx with hx₁ | hx₂
    · exact hxnot₁ hx₁
    · exact hxnot₂ hx₂
  have ha_open : a ∈ Hubsᶜ ∩ W₂ᶜ :=
    ⟨ha_mem.1, fun ha₂ => Set.disjoint_left.mp hdisj ha_mem ⟨ha_mem.1, ha₂⟩⟩
  have hb_open : b ∈ Hubsᶜ ∩ W₁ᶜ :=
    ⟨hb_mem.1, fun hb₁ => Set.disjoint_left.mp hdisj ⟨hb_mem.1, hb₁⟩ hb_mem⟩
  obtain ⟨x, hxH, hxnot₂, hxnot₁⟩ :=
    hConn_compl W₂ᶜ W₁ᶜ hW₂_cl.isOpen_compl hW₁_cl.isOpen_compl hcov' ⟨a, ha_open⟩ ⟨b, hb_open⟩
  rcases hcov hxH with hx₁ | hx₂
  · exact hxnot₁ hx₁
  · exact hxnot₂ hx₂

/-- For `η : SpanEmbedding Γ G`, `e ∈ Γ.E`, and distinct `u, v ∈ Γ.V`, `η.eMap e` links
`η.vMap u` and `η.vMap v` in `η.imageGraph` if and only if `e` links `u` and `v` in `Γ.toGraph`. -/
theorem _root_.GraphMinor.GM14.SpanEmbedding.isLink_iff_of_ne {S : Type w} [TopologicalSpace S]
    {G : Graph α β} {Γ : Drawing S} (η : SpanEmbedding Γ G)
    {e : Set S} (he : e ∈ Γ.E) {u v : S} (hu : u ∈ Γ.V) (hv : v ∈ Γ.V) (huv : u ≠ v) :
    η.imageGraph.IsLink (η.eMap e) (η.vMap u) (η.vMap v) ↔ Γ.toGraph.IsLink e u v := by
  constructor
  · intro hlink
    have hue : u ∈ closure e := (η.inc_iff e he u hu).mp hlink.inc_left
    have hve : v ∈ closure e := (η.inc_iff e he v hv).mp hlink.inc_right
    have hpair : closure e ∩ Γ.V = {u, v} := by
      rcases Γ.edge_cond e he with ⟨x, y, _, hcl, _⟩ | ⟨x, hcl, _⟩
      · have hu_xy : u ∈ ({x, y} : Set S) := hcl ▸ ⟨hue, hu⟩
        have hv_xy : v ∈ ({x, y} : Set S) := hcl ▸ ⟨hve, hv⟩
        rw [hcl]
        rcases hu_xy with rfl | rfl <;> rcases hv_xy with rfl | rfl
        · exact False.elim (huv rfl)
        · rfl
        · exact Set.pair_comm _ _
        · exact False.elim (huv rfl)
      · have hu_x : u = x := by
          have : u ∈ ({x} : Set S) := hcl ▸ ⟨hue, hu⟩
          simpa using this
        have hv_x : v = x := by
          have : v ∈ ({x} : Set S) := hcl ▸ ⟨hve, hv⟩
          simpa using this
        exact False.elim (huv (hu_x.trans hv_x.symm))
    exact ⟨he, hu, hv, hpair⟩
  · rintro ⟨_, _, _, hpair⟩
    have hue : u ∈ closure e := by
      have : u ∈ closure e ∩ Γ.V := by rw [hpair]; simp
      exact this.1
    have hve : v ∈ closure e := by
      have : v ∈ closure e ∩ Γ.V := by rw [hpair]; simp
      exact this.1
    have hinc₁ : η.imageGraph.Inc (η.eMap e) (η.vMap u) := (η.inc_iff e he u hu).mpr hue
    have hinc₂ : η.imageGraph.Inc (η.eMap e) (η.vMap v) := (η.inc_iff e he v hv).mpr hve
    obtain ⟨w₁, hw₁⟩ := hinc₁
    obtain ⟨w₂, hw₂⟩ := hinc₂
    have huv' : η.vMap u ≠ η.vMap v := fun h => huv (η.bijOn_v.injOn hu hv h)
    have h_eq := hw₁.eq_and_eq_or_eq_and_eq hw₂
    rcases h_eq with ⟨hEq, _⟩ | ⟨_, rfl⟩
    · exact False.elim (huv' hEq)
    · exact hw₁

/-- A simple walk `W` of `Γ.toGraph` maps under `η : SpanEmbedding Γ G` to a simple walk `W'` of
`η.imageGraph` with `W'.support = W.support.map η.vMap` and `W'.edges = W.edges.map η.eMap`. -/
theorem _root_.GraphMinor.GM14.SpanEmbedding.exists_walk_imageGraph
    {S : Type w} [TopologicalSpace S]
    {G : Graph α β} {Γ : Drawing S} (η : SpanEmbedding Γ G)
    {a b : S} (W : GraphWalk Γ.toGraph a b) (hW : W.IsSimple) :
    ∃ W' : GraphWalk η.imageGraph (η.vMap a) (η.vMap b),
      W'.IsSimple ∧ W'.support = W.support.map η.vMap ∧ W'.edges = W.edges.map η.eMap := by
  have hnd : W.support.Nodup := hW
  clear hW
  induction W with
  | @nil u h =>
    have huV : u ∈ Γ.V := h
    exact ⟨.nil (η.bijOn_v.mapsTo huV), by simp [GraphWalk.IsSimple], rfl, rfl⟩
  | cons h r ih =>
    rename_i u v w e
    have hu_not : u ∉ r.support := (List.nodup_cons.mp hnd).1
    have hnd_r : r.support.Nodup := (List.nodup_cons.mp hnd).2
    have huv : u ≠ v := fun hEq => hu_not (hEq ▸ r.start_mem_support)
    have hlink' : η.imageGraph.IsLink (η.eMap e) (η.vMap u) (η.vMap v) :=
      (η.isLink_iff_of_ne h.1 h.2.1 h.2.2.1 huv).mpr h
    obtain ⟨W', hW'_sim, hsup, hed⟩ := ih hnd_r
    refine ⟨.cons hlink' W', ?_, by simp [hsup], by simp [hed]⟩
    unfold GraphWalk.IsSimple at hW'_sim ⊢
    rw [GraphWalk.support_cons, List.nodup_cons]
    refine ⟨?_, hW'_sim⟩
    rw [hsup, List.mem_map]
    rintro ⟨z, hz, hzu⟩
    have hzV : z ∈ Γ.V := r.mem_vertexSet_of_mem_support hz
    have hzu' : z = u := η.bijOn_v.injOn hzV h.2.1 hzu
    exact hu_not (hzu' ▸ hz)

/-- In a 2-cell drawing `Γ` on a connected closed surface `S` with `Γ.E.Nonempty`, for any
`η : SpanEmbedding Γ G` and `a, b ∈ Γ.V`, there is a path in `η.imageGraph` from `η.vMap a` to
`η.vMap b`. -/
theorem _root_.GraphMinor.GM14.SpanEmbedding.exists_path_imageGraph
    {S : Type w} [TopologicalSpace S] [T2Space S]
    [ConnectedSpace S] (hS : IsClosedSurface S) {G : Graph α β} {Γ : Drawing S}
    (h2cell : (PaintingOrDrawing.drawing Γ).IsTwoCell) (hE : Γ.E.Nonempty)
    (η : SpanEmbedding Γ G) {a b : S} (ha : a ∈ Γ.V) (hb : b ∈ Γ.V) :
    ∃ P : Graph α β, IsGraphPathWithEnds η.imageGraph P (η.vMap a) (η.vMap b) := by
  obtain ⟨W₀⟩ := twoCell_toGraph_connected hS h2cell hE ha hb
  obtain ⟨W, hW_sim, _, _⟩ := exists_isSimple_subwalk W₀
  obtain ⟨W', hW'_sim, _, _⟩ := η.exists_walk_imageGraph W hW_sim
  exact ⟨walkSubgraph W', isGraphPathWithEnds_walkSubgraph hW'_sim⟩

/-! ## Helper Lemmas for (5.2): Zones, Common Compressions, and Dials -/

/-- Generalization of `(4.2)` (`theorem_4_2_proof`) to two drawings `H₁, H₂` whose tangles `T₁, T₂`
are
both compressions of a common tangle `(H₀, θ₀, T₀, d₀)` (Graph Minors XV, proof of `(5.2)` Claim
`(14)`, page 133). -/
theorem pointDist_le_of_common_compression
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {H₀ H₁ H₂ : Drawing S} {Z : Set S} {θ₀ lam₁ lam₂ : ℕ}
    {T₀ T₁ T₂ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d₀ d₁ d₂ : Set S → Set S → ℕ} {x y : S}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (hComp₁ : IsLambdaCompression H₀ H₁ θ₀ lam₁ T₀ T₁ d₀ d₁)
    (hComp₂ : IsLambdaCompression H₀ H₂ θ₀ lam₂ T₀ T₂ d₀ d₂)
    (hZ : ∀ a ∈ H₁.A, a ∉ H₂.A → a ⊆ Z)
    (hltZ : ∀ σ ∈ Z, pointDist H₁ d₁ x y < pointDist H₁ d₁ x σ)
    (hlt₁ : pointDist H₁ d₁ x y < θ₀ - lam₁) :
    pointDist H₂ d₂ x y ≤ pointDist H₁ d₁ x y := by
  let θ₁ := θ₀ - lam₁
  let θ₂ := θ₀ - lam₂
  have hMetric₁ : HasTangleMetric H₁ θ₁ T₁ d₁ := hComp₁.hasMetric'
  have hMetric₂ : HasTangleMetric H₂ θ₂ T₂ d₂ := hComp₂.hasMetric'
  obtain ⟨_, K₁, ins₁, hK₁, hins₁, hd₁⟩ := id hMetric₁
  obtain ⟨ax, hax, hx_ax⟩ := exists_atom_of_point H₁ x
  obtain ⟨ay, hay, hy_ay⟩ := exists_atom_of_point H₁ y
  obtain ⟨ax', hax', hx_ax'⟩ := exists_atom_of_point H₂ x
  obtain ⟨ay', hay', hy_ay'⟩ := exists_atom_of_point H₂ y
  have hpt₁ : pointDist H₁ d₁ x y = d₁ ax ay := pointDist_eq_of_mem_atom hax hay hx_ax hy_ay
  have hpt₂ : pointDist H₂ d₂ x y = d₂ ax' ay' := pointDist_eq_of_mem_atom hax' hay' hx_ax' hy_ay'
  by_cases hxy : ax = ay
  · subst hxy
    have h0 : d₁ ax ax = 0 := by rw [hd₁ ax hax ax hax]; simp [tangleMetric]
    have hax_mem' : ax ∈ H₂.A := by
      by_contra hnot
      have hsubZ : ax ⊆ Z := hZ ax hax hnot
      have hlt_xx := hltZ x (hsubZ hx_ax)
      rw [pointDist_eq_of_mem_atom hax hax hx_ax hx_ax] at hlt_xx
      omega
    have hax_eq : ax' = ax := atom_eq_of_mem hax' hax_mem' hx_ax' hx_ax
    have hay_eq : ay' = ax := atom_eq_of_mem hay' hax_mem' hy_ay' hy_ay
    obtain ⟨_, K₀', ins₀', _, _, hd₀'⟩ := hMetric₂
    rw [hpt₂, hax_eq, hay_eq, hd₀' ax hax_mem' ax hax_mem']
    simp [tangleMetric]
  · by_cases hlt₂ : pointDist H₁ d₁ x y < θ₂
    · have htm_lt : tangleMetric H₁ K₁ ins₁ θ₁ ax ay < θ₁ := by
        rwa [← hd₁ ax hax ay hay, ← hpt₁]
      obtain ⟨u, W, ax_K, ay_K, hax_K, hay_K, hW_lt, hW_len, hax_sub, hay_sub⟩ :=
        exists_walk_of_tangleMetric_lt hK₁.2.1 ins₁ hxy htm_lt
      rw [← hd₁ ax hax ay hay, ← hpt₁] at hW_len
      have hAtomsInW : ∀ a ∈ H₁.A, (a ∩ insWalk ins₁ K₁ W).Nonempty → a ∈ H₂.A := by
        intro a ha ⟨σ, hσa, hσW⟩
        by_contra hnot
        have hσZ : σ ∈ Z := hZ a ha hnot hσa
        obtain ⟨a_K, ha_K⟩ := exists_correspondingAtom hK₁.2.1 ha
        have ha_sub : a_K ⊆ insWalk ins₁ K₁ W :=
          (GM14.theorem_3_1_proof hS hK₁ hins₁ ha_K W hW_lt).mpr ⟨σ, hσa, hσW⟩
        have hle2 := two_mul_tangleMetric_le_of_walk hK₁.2.1 ins₁ θ₁ hax_K ha_K W hW_lt
          hax_sub ha_sub
        rw [← hd₁ ax hax a ha, ← pointDist_eq_of_mem_atom (d := d₁) hax ha hx_ax hσa] at hle2
        have hlt_σ := hltZ σ hσZ
        omega
      have hAtomsW : ∀ a ∈ H₁.A, (a ∩ (walkDrawing K₁ W).U).Nonempty → a ∈ H₂.A := by
        intro a ha ⟨σ, hσa, hσU⟩
        exact hAtomsInW a ha ⟨σ, hσa, Or.inl hσU⟩
      obtain ⟨K₂, W', hK₂, hWD, hW'_len⟩ :=
        exists_radialDrawing_with_walk hS hMetric₂.1.1 hK₁ W hAtomsW
      obtain ⟨ins₂, hins₂⟩ := exists_derivedSlope hMetric₂.1 hK₂.2.1
      let d₂_K₂ := tangleMetric H₂ K₂ ins₂ θ₂
      have hM₂_K₂ : HasTangleMetric H₂ θ₂ T₂ d₂_K₂ :=
        ⟨hMetric₂.1, K₂, ins₂, hK₂, hins₂, fun _ _ _ _ => rfl⟩
      obtain ⟨hd₂_eq_A, _, _⟩ :=
        tangleMetric_eq_of_hasTangleMetric hS hConn hMetric₂ hM₂_K₂
      have hins_eq : insWalk ins₁ K₁ W = insWalk ins₂ K₂ W' :=
        (theorem_4_1_proof H₀ H₁ H₂ K₁ K₂ θ₀ lam₁ lam₂ T₀ T₁ T₂ d₀ d₁ d₂ ins₁ ins₂
          hS hComp₁ hComp₂ hK₁ hins₁ hd₁ hK₂ hins₂ hd₂_eq_A).1 u u W W' hWD hW_lt (by omega)
      have hx_inW : (ax ∩ insWalk ins₁ K₁ W).Nonempty :=
        (GM14.theorem_3_1_proof hS hK₁ hins₁ hax_K W hW_lt).mp hax_sub
      have hy_inW : (ay ∩ insWalk ins₁ K₁ W).Nonempty :=
        (GM14.theorem_3_1_proof hS hK₁ hins₁ hay_K W hW_lt).mp hay_sub
      have hax_eq : ax' = ax :=
        atom_eq_of_mem hax' (hAtomsInW ax hax hx_inW) hx_ax' hx_ax
      have hay_eq : ay' = ay :=
        atom_eq_of_mem hay' (hAtomsInW ay hay hy_inW) hy_ay' hy_ay
      obtain ⟨ax'_K, hax'_K⟩ := exists_correspondingAtom hK₂.2.1 hax'
      obtain ⟨ay'_K, hay'_K⟩ := exists_correspondingAtom hK₂.2.1 hay'
      have hW'_lt : W'.length < 2 * θ₂ := by omega
      have hax'_sub : ax'_K ⊆ insWalk ins₂ K₂ W' :=
        (GM14.theorem_3_1_proof hS hK₂ hins₂ hax'_K W' hW'_lt).mpr (by rwa [hax_eq, ← hins_eq])
      have hay'_sub : ay'_K ⊆ insWalk ins₂ K₂ W' :=
        (GM14.theorem_3_1_proof hS hK₂ hins₂ hay'_K W' hW'_lt).mpr (by rwa [hay_eq, ← hins_eq])
      have hle2' := two_mul_tangleMetric_le_of_walk hK₂.2.1 ins₂ θ₂ hax'_K hay'_K W' hW'_lt
        hax'_sub hay'_sub
      change 2 * d₂_K₂ ax' ay' ≤ W'.length at hle2'
      rw [← hd₂_eq_A ax' hax' ay' hay', ← hpt₂] at hle2'
      omega
    · obtain ⟨_, K₀', ins₀', _, _, hd₀'⟩ := hMetric₂
      have hle_θ₂ : pointDist H₂ d₂ x y ≤ θ₂ := by
        rw [hpt₂, hd₀' ax' hax' ay' hay']
        exact tangleMetric_le_ord H₂ K₀' ins₀' θ₂ ax' ay'
      omega

private theorem isPreconnected_biUnion_of_mem {S : Type w} [TopologicalSpace S]
    {ι : Type*} {p : ι → Prop} {f : ι → Set S} {x₀ : S}
    (hx₀ : ∀ i, p i → x₀ ∈ f i) (hpre : ∀ i, p i → IsPreconnected (f i)) :
    IsPreconnected (⋃ i, ⋃ (_ : p i), f i) := by
  intro U V hU hV hcov ⟨x, hx, hxU⟩ ⟨y, hy, hyV⟩
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
  obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hy
  have hx₀_mem : x₀ ∈ ⋃ k, ⋃ (_ : p k), f k := mem_iUnion₂.mpr ⟨i, hi, hx₀ i hi⟩
  rcases hcov hx₀_mem with hx₀U | hx₀V
  · obtain ⟨z, hz, hzUV⟩ := hpre j hj U V hU hV
      (fun w hw => hcov (mem_iUnion₂.mpr ⟨j, hj, hw⟩)) ⟨x₀, hx₀ j hj, hx₀U⟩ ⟨y, hyj, hyV⟩
    exact ⟨z, mem_iUnion₂.mpr ⟨j, hj, hz⟩, hzUV⟩
  · obtain ⟨z, hz, hzUV⟩ := hpre i hi U V hU hV
      (fun w hw => hcov (mem_iUnion₂.mpr ⟨i, hi, hw⟩)) ⟨x, hxi, hxU⟩ ⟨x₀, hx₀ i hi, hx₀V⟩
    exact ⟨z, mem_iUnion₂.mpr ⟨i, hi, hz⟩, hzUV⟩

/-- Every atom `a ∈ Γ.A` of a drawing `Γ` is preconnected. -/
theorem atom_isPreconnected {S : Type w} [TopologicalSpace S] {Γ : Drawing S} {a : Set S}
    (ha : a ∈ Γ.A) : IsPreconnected a := by
  rcases ha with (⟨v, _, rfl⟩ | he) | hr
  · exact isPreconnected_singleton
  · exact he.2.2.1.isConnected.isPreconnected
  · exact region_isPreconnected hr

/-- For any walk `W` of `Γ.toGraph`, `(walkDrawing Γ W).U` is preconnected. -/
theorem isPreconnected_walkDrawing_U {S : Type w} [TopologicalSpace S] [T1Space S]
    (Γ : Drawing S) {u v : S} (W : GraphWalk Γ.toGraph u v) :
    IsPreconnected (walkDrawing Γ W).U := by
  induction W with
  | @nil a ha =>
    have hEq : (walkDrawing Γ (.nil ha)).U = {a} := by
      rw [Drawing.U_eq, walkDrawing_V, walkDrawing_E]
      ext x
      simp [GraphWalk.support_nil]
    rw [hEq]
    exact isPreconnected_singleton
  | @cons a w b e hlink r ih =>
    have hEq : (walkDrawing Γ (.cons hlink r)).U = closure e ∪ (walkDrawing Γ r).U := by
      rw [Drawing.U_eq, Drawing.U_eq, walkDrawing_V, walkDrawing_E, walkDrawing_V, walkDrawing_E]
      ext x
      simp only [GraphWalk.support_cons, List.mem_cons, GraphWalk.edges_cons, mem_union,
        mem_ofPred_eq, mem_iUnion, exists_prop]
      constructor
      · rintro ((rfl | hxr) | ⟨f, rfl | hfr, hxf⟩)
        · left
          have : x ∈ closure e ∩ Γ.V := by rw [hlink.2.2.2]; simp
          exact this.1
        · exact Or.inr (Or.inl hxr)
        · exact Or.inl hxf
        · exact Or.inr (Or.inr ⟨f, hfr, hxf⟩)
      · rintro (hxe | (hxr | ⟨f, hfr, hxf⟩))
        · exact Or.inr ⟨e, Or.inl rfl, hxe⟩
        · exact Or.inl (Or.inr hxr)
        · exact Or.inr ⟨f, Or.inr hfr, hxf⟩
    rw [hEq]
    have he_pre : IsPreconnected (closure e) := hlink.1.2.2.1.isConnected.isPreconnected.closure
    have hw_e : w ∈ closure e := by
      have : w ∈ closure e ∩ Γ.V := by rw [hlink.2.2.2]; simp
      exact this.1
    have hw_r : w ∈ (walkDrawing Γ r).U :=
      (walkDrawing Γ r).V_subset_U (by rw [walkDrawing_V]; exact r.start_mem_support)
    exact he_pre.union' ⟨w, hw_e, hw_r⟩ ih

/-- For a derived slope `ins` of `(H, K, θ, T)` and a closed walk `W` of `K` with
`W.length < 2 * θ`, `insWalk ins K W` is closed and preconnected. -/
theorem isClosed_and_isPreconnected_insWalk {S : Type w} [TopologicalSpace S] [T2Space S]
    {H K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Drawing S → Set S}
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    {u : S} (W : GraphWalk K.toGraph u u) (hW_lt : W.length < 2 * θ) :
    IsClosed (insWalk ins K W) ∧ IsPreconnected (insWalk ins K W) := by
  let D := walkDrawing K W
  have hDK : D.IsSubdrawing K := GM11.walkDrawing_isSubdrawing K W
  have hfinC : {C : Drawing S | C.IsCircuit ∧ C.IsSubdrawing D}.Finite := by
    refine Set.Finite.of_finite_image (f := fun C : Drawing S => (C.V, C.E)) ?_ ?_
    · refine (D.finite_V.finite_subsets.prod D.finite_edges.finite_subsets).subset ?_
      rintro _ ⟨C, ⟨-, hs'⟩, rfl⟩
      exact ⟨hs'.1, hs'.2⟩
    · intro C _ C' _ h
      exact Drawing.ext_of_V_E (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hClen : ∀ C : Drawing S, C.IsSubdrawing D → C.length < 2 * θ := by
    intro C hCs
    have hsub : C.E ⊆ {e | e ∈ W.edges} := by
      have := hCs.2
      rwa [GM11.walkDrawing_E] at this
    have hle : C.length ≤ W.length :=
      calc C.E.ncard ≤ ({e | e ∈ W.edges} : Set (Set S)).ncard :=
            Set.ncard_le_ncard hsub (List.finite_toSet _)
        _ ≤ W.edges.length := by
            rw [show ({e | e ∈ W.edges} : Set (Set S)) = ↑W.edges.toFinset by ext; simp,
              Set.ncard_coe_finset]
            exact List.toFinset_card_le _
        _ = W.length := rfl
    exact lt_of_le_of_lt hle hW_lt
  have hcl : IsClosed (insWalk ins K W) := by
    refine D.isClosed_U.union (hfinC.isClosed_biUnion fun C ⟨hC, hCs⟩ => ?_)
    exact (hins C hC (hCs.trans hDK) (hClen C hCs)).1.isClosed
  refine ⟨hcl, ?_⟩
  have hDU_pre : IsPreconnected D.U := isPreconnected_walkDrawing_U K W
  have huD : u ∈ D.U := D.V_subset_U (by rw [walkDrawing_V]; exact W.start_mem_support)
  have hEq : insWalk ins K W =
      D.U ∪ ⋃ C ∈ {C : Drawing S | C.IsCircuit ∧ C.IsSubdrawing D}, (D.U ∪ ins C) := by
    ext x
    simp only [insWalk, insOf, mem_union, mem_iUnion, exists_prop, mem_ofPred_eq]
    constructor
    · rintro (hx | ⟨C, hC, hxC⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨C, hC, Or.inr hxC⟩
    · rintro (hx | ⟨C, hC, hx | hxC⟩)
      · exact Or.inl hx
      · exact Or.inl hx
      · exact Or.inr ⟨C, hC, hxC⟩
  rw [hEq]
  by_cases hC_ne : {C : Drawing S | C.IsCircuit ∧ C.IsSubdrawing D}.Nonempty
  · obtain ⟨C₀, hC₀⟩ := hC_ne
    refine hDU_pre.union' ⟨u, huD, mem_iUnion₂.mpr ⟨C₀, hC₀, Or.inl huD⟩⟩ ?_
    refine isPreconnected_biUnion_of_mem (x₀ := u) ?_ ?_
    · intro C _
      exact Or.inl huD
    · intro C ⟨hC, hCs⟩
      obtain ⟨hDisc, hbd, _⟩ := hins C hC (hCs.trans hDK) (hClen C hCs)
      obtain ⟨e, heC⟩ := GM11.IsCircuit.E_nonempty hC
      obtain ⟨y, hye⟩ := (hCs.trans hDK).2 heC |>.1
      have hyCU : y ∈ C.U := (heC.2.1 hye).1
      have hyDU : y ∈ D.U := hCs.U_subset hyCU
      have hy_ins : y ∈ ins C := by
        have : y ∈ subBd (ins C) := hbd ▸ hyCU
        exact hDisc.isClosed.closure_subset_iff.mpr Subset.rfl this.1
      exact hDU_pre.union' ⟨y, hyDU, hy_ins⟩
        (IsClosedDisc.isPathConnected hDisc).isConnected.isPreconnected
  · have hEmp : (⋃ C ∈ {C : Drawing S | C.IsCircuit ∧ C.IsSubdrawing D}, (D.U ∪ ins C)) = ∅ := by
      simp [Set.not_nonempty_iff_eq_empty.mp hC_ne]
    rw [hEmp, union_empty]
    exact hDU_pre

/-- If `e ∈ H.E`, `v ∈ H.V ∩ closure e`, `z ∈ H.A`, and `z ≠ e`, then `d z {v} ≤ d z e`. -/
theorem dist_vertex_le_dist_edge_of_ne {S : Type w} [TopologicalSpace S] [T2Space S]
    {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (_hS : IsClosedSurface S) (hMetric : HasTangleMetric H θ T d)
    {z e : Set S} {v : S} (hz : z ∈ H.A) (he : e ∈ H.E) (hv : v ∈ H.V) (hve : v ∈ closure e)
    (hne : z ≠ e) :
    d z {v} ≤ d z e := by
  obtain ⟨_, K, ins, hK, hins, hd⟩ := hMetric
  have heA : e ∈ H.A := Or.inl (Or.inr he)
  have hvA : ({v} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
  rw [hd z hz {v} hvA, hd z hz e heA]
  by_cases hlt : tangleMetric H K ins θ z e < θ
  · obtain ⟨u, W, z', e', hz', he', hW_lt, hW_len, hz_sub, he_sub⟩ :=
      exists_walk_of_tangleMetric_lt hK.2.1 ins hne hlt
    obtain ⟨hcl, _⟩ := isClosed_and_isPreconnected_insWalk hins W hW_lt
    have hv_cor : IsCorrespondingAtom H K {v} {v} :=
      ⟨hvA, Or.inl (Or.inl ⟨v, hK.2.1.2.1 hv, rfl⟩), Or.inl ⟨v, hv, rfl, rfl⟩⟩
    have he_sub_W : e ⊆ insWalk ins K W := by
      rcases he'.2.2 with ⟨w, _, hEq, _⟩ | ⟨_, _, hsub⟩ | ⟨hr, _, _, _⟩
      · exfalso
        have hve_mem : v ∈ e := by
          rw [hEq] at hve ⊢
          rwa [isClosed_singleton.closure_eq] at hve
        exact (he.2.1 hve_mem).2 hv
      · exact hsub.trans he_sub
      · exfalso
        obtain ⟨y, hye⟩ := he.1
        exact region_subset hr hye (he.2.1 hye).1
    have hv_sub : ({v} : Set S) ⊆ insWalk ins K W :=
      singleton_subset_iff.mpr (hcl.closure_subset_iff.mpr he_sub_W hve)
    have hle2 := two_mul_tangleMetric_le_of_walk hK.2.1 ins θ hz' hv_cor W hW_lt hz_sub hv_sub
    omega
  · have := tangleMetric_le_ord H K ins θ z {v}
    omega

/-- If `e ∈ H.E`, `v ∈ H.V ∩ closure e`, `z ∈ H.A`, `2 ≤ lam`, and `d z e ≤ lam`, then
`d z {v} ≤ lam`. -/
theorem dist_vertex_le_of_dist_edge_le
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {H : Drawing S} {θ lam : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S) (hMetric : HasTangleMetric H θ T d)
    {z e : Set S} {v : S} (hz : z ∈ H.A) (he : e ∈ H.E) (hv : v ∈ H.V) (hve : v ∈ closure e)
    (hlam : 2 ≤ lam) (hle : d z e ≤ lam) :
    d z {v} ≤ lam := by
  by_cases hze : z = e
  · subst hze
    obtain ⟨_, _, _, hd_symm, _, _, hd_inc_e⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
    have h1 : d {v} z ≤ 2 := hd_inc_e v hv z he hve
    rw [hd_symm z (Or.inl (Or.inr he)) {v} (Or.inl (Or.inl ⟨v, hv, rfl⟩))]
    omega
  · exact (dist_vertex_le_dist_edge_of_ne hS hMetric hz he hv hve hze).trans hle

/-- The union of all atoms `a ∈ H.A` with `d z a ≤ lam` (Graph Minors XV, proof of `(5.2)`,
page 130: `Z₁` and `Z₂`). -/
def atomZone {S : Type w} [TopologicalSpace S]
    (H : Drawing S) (d : Set S → Set S → ℕ) (z : Set S) (lam : ℕ) : Set S :=
  {σ : S | ∃ a ∈ H.A, d z a ≤ lam ∧ σ ∈ a}

theorem mem_atomZone_iff_of_mem_atom {S : Type w} [TopologicalSpace S]
    {H : Drawing S} {d : Set S → Set S → ℕ} {z a : Set S} {lam : ℕ} {σ : S}
    (ha : a ∈ H.A) (hσ : σ ∈ a) :
    σ ∈ atomZone H d z lam ↔ d z a ≤ lam := by
  refine ⟨fun ⟨b, hb, hle, hσb⟩ => ?_, fun hle => ⟨a, ha, hle, hσ⟩⟩
  rwa [← atom_eq_of_mem ha hb hσ hσb] at hle

theorem atom_subset_or_disjoint_atomZone {S : Type w} [TopologicalSpace S]
    {H H' : Drawing S} {d : Set S → Set S → ℕ} {z : Set S} {lam : ℕ}
    (hAtoms : ∀ a ∈ H.A, lam < d z a → a ∈ H'.A) :
    (∀ a ∈ H.A, (d z a ≤ lam ∧ a ⊆ atomZone H d z lam) ∨
      (lam < d z a ∧ Disjoint a (atomZone H d z lam) ∧ a ∈ H'.A)) ∧
    (∀ a' ∈ H'.A, a' ⊆ atomZone H d z lam ∨
      (Disjoint a' (atomZone H d z lam) ∧ a' ∈ H.A ∧ lam < d z a')) := by
  refine ⟨fun a ha => ?_, fun a' ha' => ?_⟩
  · by_cases hle : d z a ≤ lam
    · exact Or.inl ⟨hle, fun σ hσ => ⟨a, ha, hle, hσ⟩⟩
    · have hlt : lam < d z a := Nat.lt_of_not_le hle
      refine Or.inr ⟨hlt, Set.disjoint_left.mpr fun σ hσ hZ => ?_, hAtoms a ha hlt⟩
      exact hle ((mem_atomZone_iff_of_mem_atom ha hσ).mp hZ)
  · by_cases hsub : a' ⊆ atomZone H d z lam
    · exact Or.inl hsub
    · obtain ⟨σ, hσa', hσnot⟩ := Set.not_subset.mp hsub
      obtain ⟨a, ha, hσa⟩ := exists_atom_of_point H σ
      have hlt : lam < d z a := by
        by_contra hnot
        exact hσnot ⟨a, ha, Nat.le_of_not_lt hnot, hσa⟩
      have haH' : a ∈ H'.A := hAtoms a ha hlt
      have heq : a' = a := atom_eq_of_mem ha' haH' hσa' hσa
      subst heq
      refine Or.inr ⟨Set.disjoint_left.mpr fun x hx hZ => ?_, ha, hlt⟩
      exact Nat.not_le.mpr hlt ((mem_atomZone_iff_of_mem_atom ha hx).mp hZ)

/-- The set `H.A` of atoms of a drawing `H` on a connected closed surface `S` is finite. -/
theorem finite_A {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (H : Drawing S) : H.A.Finite :=
  ((H.finite_V.image _).union H.finite_edges).union (GM11.finite_R hS H)

/-- Every point `y ∈ closure (atomZone H d z lam)` lies in an atom `a_y ∈ H.A` with
`d z a_y ≤ lam + 3` and within distance `≤ 3` of some point `σ ∈ atomZone H d z lam`. -/
theorem closure_atomZone_props
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {H : Drawing S} {θ lam : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z : Set S}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (hMetric : HasTangleMetric H θ T d) (hz : z ∈ H.A) :
    ∀ y ∈ closure (atomZone H d z lam),
      (∃ σ ∈ atomZone H d z lam, pointDist H d σ y ≤ 3) ∧
      ∀ a_y ∈ H.A, y ∈ a_y → d z a_y ≤ lam + 3 := by
  obtain ⟨_, _, _, hd_symm, hd_tri, _⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
  have hd_inc := atom_closure_dist_le_three hS hMetric
  have hfin : {a ∈ H.A | d z a ≤ lam}.Finite := (finite_A hS H).subset fun _ h => h.1
  have hEq : atomZone H d z lam = ⋃ a ∈ {a ∈ H.A | d z a ≤ lam}, a := by
    ext x
    simp [atomZone, and_assoc]
  intro y hy
  rw [hEq, hfin.closure_biUnion] at hy
  obtain ⟨a, ⟨ha, hle⟩, hya⟩ := mem_iUnion₂.mp hy
  obtain ⟨σ, hσa⟩ := atom_nonempty ha
  obtain ⟨a_y, ha_y, hy_ay⟩ := exists_atom_of_point H y
  have hinc : d a_y a ≤ 3 := hd_inc a_y ha_y a ha ⟨y, hy_ay, hya⟩
  have hsym : d a a_y = d a_y a := hd_symm a ha a_y ha_y
  refine ⟨⟨σ, ⟨a, ha, hle, hσa⟩, ?_⟩, fun b hb hyb => ?_⟩
  · rw [pointDist_eq_of_mem_atom ha ha_y hσa hy_ay]
    omega
  · rw [atom_eq_of_mem hb ha_y hyb hy_ay]
    have htri := hd_tri z hz a ha a_y ha_y
    omega

/-- For any `k : ℕ`, `frontier (atomZone H d z k)` is contained in `H.U` and every point `y` on it
lies in an atom `a_y ∈ H.A` with `k ≤ d z a_y + 2` and `d z a_y ≤ k + 3`. -/
theorem frontier_atomZone_subset_U
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z : Set S} (k : ℕ)
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (hMetric : HasTangleMetric H θ T d) (hz : z ∈ H.A) :
    ∀ y ∈ frontier (atomZone H d z k),
      y ∈ H.U ∧ ∀ a_y ∈ H.A, y ∈ a_y → k ≤ d z a_y + 2 ∧ d z a_y ≤ k + 3 := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨_, _, _, _, hd_tri, _⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
  have hd_inc := atom_closure_dist_le_three hS hMetric
  have hfin_gt : {b ∈ H.A | k < d z b}.Finite := (finite_A hS H).subset fun _ h => h.1
  have hCompl : (atomZone H d z k)ᶜ = ⋃ b ∈ {b ∈ H.A | k < d z b}, b := by
    ext x
    simp only [mem_compl_iff, mem_iUnion, exists_prop, mem_ofPred_eq]
    obtain ⟨b, hb, hxb⟩ := exists_atom_of_point H x
    rw [mem_atomZone_iff_of_mem_atom hb hxb, not_le]
    exact ⟨fun hlt => ⟨b, ⟨hb, hlt⟩, hxb⟩,
      fun ⟨b', ⟨hb', hlt⟩, hxb'⟩ => atom_eq_of_mem hb hb' hxb hxb' ▸ hlt⟩
  intro y ⟨hy_cl, hy_not_int⟩
  have hy_cl_compl : y ∈ closure (atomZone H d z k)ᶜ := by rwa [closure_compl]
  rw [hCompl, hfin_gt.closure_biUnion] at hy_cl_compl
  obtain ⟨b, ⟨hb, hgt⟩, hyb⟩ := mem_iUnion₂.mp hy_cl_compl
  have hle1 := (closure_atomZone_props hS hConn hMetric hz y hy_cl).2
  refine ⟨?_, fun a_y ha_y hy_ay => ⟨?_, hle1 a_y ha_y hy_ay⟩⟩
  · by_contra hyU
    obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem hyU
    have hrA : r ∈ H.A := Or.inr hr
    by_cases hle : d z r ≤ k
    · have hr_sub : r ⊆ atomZone H d z k := fun x hx => ⟨r, hrA, hle, hx⟩
      exact hy_not_int (mem_interior.mpr ⟨r, hr_sub, region_isOpen hr, hyr⟩)
    · have hr_disj : Disjoint r (atomZone H d z k) :=
        Set.disjoint_left.mpr fun x hx hZ => hle ((mem_atomZone_iff_of_mem_atom hrA hx).mp hZ)
      exact Set.disjoint_left.mp hr_disj
        (mem_closure_iff.mp hy_cl r (region_isOpen hr) hyr).choose_spec.1
        (mem_closure_iff.mp hy_cl r (region_isOpen hr) hyr).choose_spec.2
  · have hinc : d a_y b ≤ 3 := hd_inc a_y ha_y b hb ⟨y, hy_ay, hyb⟩
    have htri := hd_tri z hz a_y ha_y b hb
    omega

/-- When `lam < θ`, `atomZone H d z lam` is preconnected. -/
theorem isPreconnected_atomZone
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {H : Drawing S} {θ lam : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z : Set S}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (hMetric : HasTangleMetric H θ T d) (hz : z ∈ H.A) (hlam : lam < θ) :
    IsPreconnected (atomZone H d z lam) := by
  obtain ⟨_, hd_refl, _, _, _, _⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
  obtain ⟨_, K, ins, hK, hins, hd⟩ := hMetric
  obtain ⟨τ, hτz⟩ := atom_nonempty hz
  have hpiece : ∀ a ∈ H.A, d z a ≤ lam →
      ∃ C : Set S, IsPreconnected C ∧ τ ∈ C ∧ a ⊆ C ∧ C ⊆ atomZone H d z lam := by
    intro a ha hle
    by_cases hza : z = a
    · subst hza
      exact ⟨z, atom_isPreconnected hz, hτz, Subset.rfl, fun x hx => ⟨z, hz, hle, hx⟩⟩
    · have htm_lt : tangleMetric H K ins θ z a < θ := by
        rw [← hd z hz a ha]
        omega
      obtain ⟨u, W, z', a', hz', ha', hW_lt, hW_len, hz_sub, ha_sub⟩ :=
        exists_walk_of_tangleMetric_lt hK.2.1 ins hza htm_lt
      rw [← hd z hz a ha] at hW_len
      obtain ⟨_, hW_pre⟩ := isClosed_and_isPreconnected_insWalk hins W hW_lt
      obtain ⟨σz, hσz, hσzW⟩ := (GM14.theorem_3_1_proof hS hK hins hz' W hW_lt).mp hz_sub
      obtain ⟨σa, hσa, hσaW⟩ := (GM14.theorem_3_1_proof hS hK hins ha' W hW_lt).mp ha_sub
      have hW_sub_Z : insWalk ins K W ⊆ atomZone H d z lam := by
        intro x hxW
        obtain ⟨b, hb, hxb⟩ := exists_atom_of_point H x
        obtain ⟨b', hb'⟩ := exists_correspondingAtom hK.2.1 hb
        have hb'_sub : b' ⊆ insWalk ins K W :=
          (GM14.theorem_3_1_proof hS hK hins hb' W hW_lt).mpr ⟨x, hxb, hxW⟩
        have hle2 := two_mul_tangleMetric_le_of_walk hK.2.1 ins θ hz' hb' W hW_lt hz_sub hb'_sub
        rw [← hd z hz b hb] at hle2
        exact ⟨b, hb, by omega, hxb⟩
      have hzw_pre : IsPreconnected (z ∪ insWalk ins K W) :=
        (atom_isPreconnected hz).union' ⟨σz, hσz, hσzW⟩ hW_pre
      have hzaw_pre : IsPreconnected (z ∪ insWalk ins K W ∪ a) :=
        hzw_pre.union' ⟨σa, Or.inr hσaW, hσa⟩ (atom_isPreconnected ha)
      refine ⟨z ∪ insWalk ins K W ∪ a, hzaw_pre, Or.inl (Or.inl hτz), subset_union_right, ?_⟩
      refine union_subset (union_subset ?_ hW_sub_Z) (fun x hx => ⟨a, ha, hle, hx⟩)
      exact fun x hx => ⟨z, hz, by rw [hd_refl z hz]; exact Nat.zero_le _, hx⟩
  choose! C hC_pre hτC haC hCZ using hpiece
  have hEq : atomZone H d z lam = ⋃ a ∈ {a ∈ H.A | d z a ≤ lam}, C a := by
    apply Subset.antisymm
    · rintro x ⟨a, ha, hle, hxa⟩
      exact mem_iUnion₂.mpr ⟨a, ⟨ha, hle⟩, haC a ha hle hxa⟩
    · exact iUnion₂_subset fun a ⟨ha, hle⟩ => hCZ a ha hle
  rw [hEq]
  exact isPreconnected_biUnion_of_mem (x₀ := τ) (fun a ⟨ha, hle⟩ => hτC a ha hle)
    (fun a ⟨ha, hle⟩ => hC_pre a ha hle)

/-- When `6 ≤ lam`, there is a region `r ∈ H.R` with `closure r ⊆ atomZone H d z lam`. -/
theorem exists_region_closure_subset_atomZone
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {H : Drawing S} {θ lam : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z : Set S}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (hMetric : HasTangleMetric H θ T d) (hz : z ∈ H.A) (hlam : 6 ≤ lam) :
    ∃ r ∈ H.R, closure r ⊆ atomZone H d z lam := by
  obtain ⟨_, _, _, hd_symm, hd_tri, _⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
  have hd_inc := atom_closure_dist_le_three hS hMetric
  obtain ⟨σ, hσz⟩ := atom_nonempty hz
  obtain ⟨r, hr, hσr⟩ := exists_region_closure_mem_of_closedSurface hS H σ
  have hrA : r ∈ H.A := Or.inr hr
  have hdr : d z r ≤ 3 := hd_inc z hz r hrA ⟨σ, hσz, hσr⟩
  refine ⟨r, hr, fun y hy => ?_⟩
  obtain ⟨a_y, ha_y, hy_ay⟩ := exists_atom_of_point H y
  have h1 : d a_y r ≤ 3 := hd_inc a_y ha_y r hrA ⟨y, hy_ay, hy⟩
  have h2 : d r a_y = d a_y r := hd_symm r hrA a_y ha_y
  have htri := hd_tri z hz r hrA a_y ha_y
  exact ⟨a_y, ha_y, by omega, hy_ay⟩

/-- If `r ∈ Γ.R` is a region of `Γ` and `Γ'` is a drawing with `Disjoint r Γ'.U` and
`closure r \ r ⊆ Γ'.U`, then `r ∈ Γ'.R`. -/
theorem mem_R_of_disjoint_U_of_frontier_subset {S : Type w} [TopologicalSpace S]
    [LocallyConnectedSpace S] {Γ Γ' : Drawing S} {r : Set S}
    (hr : r ∈ Γ.R) (hdisj : Disjoint r Γ'.U) (hbd : closure r \ r ⊆ Γ'.U) :
    r ∈ Γ'.R := by
  obtain ⟨x, hxr⟩ := region_nonempty hr
  have hxU' : x ∉ Γ'.U := disjoint_left.mp hdisj hxr
  refine (GM11.mem_R_iff _).mpr ⟨x, hxU', subset_antisymm ?_ ?_⟩
  · exact (region_isPreconnected hr).subset_connectedComponentIn hxr
      fun y hy => ⟨mem_univ _, disjoint_left.mp hdisj hy⟩
  · have hcov : connectedComponentIn (univ \ Γ'.U) x ⊆ r ∪ (closure r)ᶜ := by
      intro y hy
      by_cases hyc : y ∈ closure r
      · refine Or.inl ?_
        by_contra hyr
        exact (connectedComponentIn_subset _ _ hy).2 (hbd ⟨hyc, hyr⟩)
      · exact Or.inr hyc
    refine isPreconnected_connectedComponentIn.subset_left_of_subset_union (region_isOpen hr)
      isClosed_closure.isOpen_compl ?_ hcov ⟨x, mem_connectedComponentIn ⟨mem_univ _, hxU'⟩, hxr⟩
    exact disjoint_left.mpr fun y hy h => h (subset_closure hy)

/-- A simple walk drawing `walkDrawing P W` (`W.IsSimple`) contains no circuit subdrawing. -/
theorem not_isCircuit_subdrawing_walkDrawing {S : Type w} [TopologicalSpace S] [T2Space S]
    (P : Drawing S) {u v : S} {W : GraphWalk P.toGraph u v} (hW : W.IsSimple)
    {C : Drawing S} (hC : C.IsCircuit) (hCs : C.IsSubdrawing (walkDrawing P W)) : False := by
  induction W with
  | @nil a ha =>
    obtain ⟨e, heC⟩ := GM11.IsCircuit.E_nonempty hC
    have heW : e ∈ (walkDrawing P (.nil ha)).E := hCs.2 heC
    rw [GM11.walkDrawing_E] at heW
    simp at heW
  | @cons a w b e hlink r ih =>
    have hnd := List.nodup_cons.mp hW
    have ha_not : a ∉ r.support := hnd.1
    have hr_sim : r.IsSimple := hnd.2
    have haw : a ≠ w := fun hEq => ha_not (hEq ▸ r.start_mem_support)
    have hends_r : ∀ f ∈ r.edges, a ∉ closure f ∩ P.V := by
      intro f hf ha_f
      have hfP : f ∈ P.E :=
        (GM11.walkDrawing_isSubdrawing P r).2 (by rw [GM11.walkDrawing_E]; exact hf)
      obtain ⟨x, y, hxy⟩ := (P.toGraph.edge_mem_iff_exists_isLink f).mp hfP
      rw [hxy.2.2.2] at ha_f
      rcases ha_f with rfl | hEq
      · exact ha_not (r.left_mem_support_of_mem_edges hf hxy)
      · rw [mem_singleton_iff.mp hEq] at ha_not
        exact ha_not (r.left_mem_support_of_mem_edges hf hxy.symm)
    by_cases heC : e ∈ C.E
    · have hCP : C.IsSubdrawing P := hCs.trans (GM11.walkDrawing_isSubdrawing P (.cons hlink r))
      have haCV : a ∈ C.V := by
        have : a ∈ closure e ∩ C.V := by
          rw [hCP.closure_inter_V heC, hlink.2.2.2]; simp
        exact this.2
      obtain ⟨W_C, hWC_circ, hWC_pos, hCV, hCE⟩ := GM11.exists_walk_at hC haCV
      cases W_C with
      | nil _ => simp at hWC_pos
      | @cons _ u₁ _ f₁ hl₁ r₁ =>
        have hf₁C : f₁ ∈ C.E := hl₁.1
        have hf₁W : f₁ = e ∨ f₁ ∈ r.edges := by
          have := hCs.2 hf₁C
          rwa [GM11.walkDrawing_E, mem_ofPred_eq, GraphWalk.edges_cons, List.mem_cons] at this
        have ha_f₁ : a ∈ closure f₁ ∩ P.V := by
          rw [← hCP.closure_inter_V hf₁C, hl₁.2.2.2]; simp
        have hf₁_eq : f₁ = e := hf₁W.resolve_right fun hfr => hends_r f₁ hfr ha_f₁
        have hu₁_eq : u₁ = w := by
          have hpair : ({a, u₁} : Set S) = {a, w} := by
            rw [← hl₁.2.2.2, hCP.closure_inter_V hf₁C, hf₁_eq, hlink.2.2.2]
          have : u₁ ∈ ({a, w} : Set S) := hpair ▸ Or.inr rfl
          rcases this with rfl | hEq
          · exfalso
            have hw_mem : w ∈ ({u₁, u₁} : Set S) := hpair.symm ▸ Or.inr rfl
            simp only [pair_eq_singleton, mem_singleton_iff] at hw_mem
            exact haw hw_mem.symm
          · exact mem_singleton_iff.mp hEq
        have hr₁_rev_pos : 0 < r₁.reverse.length := by
          rw [GraphWalk.length_reverse]
          cases r₁ with
          | nil _ => exact (haw hu₁_eq).elim
          | cons _ _ => simp
        generalize hrev : r₁.reverse = R₁
        cases R₁ with
        | nil _ => rw [hrev] at hr₁_rev_pos; simp at hr₁_rev_pos
        | @cons _ u₂ _ f₂ hl₂ r₂ =>
          have hf₂_r₁ : f₂ ∈ r₁.edges := by
            have : f₂ ∈ r₁.reverse.edges := by rw [hrev]; exact List.mem_cons_self
            rwa [GraphWalk.edges_reverse, List.mem_reverse] at this
          have hf₂C : f₂ ∈ C.E := hl₂.1
          have hf₂W : f₂ = e ∨ f₂ ∈ r.edges := by
            have := hCs.2 hf₂C
            rwa [GM11.walkDrawing_E, mem_ofPred_eq, GraphWalk.edges_cons, List.mem_cons] at this
          have ha_f₂ : a ∈ closure f₂ ∩ P.V := by
            rw [← hCP.closure_inter_V hf₂C, hl₂.2.2.2]; simp
          have hf₂_eq : f₂ = e := hf₂W.resolve_right fun hfr => hends_r f₂ hfr ha_f₂
          have hnd_ed := (List.nodup_cons.mp hWC_circ.2).1
          exact hnd_ed (hf₁_eq.trans hf₂_eq.symm ▸ hf₂_r₁)
    · refine ih hr_sim ⟨fun x hxC => ?_, fun f hfC => ?_⟩
      · obtain ⟨W_x, _, hWx_pos, _, _⟩ := GM11.exists_walk_at hC hxC
        cases W_x with
        | nil _ => simp at hWx_pos
        | @cons _ _ _ f hl _ =>
          have hfC : f ∈ C.E := hl.1
          have hfW : f = e ∨ f ∈ r.edges := by
            have := hCs.2 hfC
            rwa [GM11.walkDrawing_E, mem_ofPred_eq, GraphWalk.edges_cons, List.mem_cons] at this
          have hfr : f ∈ r.edges := hfW.resolve_left fun hEq => heC (hEq ▸ hfC)
          have hCP : C.IsSubdrawing P := hCs.trans (GM11.walkDrawing_isSubdrawing P (.cons hlink r))
          have hx_f : x ∈ closure f ∩ P.V := by
            rw [← hCP.closure_inter_V hfC, hl.2.2.2]; simp
          have hx_ne_a : x ≠ a := fun hEq => hends_r f hfr (hEq ▸ hx_f)
          have hxW : x = a ∨ x ∈ r.support := by
            have := hCs.1 hxC
            rwa [GM11.walkDrawing_V, mem_ofPred_eq, GraphWalk.support_cons, List.mem_cons] at this
          rw [GM11.walkDrawing_V]
          exact hxW.resolve_left hx_ne_a
      · have hfW : f = e ∨ f ∈ r.edges := by
          have := hCs.2 hfC
          rwa [GM11.walkDrawing_E, mem_ofPred_eq, GraphWalk.edges_cons, List.mem_cons] at this
        rw [GM11.walkDrawing_E]
        exact hfW.resolve_left fun hEq => heC (hEq ▸ hfC)

/-- For any dial `Δ` of `F, Γ` with `F ∩ Γ.U ⊆ Γ.V`, `Γ.interSet Δ` contains no circuit
subdrawing. -/
theorem not_isCircuit_subdrawing_of_isDial {S : Type w} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {F Δ : Set S} (hU : F ∩ Γ.U ⊆ Γ.V) (hDial : IsDial Γ F Δ)
    {C : Drawing S} (hC : C.IsCircuit) (hCs : C.IsSubdrawing (Γ.interSet Δ)) : False := by
  rcases hDial.2.2 with hsub | ⟨u, v, _, _, hPath⟩
  · obtain ⟨e, heC⟩ := GM11.IsCircuit.E_nonempty hC
    have heΔ : e ∈ (Γ.interSet Δ).E := hCs.2 heC
    rw [Drawing.interSet, Drawing.span_E] at heΔ
    have he_pair : e ∈ Γ.E ∧ e ⊆ Δ := heΔ.1
    obtain ⟨_, hdV, heU, ⟨x, hxe⟩⟩ := GM11.PaintingOrDrawing.edge_props (Γ := .drawing Γ) he_pair.1
    exact Set.disjoint_left.mp hdV hxe (hU ⟨hsub ⟨he_pair.2 hxe, heU hxe⟩, heU hxe⟩)
  · let P := Γ.interSet Δ
    obtain ⟨W, hW, hPV, hPE⟩ := hPath
    have hEq : P = walkDrawing P W :=
      Drawing.ext_of_V_E (hPV.trans (GM11.walkDrawing_V P W).symm)
        (hPE.trans (GM11.walkDrawing_E P W).symm)
    exact not_isCircuit_subdrawing_walkDrawing P hW hC (hEq ▸ hCs)

/-- In a drawing `Γ` on a connected closed surface `S`, no dial `Δ` for an `O`-arc `F` (with
`F ∩ Γ.U ⊆ Γ.V`) can contain `closure r` for any region `r ∈ Γ.R`. -/
theorem not_closure_region_subset_of_isDial {S : Type w} [TopologicalSpace S] [T2Space S]
    [ConnectedSpace S] (hS : IsClosedSurface S) {Γ : Drawing S} {F Δ : Set S}
    (hF : IsOArc F) (hU : F ∩ Γ.U ⊆ Γ.V) (hDial : IsDial Γ F Δ)
    {r : Set S} (hr : r ∈ Γ.R) : ¬ (closure r ⊆ Δ) := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  intro hsub_r
  have hr_mem : r ∈ (Γ.interSet Δ).R := by
    have hSub : (Γ.interSet Δ).IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
    refine mem_R_of_disjoint_U_of_frontier_subset hr
      (Set.disjoint_left.mpr fun x hxr hxU => region_subset hr hxr (hSub.U_subset hxU)) ?_
    rintro x ⟨hxr_cl, hxr⟩
    have hxU : x ∈ Γ.U := by
      rcases GM11.closure_region_subset hr hxr_cl with h | h
      · exact (hxr h).elim
      · exact h
    by_cases hxV : x ∈ Γ.V
    · refine (Γ.interSet Δ).V_subset_U ?_
      rw [Drawing.interSet, Drawing.span_V, Drawing.spanV]
      exact Or.inl ⟨⟨hxV, hsub_r hxr_cl⟩, hxV⟩
    · obtain ⟨e, he, hxe⟩ := Γ.exists_edge_of_mem hxU hxV
      have he_r : e ⊆ closure r :=
        GM11.edge_subset_closure_of_incident hS he hr ⟨x, hxe, hxr_cl⟩
      have heΔ : e ∈ (Γ.interSet Δ).E := by
        rw [Drawing.interSet, Drawing.span_E]
        exact ⟨⟨he, he_r.trans hsub_r⟩, he⟩
      exact (heΔ.2.1 hxe).1
  have hCompl_ne : Δᶜ.Nonempty := by
    by_contra hEmp
    have hΔ_univ : Δ = univ := eq_univ_iff_forall.mpr fun x =>
      by_contra fun hx => hEmp ⟨x, hx⟩
    obtain ⟨φ⟩ := hF
    have hxF : (φ 1).1 ∈ F := (φ 1).2
    have hx_bd : (φ 1).1 ∈ subBd Δ := hDial.2.1.symm ▸ hxF
    rw [hΔ_univ, subBd, Set.sdiff_self, closure_empty, inter_empty] at hx_bd
    exact hx_bd
  obtain ⟨y, hy_out, hy_notU⟩ :=
    GM11.exists_notMem_U (Γ := Γ.interSet Δ) hS
      hDial.1.isClosed.isOpen_compl hCompl_ne
  obtain ⟨r_out, hr_out, hy_rout⟩ := exists_region_of_notMem hy_notU
  have hr_ne : r ≠ r_out := by
    rintro rfl
    exact hy_out (hsub_r (subset_closure hy_rout))
  exact hr_ne (GM11.region_eq_of_noCircuit hS (Γ := Γ.interSet Δ)
    (fun C hC hCs => not_isCircuit_subdrawing_of_isDial hU hDial hC hCs) hr_mem hr_out)

/-- In any drawing `Γ` on a `T1Space`, for every edge `e ∈ Γ.E`, `closure e ∩ Γ.V = closure e \ e`.
-/
theorem closure_inter_V_eq_diff {S : Type w} [TopologicalSpace S]
    (Γ : Drawing S) {e : Set S} (he : e ∈ Γ.E) :
    closure e ∩ Γ.V = closure e \ e := by
  ext x
  have h := Set.ext_iff.mp (Γ.closure_diff_V he) x
  simp only [mem_inter_iff, mem_sdiff] at h ⊢
  exact ⟨fun ⟨hx, hv⟩ => ⟨hx, fun hxe => (h.mpr hxe).2 hv⟩,
    fun ⟨hx, hnot⟩ => ⟨hx, by_contra fun hv => hnot (h.mp ⟨hx, hv⟩)⟩⟩

/-- In a 2-cell drawing `Γ` on a connected closed surface `S` with `Γ.E.Nonempty`, every vertex
`v ∈ Γ.V` lies in the closure of some edge `e ∈ Γ.E` (`Γ` has no isolated vertices). -/
theorem exists_edge_closure_mem_of_twoCell {S : Type w} [TopologicalSpace S] [T2Space S]
    [ConnectedSpace S] (hS : IsClosedSurface S) {Γ : Drawing S}
    (h2cell : (PaintingOrDrawing.drawing Γ).IsTwoCell) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V) :
    ∃ e ∈ Γ.E, v ∈ closure e := by
  obtain ⟨e₀, he₀⟩ := hE
  have hu₀_ex : (closure e₀ ∩ Γ.V).Nonempty := by
    rcases Γ.edge_cond e₀ he₀ with ⟨x, y, _, hcl, _⟩ | ⟨x, hcl, _⟩
    · rw [hcl]; exact ⟨x, Or.inl rfl⟩
    · rw [hcl]; exact ⟨x, rfl⟩
  obtain ⟨u₀, hu₀_cl, hu₀_V⟩ := hu₀_ex
  by_cases hvu : v = u₀
  · subst hvu; exact ⟨e₀, he₀, hu₀_cl⟩
  · obtain ⟨W⟩ := twoCell_toGraph_connected hS h2cell ⟨e₀, he₀⟩ hv hu₀_V
    cases W with
    | nil _ => exact (hvu rfl).elim
    | @cons _ w _ e hlink _ =>
      refine ⟨e, hlink.1, ?_⟩
      have : v ∈ closure e ∩ Γ.V := by rw [hlink.2.2.2]; exact Or.inl rfl
      exact this.1

/-- Helper lemma for `unionDrawing`: the arc components of `(Γ₁.U ∪ Γ₂.U) \ (Γ₁.V ∪ Γ₂.V)` are
`Γ₁.E ∪ Γ₂.E` when `Γ₁` and `Γ₂` only meet at `Γ₁.V ∩ Γ₂.V`. -/
theorem arcComponentsIn_union {S : Type w} [TopologicalSpace S]
    (Γ₁ Γ₂ : Drawing S)
    (h1 : ∀ e₁ ∈ Γ₁.E, closure e₁ ∩ Γ₂.V ⊆ Γ₁.V)
    (h2 : ∀ e₂ ∈ Γ₂.E, closure e₂ ∩ Γ₁.V ⊆ Γ₂.V)
    (h3 : ∀ e₁ ∈ Γ₁.E, ∀ e₂ ∈ Γ₂.E, closure e₁ ∩ closure e₂ ⊆ Γ₁.V ∩ Γ₂.V) :
    arcComponentsIn ((Γ₁.U ∪ Γ₂.U) \ (Γ₁.V ∪ Γ₂.V)) = Γ₁.E ∪ Γ₂.E := by
  have hdiff : (Γ₁.U ∪ Γ₂.U) \ (Γ₁.V ∪ Γ₂.V) = ⋃₀ (Γ₁.E ∪ Γ₂.E) := by
    ext x
    simp only [mem_sdiff, mem_union, not_or, mem_sUnion]
    constructor
    · rintro ⟨hx₁ | hx₂, hnot₁, hnot₂⟩
      · obtain ⟨e, he, hxe⟩ := Γ₁.exists_edge_of_mem hx₁ hnot₁
        exact ⟨e, Or.inl he, hxe⟩
      · obtain ⟨e, he, hxe⟩ := Γ₂.exists_edge_of_mem hx₂ hnot₂
        exact ⟨e, Or.inr he, hxe⟩
    · rintro ⟨e, he₁ | he₂, hxe⟩
      · have hxU : x ∈ Γ₁.U \ Γ₁.V := he₁.2.1 hxe
        refine ⟨Or.inl hxU.1, hxU.2, fun hxV₂ => hxU.2 (h1 e he₁ ⟨subset_closure hxe, hxV₂⟩)⟩
      · have hxU : x ∈ Γ₂.U \ Γ₂.V := he₂.2.1 hxe
        refine ⟨Or.inr hxU.1, fun hxV₁ => hxU.2 (h2 e he₂ ⟨subset_closure hxe, hxV₁⟩), hxU.2⟩
  have hpre : ∀ {D : Set S}, IsPreconnected D → D ⊆ ⋃₀ (Γ₁.E ∪ Γ₂.E) →
      ∀ {e : Set S}, e ∈ Γ₁.E ∪ Γ₂.E → ∀ {x : S}, x ∈ D → x ∈ e → D ⊆ e := by
    intro D hD hDsub e he x hxD hxe
    have hfin : (Γ₁.E ∪ Γ₂.E).Finite := Γ₁.finite_edges.union Γ₂.finite_edges
    set B : Set S := ⋃ f ∈ (Γ₁.E ∪ Γ₂.E) \ {e}, closure f
    have hBcl : IsClosed B :=
      (hfin.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure
    have hcover : D ⊆ closure e ∪ B := by
      intro y hy
      obtain ⟨f, hf, hyf⟩ := hDsub hy
      by_cases hfe : f = e
      · exact Or.inl (subset_closure (hfe ▸ hyf))
      · exact Or.inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hfe⟩, subset_closure hyf⟩)
    have hnotV : ∀ y ∈ D, y ∉ Γ₁.V ∪ Γ₂.V := by
      intro y hy
      have hy_diff : y ∈ (Γ₁.U ∪ Γ₂.U) \ (Γ₁.V ∪ Γ₂.V) := hdiff.symm ▸ hDsub hy
      exact hy_diff.2
    have hdisj : ∀ y ∈ D, y ∈ closure e → y ∉ B := by
      intro y hy hye hyB
      obtain ⟨f, ⟨hf, hfe⟩, hyf⟩ := mem_iUnion₂.mp hyB
      have hy_notV := hnotV y hy
      rcases he with he₁ | he₂ <;> rcases hf with hf₁ | hf₂
      · have h1' : y ∈ e := by
          rw [← Γ₁.closure_diff_V he₁]; exact ⟨hye, fun h => hy_notV (Or.inl h)⟩
        have h2' : y ∈ f := by
          rw [← Γ₁.closure_diff_V hf₁]; exact ⟨hyf, fun h => hy_notV (Or.inl h)⟩
        exact hfe (Γ₁.edge_eq_of_mem hf₁ he₁ h2' h1')
      · exact hy_notV (Or.inl (h3 e he₁ f hf₂ ⟨hye, hyf⟩).1)
      · exact hy_notV (Or.inl (h3 f hf₁ e he₂ ⟨hyf, hye⟩).1)
      · have h1' : y ∈ e := by
          rw [← Γ₂.closure_diff_V he₂]; exact ⟨hye, fun h => hy_notV (Or.inr h)⟩
        have h2' : y ∈ f := by
          rw [← Γ₂.closure_diff_V hf₂]; exact ⟨hyf, fun h => hy_notV (Or.inr h)⟩
        exact hfe (Γ₂.edge_eq_of_mem hf₂ he₂ h2' h1')
    have hnone : ¬ (D ∩ B).Nonempty := by
      intro hne
      obtain ⟨y, hy, hyA, hyB⟩ := isPreconnected_closed_iff.mp hD _ _ isClosed_closure hBcl
        hcover ⟨x, hxD, subset_closure hxe⟩ hne
      exact hdisj y hy hyA hyB
    intro y hy
    have hyA : y ∈ closure e := (hcover hy).resolve_right fun hyB => hnone ⟨y, hy, hyB⟩
    have hy_notV := hnotV y hy
    rcases he with he₁ | he₂
    · rw [← Γ₁.closure_diff_V he₁]; exact ⟨hyA, fun h => hy_notV (Or.inl h)⟩
    · rw [← Γ₂.closure_diff_V he₂]; exact ⟨hyA, fun h => hy_notV (Or.inr h)⟩
  rw [hdiff]
  ext C
  constructor
  · rintro ⟨⟨x, hx⟩, hsub, hconn, hmax⟩
    obtain ⟨e, he, hxe⟩ := hsub hx
    have hCe : C ⊆ e := hpre hconn.isConnected.isPreconnected hsub he hx hxe
    have he_path : IsPathConnected e := by
      rcases he with he₁ | he₂
      · exact he₁.2.2.1
      · exact he₂.2.2.1
    have : e = C := hmax e (subset_sUnion_of_mem he) he_path hCe
    exact this ▸ he
  · intro he
    rcases he with he₁ | he₂
    · refine ⟨he₁.1, subset_sUnion_of_mem (Or.inl he₁), he₁.2.2.1,
        fun D hD hconn heD => ?_⟩
      obtain ⟨x, hx⟩ := he₁.1
      exact (hpre hconn.isConnected.isPreconnected hD (Or.inl he₁) (heD hx) hx).antisymm heD
    · refine ⟨he₂.1, subset_sUnion_of_mem (Or.inr he₂), he₂.2.2.1,
        fun D hD hconn heD => ?_⟩
      obtain ⟨x, hx⟩ := he₂.1
      exact (hpre hconn.isConnected.isPreconnected hD (Or.inr he₂) (heD hx) hx).antisymm heD

/-- Union of two drawings `Γ₁` and `Γ₂` on a `T1Space` whose edges only meet each other's vertices
in `Γ₁.V ∩ Γ₂.V` and whose edge closures only meet in `Γ₁.V ∩ Γ₂.V`. -/
def unionDrawing {S : Type w} [TopologicalSpace S]
    (Γ₁ Γ₂ : Drawing S)
    (h1 : ∀ e₁ ∈ Γ₁.E, closure e₁ ∩ Γ₂.V ⊆ Γ₁.V)
    (h2 : ∀ e₂ ∈ Γ₂.E, closure e₂ ∩ Γ₁.V ⊆ Γ₂.V)
    (h3 : ∀ e₁ ∈ Γ₁.E, ∀ e₂ ∈ Γ₂.E, closure e₁ ∩ closure e₂ ⊆ Γ₁.V ∩ Γ₂.V) :
    Drawing S where
  U := Γ₁.U ∪ Γ₂.U
  V := Γ₁.V ∪ Γ₂.V
  V_subset_U := union_subset_union Γ₁.V_subset_U Γ₂.V_subset_U
  isClosed_U := Γ₁.isClosed_U.union Γ₂.isClosed_U
  finite_V := Γ₁.finite_V.union Γ₂.finite_V
  finite_edges := by
    rw [arcComponentsIn_union Γ₁ Γ₂ h1 h2 h3]
    exact Γ₁.finite_edges.union Γ₂.finite_edges
  edge_cond := by
    intro e he
    rw [arcComponentsIn_union Γ₁ Γ₂ h1 h2 h3] at he
    have hcl_inter : closure e ∩ (Γ₁.V ∪ Γ₂.V) = closure e \ e := by
      rcases he with he₁ | he₂
      · rw [← closure_inter_V_eq_diff Γ₁ he₁]
        ext x
        simp only [mem_inter_iff, mem_union]
        exact ⟨fun ⟨hx, h⟩ => ⟨hx, h.elim id fun hV₂ => h1 e he₁ ⟨hx, hV₂⟩⟩,
          fun ⟨hx, h⟩ => ⟨hx, Or.inl h⟩⟩
      · rw [← closure_inter_V_eq_diff Γ₂ he₂]
        ext x
        simp only [mem_inter_iff, mem_union]
        exact ⟨fun ⟨hx, h⟩ => ⟨hx, h.elim (fun hV₁ => h2 e he₂ ⟨hx, hV₁⟩) id⟩,
          fun ⟨hx, h⟩ => ⟨hx, Or.inr h⟩⟩
    rw [hcl_inter]
    rcases he with he₁ | he₂
    · rw [← closure_inter_V_eq_diff Γ₁ he₁]
      exact Γ₁.edge_cond e he₁
    · rw [← closure_inter_V_eq_diff Γ₂ he₂]
      exact Γ₂.edge_cond e he₂

@[simp]
theorem unionDrawing_U {S : Type w} [TopologicalSpace S]
    (Γ₁ Γ₂ : Drawing S)
    (h1 : ∀ e₁ ∈ Γ₁.E, closure e₁ ∩ Γ₂.V ⊆ Γ₁.V)
    (h2 : ∀ e₂ ∈ Γ₂.E, closure e₂ ∩ Γ₁.V ⊆ Γ₂.V)
    (h3 : ∀ e₁ ∈ Γ₁.E, ∀ e₂ ∈ Γ₂.E, closure e₁ ∩ closure e₂ ⊆ Γ₁.V ∩ Γ₂.V) :
    (unionDrawing Γ₁ Γ₂ h1 h2 h3).U = Γ₁.U ∪ Γ₂.U := rfl

@[simp]
theorem unionDrawing_V {S : Type w} [TopologicalSpace S]
    (Γ₁ Γ₂ : Drawing S)
    (h1 : ∀ e₁ ∈ Γ₁.E, closure e₁ ∩ Γ₂.V ⊆ Γ₁.V)
    (h2 : ∀ e₂ ∈ Γ₂.E, closure e₂ ∩ Γ₁.V ⊆ Γ₂.V)
    (h3 : ∀ e₁ ∈ Γ₁.E, ∀ e₂ ∈ Γ₂.E, closure e₁ ∩ closure e₂ ⊆ Γ₁.V ∩ Γ₂.V) :
    (unionDrawing Γ₁ Γ₂ h1 h2 h3).V = Γ₁.V ∪ Γ₂.V := rfl

@[simp]
theorem unionDrawing_E {S : Type w} [TopologicalSpace S]
    (Γ₁ Γ₂ : Drawing S)
    (h1 : ∀ e₁ ∈ Γ₁.E, closure e₁ ∩ Γ₂.V ⊆ Γ₁.V)
    (h2 : ∀ e₂ ∈ Γ₂.E, closure e₂ ∩ Γ₁.V ⊆ Γ₂.V)
    (h3 : ∀ e₁ ∈ Γ₁.E, ∀ e₂ ∈ Γ₂.E, closure e₁ ∩ closure e₂ ⊆ Γ₁.V ∩ Γ₂.V) :
    (unionDrawing Γ₁ Γ₂ h1 h2 h3).E = Γ₁.E ∪ Γ₂.E :=
  arcComponentsIn_union Γ₁ Γ₂ h1 h2 h3

theorem isSubdrawing_left_unionDrawing {S : Type w} [TopologicalSpace S]
    (Γ₁ Γ₂ : Drawing S)
    (h1 : ∀ e₁ ∈ Γ₁.E, closure e₁ ∩ Γ₂.V ⊆ Γ₁.V)
    (h2 : ∀ e₂ ∈ Γ₂.E, closure e₂ ∩ Γ₁.V ⊆ Γ₂.V)
    (h3 : ∀ e₁ ∈ Γ₁.E, ∀ e₂ ∈ Γ₂.E, closure e₁ ∩ closure e₂ ⊆ Γ₁.V ∩ Γ₂.V) :
    Γ₁.IsSubdrawing (unionDrawing Γ₁ Γ₂ h1 h2 h3) :=
  ⟨subset_union_left, by rw [unionDrawing_E]; exact subset_union_left⟩

theorem isSubdrawing_right_unionDrawing {S : Type w} [TopologicalSpace S]
    (Γ₁ Γ₂ : Drawing S)
    (h1 : ∀ e₁ ∈ Γ₁.E, closure e₁ ∩ Γ₂.V ⊆ Γ₁.V)
    (h2 : ∀ e₂ ∈ Γ₂.E, closure e₂ ∩ Γ₁.V ⊆ Γ₂.V)
    (h3 : ∀ e₁ ∈ Γ₁.E, ∀ e₂ ∈ Γ₂.E, closure e₁ ∩ closure e₂ ⊆ Γ₁.V ∩ Γ₂.V) :
    Γ₂.IsSubdrawing (unionDrawing Γ₁ Γ₂ h1 h2 h3) :=
  ⟨subset_union_right, by rw [unionDrawing_E]; exact subset_union_right⟩

/-- If every atom in `Γ₁.A \ Γ₂.A` is contained in `Z`, then every atom in `Γ₂.A \ Γ₁.A` is also
contained in `Z`. -/
theorem atom_subset_of_compl_subset {S : Type w} [TopologicalSpace S]
    {Γ₁ Γ₂ : Drawing S} {Z : Set S}
    (hZ : ∀ a ∈ Γ₁.A, a ∉ Γ₂.A → a ⊆ Z) :
    ∀ a' ∈ Γ₂.A, a' ∉ Γ₁.A → a' ⊆ Z := by
  intro a' ha' hnot σ hσ
  obtain ⟨a, ha, hσa⟩ := exists_atom_of_point Γ₁ σ
  by_cases ha₂ : a ∈ Γ₂.A
  · exact (hnot (atom_eq_of_mem ha' ha₂ hσ hσa ▸ ha)).elim
  · exact hZ a ha ha₂ hσa

/-- Dichotomy for atoms, vertices, and edges of `H` and `H'` relative to `atomZone H d z lam` under
`IsRearrangedWithin`. -/
theorem IsRearrangedWithin.atomZone_dichotomy {S : Type w} [TopologicalSpace S] [T2Space S]
    {G : Graph α β} {H H' : Drawing S} {η : SpanEmbedding H G} {η' : SpanEmbedding H' G}
    {θ_star θ lam : ℕ} {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {z : Set S}
    (hRearr : IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z) :
    let Z := atomZone H d z lam
    (∀ a ∈ H.A, (d z a ≤ lam ∧ a ⊆ Z) ∨ (lam < d z a ∧ Disjoint a Z ∧ a ∈ H'.A)) ∧
    (∀ a' ∈ H'.A, a' ⊆ Z ∨ (Disjoint a' Z ∧ a' ∈ H.A ∧ lam < d z a')) ∧
    (∀ v ∈ H.V, (d z {v} ≤ lam ∧ v ∈ Z) ∨
      (lam < d z {v} ∧ v ∉ Z ∧ v ∈ H'.V ∧ η'.vMap v = η.vMap v)) ∧
    (∀ v' ∈ H'.V, v' ∈ Z ∨ (v' ∉ Z ∧ v' ∈ H.V ∧ lam < d z {v'} ∧ η'.vMap v' = η.vMap v')) ∧
    (∀ e ∈ H.E, (d z e ≤ lam ∧ e ⊆ Z) ∨
      (lam < d z e ∧ Disjoint e Z ∧ e ∈ H'.E ∧ η'.eMap e = η.eMap e)) ∧
    (∀ e' ∈ H'.E, e' ⊆ Z ∨ (Disjoint e' Z ∧ e' ∈ H.E ∧ lam < d z e' ∧ η'.eMap e' = η.eMap e')) := by
  have hS : IsClosedSurface S :=
    ⟨hRearr.isSpan.isSurface.1, hRearr.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hRearr.isSpan.bd_empty x hx⟩
  have : ConnectedSpace S := hRearr.isSpan.isConnected
  obtain ⟨hA₁, hA₂⟩ := atom_subset_or_disjoint_atomZone (d := d) (z := z) (lam
    := lam) hRearr.atom_mem
  refine ⟨hA₁, hA₂, fun v hv => ?_, fun v' hv' => ?_, fun e he => ?_, fun e' he' => ?_⟩
  · rcases hA₁ {v} (Or.inl (Or.inl ⟨v, hv, rfl⟩)) with ⟨hle, hsub⟩ | ⟨hlt, hdisj, _⟩
    · exact Or.inl ⟨hle, hsub rfl⟩
    · obtain ⟨hv', heq⟩ := hRearr.vMap_eq v hv hlt
      exact Or.inr ⟨hlt, fun hvZ => Set.disjoint_left.mp hdisj rfl hvZ, hv', heq⟩
  · rcases hA₂ {v'} (Or.inl (Or.inl ⟨v', hv', rfl⟩)) with hsub | ⟨hdisj, ha, hlt⟩
    · exact Or.inl (hsub rfl)
    · have hvH : v' ∈ H.V := vertex_mem_V_of_mem_A hS hv' ha
      obtain ⟨_, heq⟩ := hRearr.vMap_eq v' hvH hlt
      exact Or.inr ⟨fun hvZ => Set.disjoint_left.mp hdisj rfl hvZ, hvH, hlt, heq⟩
  · rcases hA₁ e (Or.inl (Or.inr he)) with ⟨hle, hsub⟩ | ⟨hlt, hdisj, _⟩
    · exact Or.inl ⟨hle, hsub⟩
    · obtain ⟨he', heq⟩ := hRearr.eMap_eq e he hlt
      exact Or.inr ⟨hlt, hdisj, he', heq⟩
  · rcases hA₂ e' (Or.inl (Or.inr he')) with hsub | ⟨hdisj, ha, hlt⟩
    · exact Or.inl hsub
    · have heH : e' ∈ H.E := edge_mem_E_of_mem_A hS he' ha
      obtain ⟨_, heq⟩ := hRearr.eMap_eq e' heH hlt
      exact Or.inr ⟨hdisj, heH, hlt, heq⟩

/-- Claims (3), (4), (5), (6) of Graph Minors XV, (5.2) (pages 130–131), together with distance
bounds on `closure Z₁` and `closure Z₂`. -/
theorem lemma_5_2_claims_3_to_6
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {G : Graph α β} {H H' H'' : Drawing S}
    {η : SpanEmbedding H G} {η' : SpanEmbedding H' G} {η'' : SpanEmbedding H'' G}
    {θ_star θ lam lam₁ lam₂ μ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' d'' : Set S → Set S → ℕ} {z₁ z₂ z₃ : Set S} {τ : S}
    (hFlat : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (hθ_lt : 4 * lam + 2 < θ)
    (hlam₁ : 4 ≤ lam₁) (hlam₂ : 4 ≤ lam₂)
    (hlam : 6 * lam₁ + 5 * lam₂ + 3 * μ + 4 ≤ lam)
    (hRearr₁ : IsRearrangedWithin G H H' η η' θ_star θ lam₁ T_star T T' d d' z₁)
    (hRearr₂ : IsRearrangedWithin G H' H'' η' η'' θ_star (θ - (4 * lam₁ + 2)) lam₂ T_star T' T'' d'
      d'' z₂)
    (hStep₂ : IsMuSteppedSpan G H'' η'' d'' μ)
    (hτz₂ : τ ∈ z₂) (hz₃ : z₃ ∈ H.A) (hτz₃ : τ ∈ z₃) :
    let Z₁ := atomZone H d z₁ lam₁
    let Z₂ := atomZone H' d' z₂ lam₂
    lam - lam₁ < d z₁ z₃ ∧
    (∀ σ₁ ∈ Z₁, lam - 2 * lam₁ < pointDist H d τ σ₁ ∧
      lam - 6 * lam₁ - 2 < pointDist H' d' τ σ₁) ∧
    (∀ σ₂ ∈ Z₂, pointDist H d τ σ₂ ≤ pointDist H' d' τ σ₂ ∧
      pointDist H' d' τ σ₂ ≤ lam₂) ∧
    (∀ σ₁ ∈ Z₁, ∀ σ₂ ∈ Z₂, lam - 2 * lam₁ - lam₂ < pointDist H d σ₁ σ₂) ∧
    (∀ x₁ ∈ closure Z₁, ∀ x₂ ∈ closure Z₂,
      lam - 2 * lam₁ - lam₂ - 6 < pointDist H d x₁ x₂) ∧
    Disjoint (closure Z₁) (closure Z₂) ∧
    z₂ = z₃ := by
  intro Z₁ Z₂
  have hS : IsClosedSurface S :=
    ⟨hFlat.isSpan.isSurface.1, hFlat.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hFlat.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hFlat.isSpan.isConnected
  have hMetric : HasTangleMetric H θ T d := hRearr₁.isCompression.hasMetric
  have hMetric' : HasTangleMetric H' (θ - (4 * lam₁ + 2)) T' d' := hRearr₁.isCompression.hasMetric'
  have hMetric'' : HasTangleMetric H'' (θ - (4 * lam₁ + 2) - (4 * lam₂ + 2)) T'' d'' :=
    hRearr₂.isCompression.hasMetric'
  obtain ⟨_, hd_refl, hd_le_θ, hd_symm, hd_tri, hd_inc⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
  obtain ⟨_, hd'_refl, hd'_le_θ', hd'_symm, hd'_tri, _⟩ :=
    gm11_theorem_9_1 H' (θ - (4 * lam₁ + 2)) T' d' hS hConn hMetric'
  have hord := hFlat.order_ge
  -- Claim (3): `lam - lam₁ < d z₁ z₃`
  have hClaim3 : lam - lam₁ < d z₁ z₃ := by
    by_contra hle_not
    have hle_z : d z₁ z₃ ≤ lam - lam₁ := Nat.le_of_not_lt hle_not
    let θ₀ := θ - (4 * lam + 2)
    let T₀ := GM10.truncation T'' θ₀
    have h1_θ₀ : 1 ≤ θ₀ := by dsimp [θ₀]; omega
    have hle_θ₀ : θ₀ ≤ θ - (4 * lam₁ + 2) - (4 * lam₂ + 2) := by dsimp [θ₀]; omega
    obtain ⟨d₀, hM₀, hd₀_eq, hpt₀_eq⟩ :=
      hasTangleMetric_truncation_of_hasTangleMetric hMetric'' h1_θ₀ hle_θ₀
    have hRearr₀ : IsRearrangedWithin G H H'' η η'' θ_star θ lam T_star T T₀ d d₀ z₃ := by
      refine ⟨hz₃, hFlat.isSpan, hRearr₂.isSpan'.truncation h1_θ₀ hle_θ₀, ?_, ?_, ?_, ?_⟩
      · intro a ha hlt
        have htri := hd_tri z₃ hz₃ z₁ hRearr₁.z_mem a ha
        have hsym := hd_symm z₃ hz₃ z₁ hRearr₁.z_mem
        have hlt₁ : lam₁ < d z₁ a := by omega
        have ha' : a ∈ H'.A := hRearr₁.atom_mem a ha hlt₁
        obtain ⟨σ, hσa⟩ := atom_nonempty ha
        have hpt_H : pointDist H d τ σ = d z₃ a := pointDist_eq_of_mem_atom hz₃ ha hτz₃ hσa
        have hpt_H' : pointDist H' d' τ σ = d' z₂ a :=
          pointDist_eq_of_mem_atom hRearr₂.z_mem ha' hτz₂ hσa
        have hcomp₁ := hRearr₁.isCompression.dist_le τ σ
        have hlt₂ : lam₂ < d' z₂ a := by omega
        exact hRearr₂.atom_mem a ha' hlt₂
      · intro v hv hlt
        have ha : ({v} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
        have htri := hd_tri z₃ hz₃ z₁ hRearr₁.z_mem {v} ha
        have hsym := hd_symm z₃ hz₃ z₁ hRearr₁.z_mem
        have hlt₁ : lam₁ < d z₁ {v} := by omega
        obtain ⟨hv', hv_eq₁⟩ := hRearr₁.vMap_eq v hv hlt₁
        have ha' : ({v} : Set S) ∈ H'.A := Or.inl (Or.inl ⟨v, hv', rfl⟩)
        have hpt_H : pointDist H d τ v = d z₃ {v} := pointDist_eq_of_mem_atom hz₃ ha hτz₃ rfl
        have hpt_H' : pointDist H' d' τ v = d' z₂ {v} :=
          pointDist_eq_of_mem_atom hRearr₂.z_mem ha' hτz₂ rfl
        have hcomp₁ := hRearr₁.isCompression.dist_le τ v
        have hlt₂ : lam₂ < d' z₂ {v} := by omega
        obtain ⟨hv'', hv_eq₂⟩ := hRearr₂.vMap_eq v hv' hlt₂
        exact ⟨hv'', hv_eq₂.trans hv_eq₁⟩
      · intro e he hlt
        have ha : e ∈ H.A := Or.inl (Or.inr he)
        have htri := hd_tri z₃ hz₃ z₁ hRearr₁.z_mem e ha
        have hsym := hd_symm z₃ hz₃ z₁ hRearr₁.z_mem
        have hlt₁ : lam₁ < d z₁ e := by omega
        obtain ⟨he', he_eq₁⟩ := hRearr₁.eMap_eq e he hlt₁
        have ha' : e ∈ H'.A := Or.inl (Or.inr he')
        obtain ⟨σ, hσe⟩ := he.1
        have hpt_H : pointDist H d τ σ = d z₃ e := pointDist_eq_of_mem_atom hz₃ ha hτz₃ hσe
        have hpt_H' : pointDist H' d' τ σ = d' z₂ e :=
          pointDist_eq_of_mem_atom hRearr₂.z_mem ha' hτz₂ hσe
        have hcomp₁ := hRearr₁.isCompression.dist_le τ σ
        have hlt₂ : lam₂ < d' z₂ e := by omega
        obtain ⟨he'', he_eq₂⟩ := hRearr₂.eMap_eq e he' hlt₂
        exact ⟨he'', he_eq₂.trans he_eq₁⟩
      · refine ⟨by omega, hMetric, hM₀, fun σ₁ σ₂ => ?_⟩
        obtain ⟨a₁, ha₁, hσ₁⟩ := exists_atom_of_point H σ₁
        obtain ⟨a₂, ha₂, hσ₂⟩ := exists_atom_of_point H σ₂
        have hle_θ : pointDist H d σ₁ σ₂ ≤ θ := by
          rw [pointDist_eq_of_mem_atom ha₁ ha₂ hσ₁ hσ₂]
          exact hd_le_θ a₁ ha₁ a₂ ha₂
        have h1 := hRearr₁.isCompression.dist_le σ₁ σ₂
        have h2 := hRearr₂.isCompression.dist_le σ₁ σ₂
        rw [hpt₀_eq σ₁ σ₂]
        omega
    obtain ⟨P, u, v, hu, hv, hP, hdist⟩ := hStep₂
    have hdist₀ : μ ≤ d₀ {u} {v} := by
      rw [hd₀_eq {u} (Or.inl (Or.inl ⟨u, hu, rfl⟩)) {v} (Or.inl (Or.inl ⟨v, hv, rfl⟩))]
      omega
    exact hFlat.no_stepped_rearrangement hRearr₀ ⟨P, u, v, hu, hv, hP, hdist₀⟩
  -- Claim (4): for all `σ₁ ∈ Z₁`, `lam - 2 * lam₁ < pointDist H d τ σ₁` and `lam - 6 * lam₁ - 2 <
  -- pointDist H' d' τ σ₁`
  have hClaim4 : ∀ σ₁ ∈ Z₁, lam - 2 * lam₁ < pointDist H d τ σ₁ ∧
      lam - 6 * lam₁ - 2 < pointDist H' d' τ σ₁ := by
    rintro σ₁ ⟨a₁, ha₁, hle₁, hσ₁⟩
    have hpt : pointDist H d τ σ₁ = d z₃ a₁ := pointDist_eq_of_mem_atom hz₃ ha₁ hτz₃ hσ₁
    have htri := hd_tri z₁ hRearr₁.z_mem a₁ ha₁ z₃ hz₃
    have hsym := hd_symm a₁ ha₁ z₃ hz₃
    have hcomp₁ := hRearr₁.isCompression.dist_le τ σ₁
    exact ⟨by omega, by omega⟩
  -- Claim (5): for all `σ₂ ∈ Z₂`, `pointDist H d τ σ₂ ≤ pointDist H' d' τ σ₂ ≤ lam₂`
  have hClaim5 : ∀ σ₂ ∈ Z₂, pointDist H d τ σ₂ ≤ pointDist H' d' τ σ₂ ∧
      pointDist H' d' τ σ₂ ≤ lam₂ := by
    rintro σ₂ ⟨a₂', ha₂', hle₂, hσ₂⟩
    have hpt' : pointDist H' d' τ σ₂ = d' z₂ a₂' :=
      pointDist_eq_of_mem_atom hRearr₂.z_mem ha₂' hτz₂ hσ₂
    have hle_lam₂ : pointDist H' d' τ σ₂ ≤ lam₂ := by omega
    have hZ₁_sub : ∀ a' ∈ H'.A, a' ∉ H.A → a' ⊆ Z₁ := by
      intro a' ha' hnot
      rcases hRearr₁.atomZone_dichotomy.2.1 a' ha' with hsub | ⟨_, haH, _⟩
      · exact hsub
      · exact (hnot haH).elim
    have hltZ₁ : ∀ σ₁ ∈ Z₁, pointDist H' d' τ σ₂ < pointDist H' d' τ σ₁ := by
      intro σ₁ hσ₁
      have := (hClaim4 σ₁ hσ₁).2
      omega
    have hle_H := theorem_4_2_proof H' H Z₁ (θ - (4 * lam₁ + 2)) θ (4 * lam₁ + 2) T' T d' d τ σ₂
      hS hConn hMetric' hMetric hZ₁_sub (Or.inr hRearr₁.isCompression) hltZ₁ (by omega)
    exact ⟨hle_H, hle_lam₂⟩
  -- Claim (6): for all `σ₁ ∈ Z₁, σ₂ ∈ Z₂`, `lam - 2 * lam₁ - lam₂ < pointDist H d σ₁ σ₂`
  have hClaim6 : ∀ σ₁ ∈ Z₁, ∀ σ₂ ∈ Z₂, lam - 2 * lam₁ - lam₂ < pointDist H d σ₁ σ₂ := by
    intro σ₁ hσ₁ σ₂ hσ₂
    obtain ⟨a₁, ha₁, hle₁, hσ₁_a⟩ := hσ₁
    obtain ⟨a₂, ha₂, hσ₂_a⟩ := exists_atom_of_point H σ₂
    have hpt_12 : pointDist H d σ₁ σ₂ = d a₁ a₂ := pointDist_eq_of_mem_atom ha₁ ha₂ hσ₁_a hσ₂_a
    have hpt_τ2 : pointDist H d τ σ₂ = d z₃ a₂ := pointDist_eq_of_mem_atom hz₃ ha₂ hτz₃ hσ₂_a
    have h5 := hClaim5 σ₂ hσ₂
    have htri₁ := hd_tri z₁ hRearr₁.z_mem a₁ ha₁ a₂ ha₂
    have htri₂ := hd_tri z₁ hRearr₁.z_mem a₂ ha₂ z₃ hz₃
    have hsym₂ := hd_symm z₃ hz₃ a₂ ha₂
    omega
  -- Closure distance bound
  have hClosureDist : ∀ x₁ ∈ closure Z₁, ∀ x₂ ∈ closure Z₂,
      lam - 2 * lam₁ - lam₂ - 6 < pointDist H d x₁ x₂ := by
    intro x₁ hx₁ x₂ hx₂
    obtain ⟨σ₁, hσ₁Z₁, hle_x₁⟩ :=
      (closure_atomZone_props hS hConn hMetric hRearr₁.z_mem x₁ hx₁).1
    have hfin₂ : {a' ∈ H'.A | d' z₂ a' ≤ lam₂}.Finite := (finite_A hS H').subset fun _ h => h.1
    have hEq₂ : Z₂ = ⋃ a' ∈ {a' ∈ H'.A | d' z₂ a' ≤ lam₂}, a' := by
      ext x; simp [Z₂, atomZone, and_assoc]
    have hx₂' : x₂ ∈ ⋃ a' ∈ {a' ∈ H'.A | d' z₂ a' ≤ lam₂}, closure a' := by
      rwa [← hfin₂.closure_biUnion, ← hEq₂]
    obtain ⟨b', ⟨hb', hle_b'⟩, hx₂_b'⟩ := mem_iUnion₂.mp hx₂'
    obtain ⟨σ₂, hσ₂_b'⟩ := atom_nonempty hb'
    have hσ₂Z₂ : σ₂ ∈ Z₂ := ⟨b', hb', hle_b', hσ₂_b'⟩
    obtain ⟨a_x₁, ha_x₁, hx₁_a⟩ := exists_atom_of_point H x₁
    obtain ⟨a_σ₁, ha_σ₁, hσ₁_a⟩ := exists_atom_of_point H σ₁
    obtain ⟨a_x₂, ha_x₂, hx₂_a⟩ := exists_atom_of_point H x₂
    obtain ⟨a_σ₂, ha_σ₂, hσ₂_a⟩ := exists_atom_of_point H σ₂
    -- Since `σ₂ ∈ b' ∈ H'.A` and `σ₂ ∈ Z₂`, `b'` cannot be in `Z₁` (by `hClaim6`), so `b' ∈ H.A`!
    have hb'_H : b' ∈ H.A := by
      rcases hRearr₁.atomZone_dichotomy.2.1 b' hb' with hsub | ⟨_, haH, _⟩
      · exfalso
        have hσ₂Z₁ : σ₂ ∈ Z₁ := hsub hσ₂_b'
        have h6 := hClaim6 σ₂ hσ₂Z₁ σ₂ hσ₂Z₂
        rw [pointDist_eq_of_mem_atom ha_σ₂ ha_σ₂ hσ₂_a hσ₂_a, hd_refl a_σ₂ ha_σ₂] at h6
        omega
      · exact haH
    have hb'_eq : a_σ₂ = b' := atom_eq_of_mem ha_σ₂ hb'_H hσ₂_a hσ₂_b'
    have hinc₂ : d a_x₂ a_σ₂ ≤ 3 :=
      atom_closure_dist_le_three hS hMetric a_x₂ ha_x₂ a_σ₂ ha_σ₂ ⟨x₂, hx₂_a, hb'_eq ▸ hx₂_b'⟩
    have h6 := hClaim6 σ₁ hσ₁Z₁ σ₂ hσ₂Z₂
    rw [pointDist_eq_of_mem_atom ha_σ₁ ha_σ₂ hσ₁_a hσ₂_a] at h6
    rw [pointDist_eq_of_mem_atom ha_σ₁ ha_x₁ hσ₁_a hx₁_a] at hle_x₁
    rw [pointDist_eq_of_mem_atom ha_x₁ ha_x₂ hx₁_a hx₂_a]
    have htri₁ := hd_tri a_σ₁ ha_σ₁ a_x₁ ha_x₁ a_x₂ ha_x₂
    have htri₂ := hd_tri a_σ₁ ha_σ₁ a_x₂ ha_x₂ a_σ₂ ha_σ₂
    omega
  have hDisj : Disjoint (closure Z₁) (closure Z₂) := by
    refine Set.disjoint_left.mpr fun x hx₁ hx₂ => ?_
    obtain ⟨a, ha, hxa⟩ := exists_atom_of_point H x
    have hlt := hClosureDist x hx₁ x hx₂
    rw [pointDist_eq_of_mem_atom ha ha hxa hxa, hd_refl a ha] at hlt
    omega
  have hz₂_eq : z₂ = z₃ := by
    have hz₂_Z₂ : z₂ ⊆ Z₂ := by
      intro x hx
      refine ⟨z₂, hRearr₂.z_mem, ?_, hx⟩
      rw [hd'_refl z₂ hRearr₂.z_mem]
      omega
    rcases hRearr₁.atomZone_dichotomy.2.1 z₂ hRearr₂.z_mem with hsub | ⟨_, haH, _⟩
    · exfalso
      exact Set.disjoint_left.mp hDisj (subset_closure (hsub hτz₂)) (subset_closure (hz₂_Z₂ hτz₂))
    · exact atom_eq_of_mem haH hz₃ hτz₂ hτz₃
  exact ⟨hClaim3, hClaim4, hClaim5, hClaim6, hClosureDist, hDisj, hz₂_eq⟩

/-- Claim (10) of Graph Minors XV, (5.2) (page 132):
With `S₁ = {s ∈ H.V | ∃ σ₁ ∈ Z₁, pointDist H d σ₁ s ≤ μ + 4}` and
`S₂ = {s ∈ H.V | ∃ σ₂ ∈ Z₂, pointDist H d σ₂ s ≤ μ + 4}`, there is no walk in `G` from
`η.vMap '' S₁` to `η.vMap '' S₂` whose vertices in `V(η.imageGraph)` all belong to
`η.vMap '' S₁ ∪ η.vMap '' S₂`. -/
theorem no_walk_between_S₁_S₂
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ lam lam₁ lam₂ μ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {Z₁ Z₂ : Set S}
    (hFlat : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (hMetric : HasTangleMetric H θ T d)
    (hθ_lt : 4 * lam + 2 < θ)
    (hlam₁ : 4 ≤ lam₁) (hlam₂ : 4 ≤ lam₂)
    (hlam : 6 * lam₁ + 5 * lam₂ + 3 * μ + 4 ≤ lam)
    (hClaim6 : ∀ σ₁ ∈ Z₁, ∀ σ₂ ∈ Z₂, lam - 2 * lam₁ - lam₂ < pointDist H d σ₁ σ₂)
    {a b : α} (W : GraphWalk G a b)
    (ha : a ∈ η.vMap '' {s ∈ H.V | ∃ σ₁ ∈ Z₁, pointDist H d σ₁ s ≤ μ + 4})
    (hb : b ∈ η.vMap '' {s ∈ H.V | ∃ σ₂ ∈ Z₂, pointDist H d σ₂ s ≤ μ + 4})
    (hW_V : ∀ w ∈ W.support, w ∈ V(η.imageGraph) →
      w ∈ η.vMap '' {s ∈ H.V | ∃ σ₁ ∈ Z₁, pointDist H d σ₁ s ≤ μ + 4} ∪
        η.vMap '' {s ∈ H.V | ∃ σ₂ ∈ Z₂, pointDist H d σ₂ s ≤ μ + 4}) :
    False := by
  let S₁ : Set S := {s ∈ H.V | ∃ σ₁ ∈ Z₁, pointDist H d σ₁ s ≤ μ + 4}
  let S₂ : Set S := {s ∈ H.V | ∃ σ₂ ∈ Z₂, pointDist H d σ₂ s ≤ μ + 4}
  have hS : IsClosedSurface S :=
    ⟨hFlat.isSpan.isSurface.1, hFlat.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hFlat.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hFlat.isSpan.isConnected
  obtain ⟨_, _, _, hd_symm, hd_tri, _, hd_inc_e⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
  have hdist_S : ∀ s₁ ∈ S₁, ∀ s₂ ∈ S₂, max μ 4 < d {s₁} {s₂} := by
    rintro s₁ ⟨hs₁V, σ₁, hσ₁Z₁, hle₁⟩ s₂ ⟨hs₂V, σ₂, hσ₂Z₂, hle₂⟩
    obtain ⟨a₁, ha₁, hσ₁a₁⟩ := exists_atom_of_point H σ₁
    obtain ⟨a₂, ha₂, hσ₂a₂⟩ := exists_atom_of_point H σ₂
    have hs₁A : ({s₁} : Set S) ∈ H.A := Or.inl (Or.inl ⟨s₁, hs₁V, rfl⟩)
    have hs₂A : ({s₂} : Set S) ∈ H.A := Or.inl (Or.inl ⟨s₂, hs₂V, rfl⟩)
    have h6 := hClaim6 σ₁ hσ₁Z₁ σ₂ hσ₂Z₂
    rw [pointDist_eq_of_mem_atom ha₁ ha₂ hσ₁a₁ hσ₂a₂] at h6
    rw [pointDist_eq_of_mem_atom ha₁ hs₁A hσ₁a₁ rfl] at hle₁
    rw [pointDist_eq_of_mem_atom ha₂ hs₂A hσ₂a₂ rfl] at hle₂
    have htri₁ := hd_tri a₁ ha₁ {s₁} hs₁A a₂ ha₂
    have htri₂ := hd_tri {s₁} hs₁A {s₂} hs₂A a₂ ha₂
    have hsym₂ := hd_symm {s₂} hs₂A a₂ ha₂
    omega
  obtain ⟨W_sim, hW_sim, hW_sub, _⟩ := exists_isSimple_subwalk W
  obtain ⟨y₂, W₁, _, hy₂S₂, rfl, hfirst₂⟩ :=
    exists_first_append_of_mem_set W_sim (X := η.vMap '' S₂) ⟨b, W_sim.end_mem_support, hb⟩
  have hW₁_sim : W₁.IsSimple := (isSimple_of_append hW_sim).1
  have hW₁_rev_sim : W₁.reverse.IsSimple := by
    unfold GraphWalk.IsSimple at hW₁_sim ⊢
    rwa [GraphWalk.support_reverse, List.nodup_reverse]
  obtain ⟨y₁, W₂_rev, _, hy₁S₁, hrev_eq, hfirst₁⟩ :=
    exists_first_append_of_mem_set W₁.reverse (X := η.vMap '' S₁)
      ⟨a, by rw [GraphWalk.support_reverse, List.mem_reverse]; exact W₁.start_mem_support, ha⟩
  have hW₂_rev_sim : W₂_rev.IsSimple := (GM09.isSimple_of_append (hrev_eq ▸ hW₁_rev_sim)).1
  let W₀ : GraphWalk G y₁ y₂ := W₂_rev.reverse
  have hW₀_sim : W₀.IsSimple := by
    unfold GraphWalk.IsSimple at hW₂_rev_sim ⊢
    rwa [GraphWalk.support_reverse, List.nodup_reverse]
  have hW₀_sub_W₁ : ∀ w ∈ W₀.support, w ∈ W₁.support := by
    intro w hw
    have hw_rev : w ∈ W₂_rev.support := by rwa [GraphWalk.support_reverse, List.mem_reverse] at hw
    have hw_W₁rev : w ∈ W₁.reverse.support := by
      rw [hrev_eq, GraphWalk.mem_support_append]
      exact Or.inl hw_rev
    rwa [GraphWalk.support_reverse, List.mem_reverse] at hw_W₁rev
  have hW₀_sub_W : ∀ w ∈ W₀.support, w ∈ W.support := fun w hw =>
    hW_sub w (by rw [GraphWalk.mem_support_append]; exact Or.inl (hW₀_sub_W₁ w hw))
  obtain ⟨s₁, hs₁, hs₁_eq⟩ := hy₁S₁
  obtain ⟨s₂, hs₂, hs₂_eq⟩ := hy₂S₂
  have hgt := hdist_S s₁ hs₁ s₂ hs₂
  have hs₁_ne_s₂ : s₁ ≠ s₂ := by
    rintro rfl
    obtain ⟨_, hd_refl, _⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
    rw [hd_refl {s₁} (Or.inl (Or.inl ⟨s₁, hs₁.1, rfl⟩))] at hgt
    omega
  have hy₁_ne_y₂ : y₁ ≠ y₂ := by
    rw [← hs₁_eq, ← hs₂_eq]
    exact fun h => hs₁_ne_s₂ (η.bijOn_v.injOn hs₁.1 hs₂.1 h)
  let P₀ := walkSubgraph W₀
  have hP₀_path : IsGraphPathWithEnds G P₀ y₁ y₂ := isGraphPathWithEnds_walkSubgraph hW₀_sim
  have hVP₀ : V(P₀) ∩ V(η.imageGraph) = {y₁, y₂} := by
    rw [vertexSet_walkSubgraph]
    ext w
    simp only [mem_inter_iff, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hw₀, hwIm⟩
      rcases hW_V w (hW₀_sub_W w hw₀) hwIm with hwS₁ | hwS₂
      · left
        have hw_rev : w ∈ W₂_rev.support := by
          rwa [GraphWalk.support_reverse, List.mem_reverse] at hw₀
        exact hfirst₁ w hw_rev hwS₁
      · right
        exact hfirst₂ w (hW₀_sub_W₁ w hw₀) hwS₂
    · rintro (rfl | rfl)
      · exact ⟨W₀.start_mem_support, hs₁_eq ▸ η.bijOn_v.mapsTo hs₁.1⟩
      · exact ⟨W₀.end_mem_support, hs₂_eq ▸ η.bijOn_v.mapsTo hs₂.1⟩
  have hEP₀ : Disjoint E(P₀) E(η.imageGraph) := by
    refine Set.disjoint_left.mpr fun e_G heP₀ heIm => ?_
    obtain ⟨u, v, hlinkP₀⟩ := (P₀.edge_mem_iff_exists_isLink e_G).mp heP₀
    have huv_ne : u ≠ v := fun h => hP₀_path.not_isLink_self (h ▸ hlinkP₀)
    have hlinkG : G.IsLink e_G u v := ((walkSubgraph_le W₀).isLink_iff hlinkP₀.edge_mem).mp hlinkP₀
    have hlinkIm : η.imageGraph.IsLink e_G u v := (η.imageGraph_le.isLink_iff heIm).mpr hlinkG
    have hu_mem : u ∈ ({y₁, y₂} : Set α) := hVP₀ ▸ ⟨hlinkP₀.left_mem, hlinkIm.left_mem⟩
    have hv_mem : v ∈ ({y₁, y₂} : Set α) := hVP₀ ▸ ⟨hlinkP₀.right_mem, hlinkIm.right_mem⟩
    obtain ⟨f, hfH, rfl⟩ := η.bijOn_e.surjOn heIm
    have hlink_y : η.imageGraph.IsLink (η.eMap f) (η.vMap s₁) (η.vMap s₂) := by
      rw [hs₁_eq, hs₂_eq]
      rcases hu_mem with rfl | rfl <;> rcases hv_mem with rfl | rfl
      · exact (huv_ne rfl).elim
      · exact hlinkIm
      · exact hlinkIm.symm
      · exact (huv_ne rfl).elim
    have hlinkH : H.toGraph.IsLink f s₁ s₂ :=
      (η.isLink_iff_of_ne hfH hs₁.1 hs₂.1 hs₁_ne_s₂).mp hlink_y
    have hs₁_f : s₁ ∈ closure f := by
      have : s₁ ∈ closure f ∩ H.V := by rw [hlinkH.2.2.2]; exact Or.inl rfl
      exact this.1
    have hs₂_f : s₂ ∈ closure f := by
      have : s₂ ∈ closure f ∩ H.V := by rw [hlinkH.2.2.2]; exact Or.inr rfl
      exact this.1
    have hd1 : d {s₁} f ≤ 2 := hd_inc_e s₁ hs₁.1 f hfH hs₁_f
    have hd2 : d {s₂} f ≤ 2 := hd_inc_e s₂ hs₂.1 f hfH hs₂_f
    have hsym2 : d f {s₂} = d {s₂} f :=
      hd_symm f (Or.inl (Or.inr hfH)) {s₂} (Or.inl (Or.inl ⟨s₂, hs₂.1, rfl⟩))
    have htri := hd_tri {s₁} (Or.inl (Or.inl ⟨s₁, hs₁.1, rfl⟩)) f (Or.inl (Or.inr hfH))
      {s₂} (Or.inl (Or.inl ⟨s₂, hs₂.1, rfl⟩))
    omega
  have hHPath : IsHPathWithEnds G η.imageGraph P₀ (η.vMap s₁) (η.vMap s₂) := by
    rw [hs₁_eq, hs₂_eq]
    exact ⟨η.imageGraph_le, hP₀_path, hy₁_ne_y₂,
      hs₁_eq ▸ η.bijOn_v.mapsTo hs₁.1, hs₂_eq ▸ η.bijOn_v.mapsTo hs₂.1, hVP₀, hEP₀⟩
  exact not_isMuSteppedSpan_of_isFlatSpan hFlat hMetric hθ_lt
    ⟨P₀, s₁, s₂, hs₁.1, hs₂.1, hHPath, by omega⟩

/-- Claim (9) of Graph Minors XV, (5.2) (page 132):
For any rearrangement `H', η', T'` of `H, η, T` within `lam` of `z` (with `2 ≤ lam` and
`2 ≤ θ - (4 * lam + 2)`), from every vertex `y ∈ H'.V ∩ closure (atomZone H d z lam)` there is a
walk `W` in `G` from `η'.vMap y` to `η.vMap s` for some `s ∈ H.V \ atomZone H d z lam` with
`∃ σ ∈ atomZone H d z lam, pointDist H d σ s ≤ 4` such that every vertex of `W` is either `η.vMap s`
or `η'.vMap v` for some `v ∈ H'.V ∩ atomZone H d z lam`. -/
theorem IsRearrangedWithin.exists_walk_to_outside
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {G : Graph α β} {H H' : Drawing S} {η : SpanEmbedding H G} {η' : SpanEmbedding H' G}
    {θ_star θ lam : ℕ} {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {z : Set S}
    (hRearr : IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z)
    (hlam : 2 ≤ lam) (hθ' : 2 ≤ θ - (4 * lam + 2))
    {y : S} (hyV : y ∈ H'.V) (hyZ : y ∈ closure (atomZone H d z lam)) :
    let Z := atomZone H d z lam
    ∃ (s : S) (W : GraphWalk G (η'.vMap y) (η.vMap s)),
      s ∈ H.V ∧ s ∉ Z ∧
      (∃ σ ∈ Z, pointDist H d σ s ≤ 4) ∧
      ∀ w ∈ W.support, w = η.vMap s ∨ ∃ v ∈ H'.V, v ∈ Z ∧ w = η'.vMap v := by
  intro Z
  have hS : IsClosedSurface S :=
    ⟨hRearr.isSpan.isSurface.1, hRearr.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hRearr.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hRearr.isSpan.isConnected
  have hMetric : HasTangleMetric H θ T d := hRearr.isCompression.hasMetric
  obtain ⟨_, _, _, hd_symm, hd_tri, _, hd_inc_e⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
  have h2E : 2 ≤ H.E.ncard := two_le_ncard_edges_of_tangle hS hMetric.1 (by omega)
  obtain ⟨e_far, he_far, hd_far⟩ :=
    gm12_theorem_1_2 H θ T d z hS hConn (by omega) hMetric h2E hRearr.z_mem
  have hv_far_ex : (closure e_far ∩ H.V).Nonempty := by
    rcases H.edge_cond e_far he_far with ⟨x, u, _, hcl, _⟩ | ⟨x, hcl, _⟩
    · rw [hcl]; exact ⟨x, Or.inl rfl⟩
    · rw [hcl]; exact ⟨x, rfl⟩
  obtain ⟨v_out, hv_out_cl, hv_out_H⟩ := hv_far_ex
  have hd_v_out : lam < d z {v_out} := by
    have hinc : d {v_out} e_far ≤ 2 := hd_inc_e v_out hv_out_H e_far he_far hv_out_cl
    have htri := hd_tri z hRearr.z_mem {v_out} (Or.inl (Or.inl ⟨v_out, hv_out_H, rfl⟩))
      e_far (Or.inl (Or.inr he_far))
    omega
  have hv_out_notZ : v_out ∉ Z := fun h =>
    Nat.not_le.mpr hd_v_out ((mem_atomZone_iff_of_mem_atom (Or.inl (Or.inl ⟨v_out, hv_out_H, rfl⟩))
      rfl).mp h)
  have hv_out_H' : v_out ∈ H'.V := (hRearr.vMap_eq v_out hv_out_H hd_v_out).1
  have hE'_ne : H'.E.Nonempty := edges_nonempty_of_tangle hS hRearr.isSpan'.isRespectful hθ'
  obtain ⟨W_raw⟩ := twoCell_toGraph_connected hS hRearr.isSpan'.isRespectful.1 hE'_ne hyV hv_out_H'
  obtain ⟨W₀, hW₀_sim, _, _⟩ := exists_isSimple_subwalk W_raw
  obtain ⟨s, W₁, _, ⟨hs_H', hs_notZ⟩, hW₀_eq, hfirst⟩ :=
    exists_first_append_of_mem_set W₀ (X := {v ∈ H'.V | v ∉ Z})
      ⟨v_out, W₀.end_mem_support, hv_out_H', hv_out_notZ⟩
  have hW₁_sim : W₁.IsSimple := (GM09.isSimple_of_append (hW₀_eq ▸ hW₀_sim)).1
  rcases hRearr.atomZone_dichotomy.2.2.2.1 s hs_H' with hsZ | ⟨_, hs_H, hs_gt, hs_map⟩
  · exact (hs_notZ hsZ).elim
  have hs_dist : ∃ σ ∈ Z, pointDist H d σ s ≤ 4 := by
    by_cases hys : y = s
    · subst hys
      obtain ⟨σ, hσZ, hle3⟩ := (closure_atomZone_props hS hConn hMetric hRearr.z_mem y hyZ).1
      exact ⟨σ, hσZ, by omega⟩
    · have hW₁_rev_sim : W₁.reverse.IsSimple := by
        unfold GraphWalk.IsSimple at hW₁_sim ⊢
        rwa [GraphWalk.support_reverse, List.nodup_reverse]
      generalize hrev : W₁.reverse = R
      cases R with
      | nil _ =>
        exact (hys rfl).elim
      | @cons _ v_prev _ e' hlink r =>
        have hv_prev_W₁ : v_prev ∈ W₁.support := by
          have : v_prev ∈ W₁.reverse.support := by
            rw [hrev, GraphWalk.support_cons]
            exact List.mem_cons_of_mem _ r.start_mem_support
          rwa [GraphWalk.support_reverse, List.mem_reverse] at this
        have hv_prev_ne_s : v_prev ≠ s := by
          intro hEq
          rw [hrev] at hW₁_rev_sim
          exact (List.nodup_cons.mp hW₁_rev_sim).1 (hEq ▸ r.start_mem_support)
        have hv_prev_H' : v_prev ∈ H'.V := hlink.2.2.1
        have hv_prev_Z : v_prev ∈ Z := by
          by_contra hnotZ
          exact hv_prev_ne_s (hfirst v_prev hv_prev_W₁ ⟨hv_prev_H', hnotZ⟩)
        have he'_H' : e' ∈ H'.E := hlink.1
        have hs_cl : s ∈ closure e' := by
          have : s ∈ closure e' ∩ H'.V := by rw [hlink.2.2.2]; exact Or.inl rfl
          exact this.1
        have hv_prev_cl : v_prev ∈ closure e' := by
          have : v_prev ∈ closure e' ∩ H'.V := by rw [hlink.2.2.2]; exact Or.inr rfl
          exact this.1
        rcases hRearr.atomZone_dichotomy.2.2.2.2.2 e' he'_H' with he'Z | ⟨_, he'H, _, _⟩
        · have hs_clZ : s ∈ closure Z := closure_mono he'Z hs_cl
          obtain ⟨σ, hσZ, hle3⟩ := (closure_atomZone_props hS hConn hMetric hRearr.z_mem s hs_clZ).1
          exact ⟨σ, hσZ, by omega⟩
        · have hv_prev_H : v_prev ∈ H.V := by
            have : v_prev ∈ closure e' ∩ H.V := by
              rw [closure_inter_V_eq_diff H he'H, ← closure_inter_V_eq_diff H' he'_H']
              exact ⟨hv_prev_cl, hv_prev_H'⟩
            exact this.2
          refine ⟨v_prev, hv_prev_Z, ?_⟩
          have hd1 : d {v_prev} e' ≤ 2 := hd_inc_e v_prev hv_prev_H e' he'H hv_prev_cl
          have hd2 : d {s} e' ≤ 2 := hd_inc_e s hs_H e' he'H hs_cl
          have hsym2 : d e' {s} = d {s} e' :=
            hd_symm e' (Or.inl (Or.inr he'H)) {s} (Or.inl (Or.inl ⟨s, hs_H, rfl⟩))
          have htri := hd_tri {v_prev} (Or.inl (Or.inl ⟨v_prev, hv_prev_H, rfl⟩))
            e' (Or.inl (Or.inr he'H)) {s} (Or.inl (Or.inl ⟨s, hs_H, rfl⟩))
          have hpd : pointDist H d v_prev s = d {v_prev} {s} :=
            pointDist_eq_of_mem_atom (a₁ := {v_prev}) (a₂ := {s})
              (Or.inl (Or.inl ⟨v_prev, hv_prev_H, rfl⟩))
              (Or.inl (Or.inl ⟨s, hs_H, rfl⟩)) rfl rfl
          omega
  obtain ⟨W_im, hW_im_sim, hW_im_sup, _⟩ := η'.exists_walk_imageGraph W₁ hW₁_sim
  have ⟨W_G, hWG_sup⟩ : ∃ W_G : GraphWalk G (η'.vMap y) (η.vMap s), W_G.support = W_im.support := by
    rw [← hs_map]
    obtain ⟨W_G0, hWG0_sup, _⟩ := GM09.exists_walk_up_of_le η'.imageGraph_le W_im
    exact ⟨W_G0, hWG0_sup⟩
  refine ⟨s, W_G, hs_H, hs_notZ, hs_dist, fun w hw => ?_⟩
  have hw_im : w ∈ W_im.support := hWG_sup ▸ hw
  rw [hW_im_sup, List.mem_map] at hw_im
  obtain ⟨v, hv_W₁, rfl⟩ := hw_im
  have hv_H' : v ∈ H'.V := W₁.mem_vertexSet_of_mem_support hv_W₁
  by_cases hvZ : v ∈ Z
  · exact Or.inr ⟨v, hv_H', hvZ, rfl⟩
  · have hvs : v = s := hfirst v hv_W₁ ⟨hv_H', hvZ⟩
    subst hvs
    exact Or.inl hs_map

/-- From any vertex `a ∈ W.support` of a walk `W : GraphWalk G x y`, there is a walk `W' : GraphWalk
G a y`
whose support is contained in `W.support`. -/
theorem exists_walk_from_of_mem_support {G : Graph α β} {x y a : α}
    (W : GraphWalk G x y) (ha : a ∈ W.support) :
    ∃ W' : GraphWalk G a y, ∀ w ∈ W'.support, w ∈ W.support := by
  induction W with
  | @nil u hu =>
    rw [GraphWalk.support_nil, List.mem_singleton] at ha
    subst ha
    exact ⟨.nil hu, fun w hw => hw⟩
  | @cons u v z e hlink r ih =>
    rw [GraphWalk.support_cons, List.mem_cons] at ha
    rcases ha with rfl | har
    · exact ⟨.cons hlink r, fun w hw => hw⟩
    · obtain ⟨W', hW'⟩ := ih har
      refine ⟨W', fun w hw => ?_⟩
      rw [GraphWalk.support_cons]
      exact List.mem_cons_of_mem u (hW' w hw)

/-- Between any two vertices `a₁, a₂ ∈ W.support` of a walk `W : GraphWalk G x y`, there is a walk
`W' : GraphWalk G a₁ a₂` whose support is contained in `W.support`. -/
theorem exists_walk_between_of_mem_support {G : Graph α β} {x y a₁ a₂ : α}
    (W : GraphWalk G x y) (ha₁ : a₁ ∈ W.support) (ha₂ : a₂ ∈ W.support) :
    ∃ W' : GraphWalk G a₁ a₂, ∀ w ∈ W'.support, w ∈ W.support := by
  obtain ⟨W₁, hW₁⟩ := exists_walk_from_of_mem_support W ha₁
  obtain ⟨W₂, hW₂⟩ := exists_walk_from_of_mem_support W ha₂
  refine ⟨W₁.append W₂.reverse, fun w hw => ?_⟩
  rcases (GraphWalk.mem_support_append _ _).mp hw with hw₁ | hw₂
  · exact hW₁ w hw₁
  · rw [GraphWalk.support_reverse, List.mem_reverse] at hw₂
    exact hW₂ w hw₂

/-- Claim (10) of `(5.2)` (page 132) in full: no walk `W` in `G` from `X₁` to `X₂` has all its
vertices in `V(η(H))` contained in `X₁ ∪ X₂`. -/
theorem no_walk_between_X₁_X₂
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {G : Graph α β} {H H' H'' : Drawing S}
    {η : SpanEmbedding H G} {η' : SpanEmbedding H' G} {η'' : SpanEmbedding H'' G}
    {θ_star θ lam lam₁ lam₂ μ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' d'' : Set S → Set S → ℕ} {z₁ z₂ : Set S}
    (hFlat : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (hθ_lt : 4 * lam + 2 < θ)
    (hlam₁ : 4 ≤ lam₁) (hlam₂ : 4 ≤ lam₂)
    (hlam : 6 * lam₁ + 5 * lam₂ + 3 * μ + 4 ≤ lam)
    (hRearr₁ : IsRearrangedWithin G H H' η η' θ_star θ lam₁ T_star T T' d d' z₁)
    (hRearr₂ : IsRearrangedWithin G H' H'' η' η'' θ_star (θ - (4 * lam₁ + 2)) lam₂ T_star T' T'' d'
      d'' z₂)
    (hStep : IsMuSteppedSpan G H'' η'' d'' μ)
    {a₁ a₂ : α} (W : GraphWalk G a₁ a₂)
    (ha₁ : a₁ ∈ (η.vMap '' {s ∈ H.V | ∃ σ₁ ∈ atomZone H d z₁ lam₁, pointDist H d σ₁ s ≤ μ + 4}) ∪
      (η'.vMap '' (H'.V ∩ atomZone H d z₁ lam₁)))
    (ha₂ : a₂ ∈ (η.vMap '' {s ∈ H.V | ∃ σ₂ ∈ atomZone H' d' z₂ lam₂, pointDist H d σ₂ s ≤ μ + 4}) ∪
      (η''.vMap '' (H''.V ∩ atomZone H' d' z₂ lam₂)))
    (hW_V : ∀ w ∈ W.support, w ∈ V(η.imageGraph) →
      w ∈ ((η.vMap '' {s ∈ H.V | ∃ σ₁ ∈ atomZone H d z₁ lam₁, pointDist H d σ₁ s ≤ μ + 4}) ∪
          (η'.vMap '' (H'.V ∩ atomZone H d z₁ lam₁))) ∪
        ((η.vMap '' {s ∈ H.V | ∃ σ₂ ∈ atomZone H' d' z₂ lam₂, pointDist H d σ₂ s ≤ μ + 4}) ∪
          (η''.vMap '' (H''.V ∩ atomZone H' d' z₂ lam₂)))) :
    False := by
  let Z₁ := atomZone H d z₁ lam₁
  let Z₂ := atomZone H' d' z₂ lam₂
  let S₁ := {s ∈ H.V | ∃ σ₁ ∈ Z₁, pointDist H d σ₁ s ≤ μ + 4}
  let S₂ := {s ∈ H.V | ∃ σ₂ ∈ Z₂, pointDist H d σ₂ s ≤ μ + 4}
  let X₁ := (η.vMap '' S₁) ∪ (η'.vMap '' (H'.V ∩ Z₁))
  let X₂ := (η.vMap '' S₂) ∪ (η''.vMap '' (H''.V ∩ Z₂))
  have hS : IsClosedSurface S :=
    ⟨hFlat.isSpan.isSurface.1, hFlat.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hFlat.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hFlat.isSpan.isConnected
  have hMetric : HasTangleMetric H θ T d := hRearr₁.isCompression.hasMetric
  have hMetric' : HasTangleMetric H' (θ - (4 * lam₁ + 2)) T' d' := hRearr₁.isCompression.hasMetric'
  obtain ⟨_, _, _, hd_symm, hd_tri, _⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
  obtain ⟨_, _, _, hd'_symm, hd'_tri, _⟩ := gm11_theorem_9_1 H' (θ - (4 * lam₁ + 2)) T' d' hS hConn
    hMetric'
  obtain ⟨τ, hτ_z₂⟩ := atom_nonempty hRearr₂.z_mem
  obtain ⟨z₃, hz₃, hτ_z₃⟩ := exists_atom_of_point H τ
  obtain ⟨_, hClaim4, _, hClaim6, _, _, _⟩ :=
    lemma_5_2_claims_3_to_6 hFlat hθ_lt hlam₁ hlam₂ hlam hRearr₁ hRearr₂ hStep hτ_z₂ hz₃ hτ_z₃
  have hX₁_V : ∀ w ∈ X₁, w ∈ V(η.imageGraph) → w ∈ η.vMap '' S₁ := by
    rintro w (hw | ⟨v, ⟨hvH', hvZ₁⟩, rfl⟩) hw_im
    · exact hw
    · obtain ⟨x, hxH, hmap⟩ := η.bijOn_v.surjOn hw_im
      by_cases hxZ₁ : x ∈ Z₁
      · refine ⟨x, ⟨hxH, x, hxZ₁, ?_⟩, hmap⟩
        obtain ⟨_, hd_refl, _⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
        have hxA : ({x} : Set S) ∈ H.A := Or.inl (Or.inl ⟨x, hxH, rfl⟩)
        rw [pointDist_eq_of_mem_atom (a₁ := {x}) (a₂ := {x}) hxA hxA rfl rfl, hd_refl {x} hxA]
        omega
      · rcases hRearr₁.atomZone_dichotomy.2.2.1 x hxH with ⟨_, hxZ₁'⟩ | ⟨_, _, hxH', hx_map⟩
        · exact (hxZ₁ hxZ₁').elim
        · have hxv : x = v := η'.bijOn_v.injOn hxH' hvH' (hx_map.trans hmap)
          exact (hxZ₁ (hxv ▸ hvZ₁)).elim
  have hX₂_V : ∀ w ∈ X₂, w ∈ V(η.imageGraph) → w ∈ η.vMap '' S₁ ∪ η.vMap '' S₂ := by
    rintro w (hw | ⟨v, ⟨hvH'', hvZ₂⟩, rfl⟩) hw_im
    · exact Or.inr hw
    · obtain ⟨x, hxH, hmap⟩ := η.bijOn_v.surjOn hw_im
      obtain ⟨_, hd_refl, _⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
      have hxA : ({x} : Set S) ∈ H.A := Or.inl (Or.inl ⟨x, hxH, rfl⟩)
      have h0 : pointDist H d x x = 0 := by
        rw [pointDist_eq_of_mem_atom (a₁ := {x}) (a₂ := {x}) hxA hxA rfl rfl, hd_refl {x} hxA]
      by_cases hxZ₁ : x ∈ Z₁
      · exact Or.inl ⟨x, ⟨hxH, x, hxZ₁, by omega⟩, hmap⟩
      · by_cases hxZ₂ : x ∈ Z₂
        · exact Or.inr ⟨x, ⟨hxH, x, hxZ₂, by omega⟩, hmap⟩
        · rcases hRearr₁.atomZone_dichotomy.2.2.1 x hxH with ⟨_, hxZ₁'⟩ | ⟨_, _, hxH', hx_map₁⟩
          · exact (hxZ₁ hxZ₁').elim
          · rcases hRearr₂.atomZone_dichotomy.2.2.1 x hxH' with ⟨_, hxZ₂'⟩ | ⟨_, _, hxH'', hx_map₂⟩
            · exact (hxZ₂ hxZ₂').elim
            · have hxv : x = v := η''.bijOn_v.injOn hxH'' hvH'' ((hx_map₂.trans hx_map₁).trans hmap)
              exact (hxZ₂ (hxv ▸ hvZ₂)).elim
  have ⟨s₁, hs₁, W_left, hW_left⟩ :
      ∃ s₁ ∈ S₁, ∃ W_left : GraphWalk G (η.vMap s₁) a₁, ∀ w ∈ W_left.support, w ∈ X₁ := by
    rcases ha₁ with ⟨s₁, hs₁, rfl⟩ | ⟨y₁, ⟨hy₁H', hy₁Z₁⟩, rfl⟩
    · exact ⟨s₁, hs₁, .nil (η.imageGraph_le.1 (η.bijOn_v.mapsTo hs₁.1)), fun w hw => by
        rw [GraphWalk.support_nil, List.mem_singleton] at hw
        subst hw; exact Or.inl ⟨s₁, hs₁, rfl⟩⟩
    · obtain ⟨s₁, W₀, hs₁H, _, ⟨σ₁, hσ₁Z₁, hle4⟩, hW₀_sup⟩ :=
        hRearr₁.exists_walk_to_outside (by omega) (by omega) hy₁H' (subset_closure hy₁Z₁)
      have hs₁S₁ : s₁ ∈ S₁ := ⟨hs₁H, σ₁, hσ₁Z₁, by omega⟩
      refine ⟨s₁, hs₁S₁, W₀.reverse, fun w hw => ?_⟩
      rw [GraphWalk.support_reverse, List.mem_reverse] at hw
      rcases hW₀_sup w hw with rfl | ⟨v, hvH', hvZ₁, rfl⟩
      · exact Or.inl ⟨s₁, hs₁S₁, rfl⟩
      · exact Or.inr ⟨v, ⟨hvH', hvZ₁⟩, rfl⟩
  have ⟨s₂, hs₂, W_right, hW_right⟩ :
      ∃ s₂ ∈ S₂, ∃ W_right : GraphWalk G a₂ (η.vMap s₂), ∀ w ∈ W_right.support, w ∈ X₂ := by
    rcases ha₂ with ⟨s₂, hs₂, rfl⟩ | ⟨y₂, ⟨hy₂H'', hy₂Z₂⟩, rfl⟩
    · exact ⟨s₂, hs₂, .nil (η.imageGraph_le.1 (η.bijOn_v.mapsTo hs₂.1)), fun w hw => by
        rw [GraphWalk.support_nil, List.mem_singleton] at hw
        subst hw; exact Or.inl ⟨s₂, hs₂, rfl⟩⟩
    · obtain ⟨s₂, W₀, hs₂H', _, ⟨σ₂, hσ₂Z₂, hle4⟩, hW₀_sup⟩ :=
        hRearr₂.exists_walk_to_outside (by omega) (by omega) hy₂H'' (subset_closure hy₂Z₂)
      have hlt_Z₁ : ∀ σ₁ ∈ Z₁, pointDist H' d' σ₂ s₂ < pointDist H' d' σ₂ σ₁ := by
        intro σ₁ hσ₁Z₁
        have h4 := (hClaim4 σ₁ hσ₁Z₁).2
        obtain ⟨a_σ₁, ha_σ₁, hσ₁_a⟩ := exists_atom_of_point H' σ₁
        obtain ⟨a_σ₂, ha_σ₂, hσ₂_a⟩ := exists_atom_of_point H' σ₂
        have hd'_σ₂ : d' z₂ a_σ₂ ≤ lam₂ := (mem_atomZone_iff_of_mem_atom ha_σ₂ hσ₂_a).mp hσ₂Z₂
        rw [pointDist_eq_of_mem_atom hRearr₂.z_mem ha_σ₁ hτ_z₂ hσ₁_a] at h4
        rw [pointDist_eq_of_mem_atom ha_σ₂ ha_σ₁ hσ₂_a hσ₁_a]
        have hsym := hd'_symm z₂ hRearr₂.z_mem a_σ₁ ha_σ₁
        have htri := hd'_tri a_σ₁ ha_σ₁ a_σ₂ ha_σ₂ z₂ hRearr₂.z_mem
        have hsym2 := hd'_symm a_σ₂ ha_σ₂ z₂ hRearr₂.z_mem
        have hsym3 := hd'_symm a_σ₁ ha_σ₁ a_σ₂ ha_σ₂
        omega
      have hs₂_notZ₁ : s₂ ∉ Z₁ := by
        intro hs₂Z₁
        have hlt := hlt_Z₁ s₂ hs₂Z₁
        omega
      rcases hRearr₁.atomZone_dichotomy.2.2.2.1 s₂ hs₂H' with hs₂Z₁ | ⟨_, hs₂H, _, hs₂_map⟩
      · exact (hs₂_notZ₁ hs₂Z₁).elim
      have hZ₁_sub : ∀ a' ∈ H'.A, a' ∉ H.A → a' ⊆ Z₁ := by
        intro a' ha' hnot
        rcases hRearr₁.atomZone_dichotomy.2.1 a' ha' with hsub | ⟨_, haH, _⟩
        · exact hsub
        · exact (hnot haH).elim
      have hd_le_d' : pointDist H d σ₂ s₂ ≤ pointDist H' d' σ₂ s₂ :=
        theorem_4_2_proof H' H Z₁ (θ - (4 * lam₁ + 2)) θ (4 * lam₁ + 2) T' T d' d σ₂ s₂
          hS hConn hMetric' hMetric hZ₁_sub (Or.inr hRearr₁.isCompression) hlt_Z₁ (by omega)
      have hs₂S₂ : s₂ ∈ S₂ := ⟨hs₂H, σ₂, hσ₂Z₂, by omega⟩
      have ⟨W₁, hW₁_sup⟩ : ∃ W₁ : GraphWalk G (η''.vMap y₂) (η.vMap s₂), W₁.support = W₀.support
        := by
        rw [← hs₂_map]
        exact ⟨W₀, rfl⟩
      refine ⟨s₂, hs₂S₂, W₁, fun w hw => ?_⟩
      rw [hW₁_sup] at hw
      rcases hW₀_sup w hw with rfl | ⟨v, hvH'', hvZ₂, rfl⟩
      · rw [hs₂_map]
        exact Or.inl ⟨s₂, hs₂S₂, rfl⟩
      · exact Or.inr ⟨v, ⟨hvH'', hvZ₂⟩, rfl⟩
  let W_full := W_left.append (W.append W_right)
  refine no_walk_between_S₁_S₂ hFlat hMetric hθ_lt hlam₁ hlam₂ hlam hClaim6 W_full
    ⟨s₁, hs₁, rfl⟩ ⟨s₂, hs₂, rfl⟩ (fun w hw hw_im => ?_)
  rcases (GraphWalk.mem_support_append _ _).mp hw with hw_l | hw_r
  · exact Or.inl (hX₁_V w (hW_left w hw_l) hw_im)
  · rcases (GraphWalk.mem_support_append _ _).mp hw_r with hw_m | hw_r2
    · rcases hW_V w hw_m hw_im with hwX₁ | hwX₂
      · exact Or.inl (hX₁_V w hwX₁ hw_im)
      · exact hX₂_V w hwX₂ hw_im
    · exact hX₂_V w (hW_right w hw_r2) hw_im

/-- A point `x` lies in `Γ.U` if and only if `x ∈ Γ.V` or `x ∈ e` for some `e ∈ Γ.E`. -/
theorem mem_U_iff_mem_V_or_mem_E {S : Type w} [TopologicalSpace S]
    (Γ : Drawing S) (x : S) :
    x ∈ Γ.U ↔ x ∈ Γ.V ∨ ∃ e ∈ Γ.E, x ∈ e := by
  rw [Γ.U_eq, mem_union, mem_iUnion₂]
  constructor
  · rintro (hxV | ⟨e, he, hxcl⟩)
    · exact Or.inl hxV
    · by_cases hxe : x ∈ e
      · exact Or.inr ⟨e, he, hxe⟩
      · have hxV : x ∈ closure e ∩ Γ.V := by
          rw [closure_inter_V_eq_diff Γ he]
          exact ⟨hxcl, hxe⟩
        exact Or.inl hxV.2
  · rintro (hxV | ⟨e, he, hxe⟩)
    · exact Or.inl hxV
    · exact Or.inr ⟨e, he, subset_closure hxe⟩

/-- For every atom `a ∈ Γ.A` of a drawing `Γ`, `closure a \ a ⊆ Γ.U`. -/
theorem closure_atom_diff_subset_U {S : Type w} [TopologicalSpace S] [T1Space S]
    [LocallyConnectedSpace S] (Γ : Drawing S) {a : Set S} (ha : a ∈ Γ.A) :
    closure a \ a ⊆ Γ.U := by
  rcases ha with (⟨v, _, rfl⟩ | he) | hr
  · rw [closure_singleton, Set.sdiff_self]
    exact empty_subset _
  · rw [← closure_inter_V_eq_diff Γ he]
    exact inter_subset_right.trans Γ.V_subset_U
  · intro x ⟨hx_cl, hx_not⟩
    exact (closure_region_subset hr hx_cl).resolve_left hx_not

/-- If a region `r ∈ Γ₁.R` is disjoint from `Γ₂.U` and satisfies `closure r \ r ⊆ Γ₂.U`, then
`r ∈ Γ₂.R`. -/
theorem region_mem_of_disjoint_U {S : Type w} [TopologicalSpace S] [LocallyConnectedSpace S]
    {Γ₁ Γ₂ : Drawing S} {r : Set S} (hr : r ∈ Γ₁.R)
    (hdisj : Disjoint r Γ₂.U) (hbd : closure r \ r ⊆ Γ₂.U) :
    r ∈ Γ₂.R := by
  obtain ⟨x, hxr⟩ := region_nonempty hr
  have hxU₂ : x ∉ Γ₂.U := Set.disjoint_left.mp hdisj hxr
  obtain ⟨r', hr', hxr'⟩ := exists_region_of_notMem (Γ := Γ₂) hxU₂
  have hsub₁ : r ⊆ r' := subset_region hr' (region_isPreconnected hr) hdisj hxr hxr'
  have hsub₂ : r' ⊆ r := by
    intro y hy
    by_contra hyr
    have hy_not_cl : y ∈ (closure r)ᶜ := fun hycl => region_subset hr' hy (hbd ⟨hycl, hyr⟩)
    obtain ⟨z, _, hzr, hz_compl⟩ :=
      region_isPreconnected hr' r (closure r)ᶜ (region_isOpen hr) isClosed_closure.isOpen_compl
        (fun w hw => by_cases Or.inl fun hwr =>
          Or.inr fun hwcl => region_subset hr' hw (hbd ⟨hwcl, hwr⟩))
        ⟨x, hxr', hxr⟩ ⟨y, hy, hy_not_cl⟩
    exact hz_compl (subset_closure hzr)
  exact Subset.antisymm hsub₁ hsub₂ ▸ hr'

private theorem outer_vertices_follow_second_rearrangement
    {α : Type u}
    {β : Type v}
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {G : Graph α β}
    {H : Drawing S}
    {H' : Drawing S}
    {H'' : Drawing S}
    {η : SpanEmbedding H G}
    {η' : SpanEmbedding H' G}
    {η'' : SpanEmbedding H'' G}
    {θ_star : ℕ}
    {θ : ℕ}
    {lam₁ : ℕ}
    {lam₂ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {d' : Set S → Set S → ℕ}
    {d'' : Set S → Set S → ℕ}
    {z₁ : Set S}
    {z₂ : Set S}
    (hRearr₁ : IsRearrangedWithin G H H' η η' θ_star θ lam₁ T_star T T' d d' z₁)
    (hRearr₂ : IsRearrangedWithin G H' H'' η' η'' θ_star (θ - (4 * lam₁ + 2)) lam₂ T_star T' T''
      d' d'' z₂)
    (Z₁ : Set S)
    (hZoneEqZ₁ : Z₁ = atomZone H d z₁ lam₁)
    (Z₂ : Set S)
    (hZoneEqZ₂ : Z₂ = atomZone H' d' z₂ lam₂)
    (H''' : Drawing S)
    (hH'''_V : ∀ (v : S), v ∈ H'''.V ↔ v ∈ H.V ∧ v ∉ Z₂ ∨ v ∈ H''.V ∧ v ∈ Z₂)
    (vMap''' : S → α)
    (hvMap'''_Z₂ : ∀ v ∈ Z₂, vMap''' v = η''.vMap v)
    (hvMap'''_notZ₂ : ∀ v ∉ Z₂, vMap''' v = η.vMap v) :
    ∀ v ∉ Z₁, (v ∈ H'''.V ↔ v ∈ H''.V) ∧ (v ∈ H'''.V → vMap''' v = η''.vMap v) := by
  subst Z₂
  let Z₂ := atomZone H' d' z₂ lam₂
  subst Z₁
  let Z₁ := atomZone H d z₁ lam₁
  intro v hv_notZ₁
  by_cases hvZ₂ : v ∈ Z₂
  · rw [hH'''_V, hvMap'''_Z₂ v hvZ₂]
    exact ⟨⟨fun h => (h.resolve_left fun h1 => h1.2 hvZ₂).1, fun h => Or.inr ⟨h, hvZ₂⟩⟩,
      fun _ => rfl⟩
  · rw [hH'''_V, hvMap'''_notZ₂ v hvZ₂]
    have hH_iff_H' : (v ∈ H.V ↔ v ∈ H'.V) ∧ (v ∈ H.V → η.vMap v = η'.vMap v) := by
      constructor
      · refine ⟨fun hvH => ?_, fun hvH' => ?_⟩
        · rcases hRearr₁.atomZone_dichotomy.2.2.1 v hvH with ⟨_, hZ₁⟩ | ⟨_, _, hvH', _⟩
          · exact (hv_notZ₁ hZ₁).elim
          · exact hvH'
        · rcases hRearr₁.atomZone_dichotomy.2.2.2.1 v hvH' with hZ₁ | ⟨_, hvH, _⟩
          · exact (hv_notZ₁ hZ₁).elim
          · exact hvH
      · intro hvH
        rcases hRearr₁.atomZone_dichotomy.2.2.1 v hvH with ⟨_, hZ₁⟩ | ⟨_, _, _, hmap⟩
        · exact (hv_notZ₁ hZ₁).elim
        · exact hmap.symm
    have hH'_iff_H'' : (v ∈ H'.V ↔ v ∈ H''.V) ∧ (v ∈ H'.V → η'.vMap v = η''.vMap v) := by
      constructor
      · refine ⟨fun hvH' => ?_, fun hvH'' => ?_⟩
        · rcases hRearr₂.atomZone_dichotomy.2.2.1 v hvH' with ⟨_, hZ₂⟩ | ⟨_, _, hvH'', _⟩
          · exact (hvZ₂ hZ₂).elim
          · exact hvH''
        · rcases hRearr₂.atomZone_dichotomy.2.2.2.1 v hvH'' with hZ₂ | ⟨_, hvH', _⟩
          · exact (hvZ₂ hZ₂).elim
          · exact hvH'
      · intro hvH'
        rcases hRearr₂.atomZone_dichotomy.2.2.1 v hvH' with ⟨_, hZ₂⟩ | ⟨_, _, _, hmap⟩
        · exact (hvZ₂ hZ₂).elim
        · exact hmap.symm
    refine ⟨?_, fun hv''' => ?_⟩
    · rw [hH_iff_H'.1, hH'_iff_H''.1]
      exact ⟨fun h => h.elim And.left And.left, fun h => Or.inl ⟨h, hvZ₂⟩⟩
    · have hvH : v ∈ H.V := (hv'''.resolve_right fun h => hvZ₂ h.2).1
      exact (hH_iff_H'.2 hvH).trans (hH'_iff_H''.2 (hH_iff_H'.1.mp hvH))

private theorem outer_edges_follow_second_rearrangement
    {α : Type u}
    {β : Type v}
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {G : Graph α β}
    {H : Drawing S}
    {H' : Drawing S}
    {H'' : Drawing S}
    {η : SpanEmbedding H G}
    {η' : SpanEmbedding H' G}
    {η'' : SpanEmbedding H'' G}
    {θ_star : ℕ}
    {θ : ℕ}
    {lam₁ : ℕ}
    {lam₂ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {d' : Set S → Set S → ℕ}
    {d'' : Set S → Set S → ℕ}
    {z₁ : Set S}
    {z₂ : Set S}
    (hRearr₁ : IsRearrangedWithin G H H' η η' θ_star θ lam₁ T_star T T' d d' z₁)
    (hRearr₂ : IsRearrangedWithin G H' H'' η' η'' θ_star (θ - (4 * lam₁ + 2)) lam₂ T_star T' T''
      d' d'' z₂)
    (Z₁ : Set S)
    (hZoneEqZ₁ : Z₁ = atomZone H d z₁ lam₁)
    (Z₂ : Set S)
    (hZoneEqZ₂ : Z₂ = atomZone H' d' z₂ lam₂)
    (H''' : Drawing S)
    (hH'''_E : ∀ (e : Set S), e ∈ H'''.E ↔ e ∈ H.E ∧ ¬e ⊆ Z₂ ∨ e ∈ H''.E ∧ e ⊆ Z₂)
    (eMap''' : Set S → β)
    (heMap'''_Z₂ : ∀ e ⊆ Z₂, eMap''' e = η''.eMap e)
    (heMap'''_notZ₂ : ∀ (e : Set S), ¬e ⊆ Z₂ → eMap''' e = η.eMap e) :
    ∀ (e : Set S), ¬e ⊆ Z₁ → (e ∈ H'''.E ↔ e ∈ H''.E) ∧ (e ∈ H'''.E → eMap''' e = η''.eMap e) := by
  subst Z₂
  let Z₂ := atomZone H' d' z₂ lam₂
  subst Z₁
  let Z₁ := atomZone H d z₁ lam₁
  intro e he_notZ₁
  by_cases heZ₂ : e ⊆ Z₂
  · rw [hH'''_E, heMap'''_Z₂ e heZ₂]
    exact ⟨⟨fun h => (h.resolve_left fun h1 => h1.2 heZ₂).1, fun h => Or.inr ⟨h, heZ₂⟩⟩,
      fun _ => rfl⟩
  · rw [hH'''_E, heMap'''_notZ₂ e heZ₂]
    have hH_iff_H' : (e ∈ H.E ↔ e ∈ H'.E) ∧ (e ∈ H.E → η.eMap e = η'.eMap e) := by
      constructor
      · refine ⟨fun heH => ?_, fun heH' => ?_⟩
        · rcases hRearr₁.atomZone_dichotomy.2.2.2.2.1 e heH with ⟨_, hZ₁⟩ | ⟨_, _, heH', _⟩
          · exact (he_notZ₁ hZ₁).elim
          · exact heH'
        · rcases hRearr₁.atomZone_dichotomy.2.2.2.2.2 e heH' with hZ₁ | ⟨_, heH, _⟩
          · exact (he_notZ₁ hZ₁).elim
          · exact heH
      · intro heH
        rcases hRearr₁.atomZone_dichotomy.2.2.2.2.1 e heH with ⟨_, hZ₁⟩ | ⟨_, _, _, hmap⟩
        · exact (he_notZ₁ hZ₁).elim
        · exact hmap.symm
    have hH'_iff_H'' : (e ∈ H'.E ↔ e ∈ H''.E) ∧ (e ∈ H'.E → η'.eMap e = η''.eMap e) := by
      constructor
      · refine ⟨fun heH' => ?_, fun heH'' => ?_⟩
        · rcases hRearr₂.atomZone_dichotomy.2.2.2.2.1 e heH' with ⟨_, hZ₂⟩ | ⟨_, _, heH'', _⟩
          · exact (heZ₂ hZ₂).elim
          · exact heH''
        · rcases hRearr₂.atomZone_dichotomy.2.2.2.2.2 e heH'' with hZ₂ | ⟨_, heH', _⟩
          · exact (heZ₂ hZ₂).elim
          · exact heH'
      · intro heH'
        rcases hRearr₂.atomZone_dichotomy.2.2.2.2.1 e heH' with ⟨_, hZ₂⟩ | ⟨_, _, _, hmap⟩
        · exact (heZ₂ hZ₂).elim
        · exact hmap.symm
    refine ⟨?_, fun he''' => ?_⟩
    · rw [hH_iff_H'.1, hH'_iff_H''.1]
      exact ⟨fun h => h.elim And.left And.left, fun h => Or.inl ⟨h, heZ₂⟩⟩
    · have heH : e ∈ H.E := (he'''.resolve_right fun h => heZ₂ h.2).1
      exact (hH_iff_H'.2 heH).trans (hH'_iff_H''.2 (hH_iff_H'.1.mp heH))

private theorem combined_drawing_vertex_map_is_injective
    {α : Type u}
    {β : Type v}
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {G : Graph α β}
    {H : Drawing S}
    {H' : Drawing S}
    {H'' : Drawing S}
    {η : SpanEmbedding H G}
    {η' : SpanEmbedding H' G}
    {η'' : SpanEmbedding H'' G}
    {θ_star : ℕ}
    {θ : ℕ}
    {lam : ℕ}
    {lam₁ : ℕ}
    {lam₂ : ℕ}
    {μ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {d' : Set S → Set S → ℕ}
    {d'' : Set S → Set S → ℕ}
    {z₁ : Set S}
    {z₂ : Set S}
    (hFlat : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (hθ_lt : 4 * lam + 2 < θ)
    (hlam₁ : 4 ≤ lam₁)
    (hlam₂ : 4 ≤ lam₂)
    (hlam : 6 * lam₁ + 5 * lam₂ + 3 * μ + 4 ≤ lam)
    (hRearr₁ : IsRearrangedWithin G H H' η η' θ_star θ lam₁ T_star T T' d d' z₁)
    (hRearr₂ : IsRearrangedWithin G H' H'' η' η'' θ_star (θ - (4 * lam₁ + 2)) lam₂ T_star T' T''
      d' d'' z₂)
    (hStep : IsMuSteppedSpan G H'' η'' d'' μ)
    (Z₁ : Set S)
    (hZoneEqZ₁ : Z₁ = atomZone H d z₁ lam₁)
    (Z₂ : Set S)
    (hZoneEqZ₂ : Z₂ = atomZone H' d' z₂ lam₂)
    (hd_refl : ∀ a ∈ H.A, d a a = 0)
    (_z₃ : Set S)
    (H''' : Drawing S)
    (hH'''_V : ∀ (v : S), v ∈ H'''.V ↔ v ∈ H.V ∧ v ∉ Z₂ ∨ v ∈ H''.V ∧ v ∈ Z₂)
    (vMap''' : S → α)
    (hvMap'''_Z₂ : ∀ v ∈ Z₂, vMap''' v = η''.vMap v)
    (hvMap'''_notZ₂ : ∀ v ∉ Z₂, vMap''' v = η.vMap v)
    (hV_notZ₁ : ∀ v ∉ Z₁, (v ∈ H'''.V ↔ v ∈ H''.V) ∧ (v ∈ H'''.V → vMap''' v = η''.vMap v)) :
    InjOn vMap''' H'''.V := by
  subst Z₂
  let Z₂ := atomZone H' d' z₂ lam₂
  subst Z₁
  let Z₁ := atomZone H d z₁ lam₁
  intro v₁ hv₁ v₂ hv₂ hEq
  rcases (hH'''_V v₁).mp hv₁ with ⟨hv₁H, hv₁_notZ₂⟩ | ⟨hv₁H'', hv₁Z₂⟩ <;>
    rcases (hH'''_V v₂).mp hv₂ with ⟨hv₂H, hv₂_notZ₂⟩ | ⟨hv₂H'', hv₂Z₂⟩
  · rw [hvMap'''_notZ₂ v₁ hv₁_notZ₂, hvMap'''_notZ₂ v₂ hv₂_notZ₂] at hEq
    exact η.bijOn_v.injOn hv₁H hv₂H hEq
  · by_cases hv₁Z₁ : v₁ ∈ Z₁
    · exfalso
      rw [hvMap'''_notZ₂ v₁ hv₁_notZ₂, hvMap'''_Z₂ v₂ hv₂Z₂] at hEq
      have hv₁_A : ({v₁} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v₁, hv₁H, rfl⟩)
      have h0 : pointDist H d v₁ v₁ = 0 := by
        rw [pointDist_eq_of_mem_atom (a₁ := {v₁}) (a₂ := {v₁}) hv₁_A hv₁_A rfl rfl,
          hd_refl {v₁} hv₁_A]
      have ha₁ : η.vMap v₁ ∈ (η.vMap '' {s ∈ H.V | ∃ σ₁ ∈ Z₁, pointDist H d σ₁ s ≤ μ + 4}) ∪
          (η'.vMap '' (H'.V ∩ Z₁)) :=
        Or.inl ⟨v₁, ⟨hv₁H, v₁, hv₁Z₁, by omega⟩, rfl⟩
      have ha₂ : η.vMap v₁ ∈ (η.vMap '' {s ∈ H.V | ∃ σ₂ ∈ Z₂, pointDist H d σ₂ s ≤ μ + 4}) ∪
          (η''.vMap '' (H''.V ∩ Z₂)) := by
        rw [hEq]
        exact Or.inr ⟨v₂, ⟨hv₂H'', hv₂Z₂⟩, rfl⟩
      exact no_walk_between_X₁_X₂ hFlat hθ_lt hlam₁ hlam₂ hlam hRearr₁ hRearr₂ hStep
        (.nil (η.imageGraph_le.1 (η.bijOn_v.mapsTo hv₁H))) ha₁ ha₂
        (fun w hw _ => by
          rw [GraphWalk.support_nil, List.mem_singleton] at hw
          subst hw; exact Or.inl ha₁)
    · have hv₁H'' : v₁ ∈ H''.V := (hV_notZ₁ v₁ hv₁Z₁).1.mp hv₁
      have hmap₁ : vMap''' v₁ = η''.vMap v₁ := (hV_notZ₁ v₁ hv₁Z₁).2 hv₁
      rw [hmap₁, hvMap'''_Z₂ v₂ hv₂Z₂] at hEq
      exact η''.bijOn_v.injOn hv₁H'' hv₂H'' hEq
  · by_cases hv₂Z₁ : v₂ ∈ Z₁
    · exfalso
      rw [hvMap'''_Z₂ v₁ hv₁Z₂, hvMap'''_notZ₂ v₂ hv₂_notZ₂] at hEq
      have hv₂_A : ({v₂} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v₂, hv₂H, rfl⟩)
      have h0 : pointDist H d v₂ v₂ = 0 := by
        rw [pointDist_eq_of_mem_atom (a₁ := {v₂}) (a₂ := {v₂}) hv₂_A hv₂_A rfl rfl,
          hd_refl {v₂} hv₂_A]
      have ha₁ : η.vMap v₂ ∈ (η.vMap '' {s ∈ H.V | ∃ σ₁ ∈ Z₁, pointDist H d σ₁ s ≤ μ + 4}) ∪
          (η'.vMap '' (H'.V ∩ Z₁)) :=
        Or.inl ⟨v₂, ⟨hv₂H, v₂, hv₂Z₁, by omega⟩, rfl⟩
      have ha₂ : η.vMap v₂ ∈ (η.vMap '' {s ∈ H.V | ∃ σ₂ ∈ Z₂, pointDist H d σ₂ s ≤ μ + 4}) ∪
          (η''.vMap '' (H''.V ∩ Z₂)) := by
        rw [← hEq]
        exact Or.inr ⟨v₁, ⟨hv₁H'', hv₁Z₂⟩, rfl⟩
      exact no_walk_between_X₁_X₂ hFlat hθ_lt hlam₁ hlam₂ hlam hRearr₁ hRearr₂ hStep
        (.nil (η.imageGraph_le.1 (η.bijOn_v.mapsTo hv₂H))) ha₁ ha₂
        (fun w hw _ => by
          rw [GraphWalk.support_nil, List.mem_singleton] at hw
          subst hw; exact Or.inl ha₁)
    · have hv₂H'' : v₂ ∈ H''.V := (hV_notZ₁ v₂ hv₂Z₁).1.mp hv₂
      have hmap₂ : vMap''' v₂ = η''.vMap v₂ := (hV_notZ₁ v₂ hv₂Z₁).2 hv₂
      rw [hvMap'''_Z₂ v₁ hv₁Z₂, hmap₂] at hEq
      exact η''.bijOn_v.injOn hv₁H'' hv₂H'' hEq
  · rw [hvMap'''_Z₂ v₁ hv₁Z₂, hvMap'''_Z₂ v₂ hv₂Z₂] at hEq
    exact η''.bijOn_v.injOn hv₁H'' hv₂H'' hEq

private theorem combined_drawing_incidence_matches_graph
    {α : Type u}
    {β : Type v}
    {S : Type w}
    [TopologicalSpace S]
    {G : Graph α β}
    {H : Drawing S}
    {H'' : Drawing S}
    {η : SpanEmbedding H G}
    {η'' : SpanEmbedding H'' G}
    (Z₁ : Set S)
    (Z₂ : Set S)
    (H''' : Drawing S)
    (hH'''_V : ∀ (v : S), v ∈ H'''.V ↔ v ∈ H.V ∧ v ∉ Z₂ ∨ v ∈ H''.V ∧ v ∈ Z₂)
    (vMap''' : S → α)
    (hvMap'''_notZ₂ : ∀ v ∉ Z₂, vMap''' v = η.vMap v)
    (eMap''' : Set S → β)
    (heMap'''_notZ₂ : ∀ (e : Set S), ¬e ⊆ Z₂ → eMap''' e = η.eMap e)
    (hV_notZ₁ : ∀ v ∉ Z₁, (v ∈ H'''.V ↔ v ∈ H''.V) ∧ (v ∈ H'''.V → vMap''' v = η''.vMap v))
    (hinj_v : InjOn vMap''' H'''.V)
    (hE'''_cases : ∀ e ∈ H'''.E, e ∈ H.E ∧ ¬e ⊆ Z₂ ∧ Disjoint (closure e) Z₂ ∨ e ∈ H''.E ∧
      Disjoint (closure e) Z₁ ∧ eMap''' e = η''.eMap e) :
    ∀ e ∈ H'''.E, eMap''' e ∈ E(G) ∧ (∀ (x y : α), G.IsLink (eMap''' e) x y → x ∈ vMap''' ''
      H'''.V ∧ y ∈ vMap''' '' H'''.V) ∧ ∀ v ∈ H'''.V, G.Inc (eMap''' e) (vMap''' v) ↔ v ∈ closure
      e := by
  intro e he
  rcases hE'''_cases e he with ⟨heH, hnotZ₂, hdisj₂⟩ | ⟨heH'', hdisj₁, he_map''⟩
  · rw [heMap'''_notZ₂ e hnotZ₂]
    have he_im : η.eMap e ∈ E(η.imageGraph) := η.bijOn_e.mapsTo heH
    have hends_sub : ∀ u ∈ closure e ∩ H.V, u ∈ H'''.V ∧ vMap''' u = η.vMap u := by
      rintro u ⟨hu_cl, huH⟩
      have hu_notZ₂ : u ∉ Z₂ := Set.disjoint_left.mp hdisj₂ hu_cl
      exact ⟨(hH'''_V u).mpr (Or.inl ⟨huH, hu_notZ₂⟩), hvMap'''_notZ₂ u hu_notZ₂⟩
    refine ⟨η.imageGraph_le.edgeSet_mono he_im, ?_, ?_⟩
    · intro x y hlinkG
      have hlink_im : η.imageGraph.IsLink (η.eMap e) x y :=
        (η.imageGraph_le.isLink_iff he_im).mpr hlinkG
      obtain ⟨u, huH, rfl⟩ := η.bijOn_v.surjOn (η.imageGraph.left_mem_of_isLink hlink_im)
      obtain ⟨w, hwH, rfl⟩ := η.bijOn_v.surjOn (η.imageGraph.left_mem_of_isLink hlink_im.symm)
      have hu_cl : u ∈ closure e := (η.inc_iff e heH u huH).mp ⟨η.vMap w, hlink_im⟩
      have hw_cl : w ∈ closure e := (η.inc_iff e heH w hwH).mp ⟨η.vMap u, hlink_im.symm⟩
      obtain ⟨hu''', humap⟩ := hends_sub u ⟨hu_cl, huH⟩
      obtain ⟨hw''', hwmap⟩ := hends_sub w ⟨hw_cl, hwH⟩
      exact ⟨⟨u, hu''', humap⟩, ⟨w, hw''', hwmap⟩⟩
    · intro v hv'''
      constructor
      · rintro ⟨w, hlinkG⟩
        have hlink_im : η.imageGraph.IsLink (η.eMap e) (vMap''' v) w :=
          (η.imageGraph_le.isLink_iff he_im).mpr hlinkG
        obtain ⟨u, huH, humap⟩ := η.bijOn_v.surjOn (η.imageGraph.left_mem_of_isLink hlink_im)
        have hu_cl : u ∈ closure e := (η.inc_iff e heH u huH).mp ⟨w, humap ▸ hlink_im⟩
        obtain ⟨hu''', humap'''⟩ := hends_sub u ⟨hu_cl, huH⟩
        have huv : u = v := hinj_v hu''' hv''' (humap'''.trans humap)
        exact huv ▸ hu_cl
      · intro hv_cl
        have hv_notZ₂ : v ∉ Z₂ := Set.disjoint_left.mp hdisj₂ hv_cl
        have hvH : v ∈ H.V := ((hH'''_V v).mp hv''').resolve_right (fun h => hv_notZ₂ h.2) |>.1
        rw [hvMap'''_notZ₂ v hv_notZ₂]
        obtain ⟨w, hlink_im⟩ := (η.inc_iff e heH v hvH).mpr hv_cl
        exact ⟨w, (η.imageGraph_le.isLink_iff he_im).mp hlink_im⟩
  · rw [he_map'']
    have he_im : η''.eMap e ∈ E(η''.imageGraph) := η''.bijOn_e.mapsTo heH''
    have hends_sub : ∀ u ∈ closure e ∩ H''.V, u ∈ H'''.V ∧ vMap''' u = η''.vMap u := by
      rintro u ⟨hu_cl, huH''⟩
      have hu_notZ₁ : u ∉ Z₁ := Set.disjoint_left.mp hdisj₁ hu_cl
      have hu''' : u ∈ H'''.V := (hV_notZ₁ u hu_notZ₁).1.mpr huH''
      exact ⟨hu''', (hV_notZ₁ u hu_notZ₁).2 hu'''⟩
    refine ⟨η''.imageGraph_le.edgeSet_mono he_im, ?_, ?_⟩
    · intro x y hlinkG
      have hlink_im : η''.imageGraph.IsLink (η''.eMap e) x y :=
        (η''.imageGraph_le.isLink_iff he_im).mpr hlinkG
      obtain ⟨u, huH'', rfl⟩ := η''.bijOn_v.surjOn (η''.imageGraph.left_mem_of_isLink hlink_im)
      obtain ⟨w, hwH'', rfl⟩ := η''.bijOn_v.surjOn (η''.imageGraph.left_mem_of_isLink hlink_im.symm)
      have hu_cl : u ∈ closure e := (η''.inc_iff e heH'' u huH'').mp ⟨η''.vMap w, hlink_im⟩
      have hw_cl : w ∈ closure e := (η''.inc_iff e heH'' w hwH'').mp ⟨η''.vMap u, hlink_im.symm⟩
      obtain ⟨hu''', humap⟩ := hends_sub u ⟨hu_cl, huH''⟩
      obtain ⟨hw''', hwmap⟩ := hends_sub w ⟨hw_cl, hwH''⟩
      exact ⟨⟨u, hu''', humap⟩, ⟨w, hw''', hwmap⟩⟩
    · intro v hv'''
      constructor
      · rintro ⟨w, hlinkG⟩
        have hlink_im : η''.imageGraph.IsLink (η''.eMap e) (vMap''' v) w :=
          (η''.imageGraph_le.isLink_iff he_im).mpr hlinkG
        obtain ⟨u, huH'', humap⟩ := η''.bijOn_v.surjOn (η''.imageGraph.left_mem_of_isLink hlink_im)
        have hu_cl : u ∈ closure e := (η''.inc_iff e heH'' u huH'').mp ⟨w, humap ▸ hlink_im⟩
        obtain ⟨hu''', humap'''⟩ := hends_sub u ⟨hu_cl, huH''⟩
        have huv : u = v := hinj_v hu''' hv''' (humap'''.trans humap)
        exact huv ▸ hu_cl
      · intro hv_cl
        have hv_notZ₁ : v ∉ Z₁ := Set.disjoint_left.mp hdisj₁ hv_cl
        have hvH'' : v ∈ H''.V := (hV_notZ₁ v hv_notZ₁).1.mp hv'''
        rw [(hV_notZ₁ v hv_notZ₁).2 hv''']
        obtain ⟨w, hlink_im⟩ := (η''.inc_iff e heH'' v hvH'').mpr hv_cl
        exact ⟨w, (η''.imageGraph_le.isLink_iff he_im).mp hlink_im⟩

private theorem combined_drawing_edge_map_is_injective
    {α : Type u}
    {β : Type v}
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {G : Graph α β}
    {H : Drawing S}
    {H' : Drawing S}
    {H'' : Drawing S}
    {η : SpanEmbedding H G}
    {η' : SpanEmbedding H' G}
    {η'' : SpanEmbedding H'' G}
    {θ_star : ℕ}
    {θ : ℕ}
    {lam₁ : ℕ}
    {lam₂ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {d' : Set S → Set S → ℕ}
    {z₁ : Set S}
    {z₂ : Set S}
    (hlam₁ : 4 ≤ lam₁)
    (hRearr₁ : IsRearrangedWithin G H H' η η' θ_star θ lam₁ T_star T T' d d' z₁)
    (Z₁ : Set S)
    (hZoneEqZ₁ : Z₁ = atomZone H d z₁ lam₁)
    (Z₂ : Set S)
    (hZoneEqZ₂ : Z₂ = atomZone H' d' z₂ lam₂)
    (hS : IsClosedSurface S)
    [hConn : ConnectedSpace S]
    (hMetric : HasTangleMetric H θ T d)
    (_z₃ : Set S)
    (hDisj_cl : Disjoint (closure (atomZone H d z₁ lam₁)) (closure (atomZone H' d' z₂ lam₂)))
    (H''' : Drawing S)
    (hH'''_V : ∀ (v : S), v ∈ H'''.V ↔ v ∈ H.V ∧ v ∉ Z₂ ∨ v ∈ H''.V ∧ v ∈ Z₂)
    (vMap''' : S → α)
    (eMap''' : Set S → β)
    (heMap'''_notZ₂ : ∀ (e : Set S), ¬e ⊆ Z₂ → eMap''' e = η.eMap e)
    (hE_notZ₁ : ∀ (e : Set S), ¬e ⊆ Z₁ → (e ∈ H'''.E ↔ e ∈ H''.E) ∧ (e ∈ H'''.E → eMap''' e =
      η''.eMap e))
    (hE'''_cases : ∀ e ∈ H'''.E, e ∈ H.E ∧ ¬e ⊆ Z₂ ∧ Disjoint (closure e) Z₂ ∨ e ∈ H''.E ∧
      Disjoint (closure e) Z₁ ∧ eMap''' e = η''.eMap e)
    (hE_inc_G : ∀ e ∈ H'''.E, eMap''' e ∈ E(G) ∧ (∀ (x y : α), G.IsLink (eMap''' e) x y → x ∈
      vMap''' '' H'''.V ∧ y ∈ vMap''' '' H'''.V) ∧ ∀ v ∈ H'''.V, G.Inc (eMap''' e) (vMap''' v) ↔ v
      ∈ closure e) :
    InjOn eMap''' H'''.E := by
  subst Z₂
  let Z₂ := atomZone H' d' z₂ lam₂
  subst Z₁
  let Z₁ := atomZone H d z₁ lam₁
  intro e₁ he₁ e₂ he₂ hEq
  rcases hE'''_cases e₁ he₁ with ⟨he₁H, hnot₁, hdisj₂_1⟩ | ⟨he₁H'', hdisj₁_1, hmap₁''⟩ <;>
    rcases hE'''_cases e₂ he₂ with ⟨he₂H, hnot₂, hdisj₂_2⟩ | ⟨he₂H'', hdisj₁_2, hmap₂''⟩
  · rw [heMap'''_notZ₂ e₁ hnot₁, heMap'''_notZ₂ e₂ hnot₂] at hEq
    exact η.bijOn_e.injOn he₁H he₂H hEq
  · have hv_ex : (closure e₁ ∩ H'''.V).Nonempty := by
      rcases H'''.edge_cond e₁ he₁ with ⟨x, _, _, hcl, _⟩ | ⟨x, hcl, _⟩
      · rw [hcl]; exact ⟨x, Or.inl rfl⟩
      · rw [hcl]; exact ⟨x, rfl⟩
    obtain ⟨v, hv_cl₁, hv'''⟩ := hv_ex
    have hv_cl₂ : v ∈ closure e₂ := by
      rw [← (hE_inc_G e₂ he₂).2.2 v hv''', ← hEq]
      exact ((hE_inc_G e₁ he₁).2.2 v hv''').mpr hv_cl₁
    have he₁_notZ₁ : ¬ e₁ ⊆ Z₁ := by
      intro hsub₁
      obtain ⟨x, hxe₁⟩ := he₁H.1
      have hxZ₁ : x ∈ Z₁ := hsub₁ hxe₁
      rcases hRearr₁.atomZone_dichotomy.2.2.2.2.1 e₁ he₁H with ⟨hd_le₁, _⟩ | ⟨_, hdisj, _, _⟩
      · have hv_H : v ∈ H.V := by
          rcases (hH'''_V v).mp hv''' with ⟨hvH, _⟩ | ⟨_, hvZ₂⟩
          · exact hvH
          · exact (Set.disjoint_left.mp hDisj_cl (closure_mono hsub₁ hv_cl₁)
              (subset_closure hvZ₂)).elim
        have hvZ₁ : v ∈ Z₁ := by
          have hv_le := dist_vertex_le_of_dist_edge_le hS hConn hMetric hRearr₁.z_mem he₁H hv_H
            hv_cl₁
            (by omega) hd_le₁
          exact (mem_atomZone_iff_of_mem_atom (Or.inl (Or.inl ⟨v, hv_H, rfl⟩)) rfl).mpr hv_le
        exact Set.disjoint_left.mp hdisj₁_2 hv_cl₂ hvZ₁
      · exact Set.disjoint_left.mp hdisj hxe₁ hxZ₁
    have he₁H'' : e₁ ∈ H''.E := (hE_notZ₁ e₁ he₁_notZ₁).1.mp he₁
    rw [(hE_notZ₁ e₁ he₁_notZ₁).2 he₁, hmap₂''] at hEq
    exact η''.bijOn_e.injOn he₁H'' he₂H'' hEq
  · have hv_ex : (closure e₂ ∩ H'''.V).Nonempty := by
      rcases H'''.edge_cond e₂ he₂ with ⟨x, _, _, hcl, _⟩ | ⟨x, hcl, _⟩
      · rw [hcl]; exact ⟨x, Or.inl rfl⟩
      · rw [hcl]; exact ⟨x, rfl⟩
    obtain ⟨v, hv_cl₂, hv'''⟩ := hv_ex
    have hv_cl₁ : v ∈ closure e₁ := by
      rw [← (hE_inc_G e₁ he₁).2.2 v hv''', hEq]
      exact ((hE_inc_G e₂ he₂).2.2 v hv''').mpr hv_cl₂
    have he₂_notZ₁ : ¬ e₂ ⊆ Z₁ := by
      intro hsub₂
      obtain ⟨x, hxe₂⟩ := he₂H.1
      have hxZ₁ : x ∈ Z₁ := hsub₂ hxe₂
      rcases hRearr₁.atomZone_dichotomy.2.2.2.2.1 e₂ he₂H with ⟨hd_le₂, _⟩ | ⟨_, hdisj, _, _⟩
      · have hv_H : v ∈ H.V := by
          rcases (hH'''_V v).mp hv''' with ⟨hvH, _⟩ | ⟨_, hvZ₂⟩
          · exact hvH
          · exact (Set.disjoint_left.mp hDisj_cl (closure_mono hsub₂ hv_cl₂)
              (subset_closure hvZ₂)).elim
        have hvZ₁ : v ∈ Z₁ := by
          have hv_le := dist_vertex_le_of_dist_edge_le hS hConn hMetric hRearr₁.z_mem he₂H hv_H
            hv_cl₂
            (by omega) hd_le₂
          exact (mem_atomZone_iff_of_mem_atom (Or.inl (Or.inl ⟨v, hv_H, rfl⟩)) rfl).mpr hv_le
        exact Set.disjoint_left.mp hdisj₁_1 hv_cl₁ hvZ₁
      · exact Set.disjoint_left.mp hdisj hxe₂ hxZ₁
    have he₂H'' : e₂ ∈ H''.E := (hE_notZ₁ e₂ he₂_notZ₁).1.mp he₂
    rw [hmap₁'', (hE_notZ₁ e₂ he₂_notZ₁).2 he₂] at hEq
    exact η''.bijOn_e.injOn he₁H'' he₂H'' hEq
  · rw [hmap₁'', hmap₂''] at hEq
    exact η''.bijOn_e.injOn he₁H'' he₂H'' hEq

private theorem first_drawing_atoms_off_second_zone_survive
    {α : Type u}
    {β : Type v}
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {G : Graph α β}
    {H : Drawing S}
    {H' : Drawing S}
    {H'' : Drawing S}
    {η : SpanEmbedding H G}
    {η' : SpanEmbedding H' G}
    {η'' : SpanEmbedding H'' G}
    {θ_star : ℕ}
    {θ : ℕ}
    {lam₁ : ℕ}
    {lam₂ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {d' : Set S → Set S → ℕ}
    {d'' : Set S → Set S → ℕ}
    {z₁ : Set S}
    {z₂ : Set S}
    (hRearr₁ : IsRearrangedWithin G H H' η η' θ_star θ lam₁ T_star T T' d d' z₁)
    (hRearr₂ : IsRearrangedWithin G H' H'' η' η'' θ_star (θ - (4 * lam₁ + 2)) lam₂ T_star T' T''
      d' d'' z₂)
    (Z₂ : Set S)
    (hZoneEqZ₂ : Z₂ = atomZone H' d' z₂ lam₂)
    (hDisj_cl : Disjoint (closure (atomZone H d z₁ lam₁)) (closure (atomZone H' d' z₂ lam₂)))
    (H''' : Drawing S)
    (hH'''_V : ∀ (v : S), v ∈ H'''.V ↔ v ∈ H.V ∧ v ∉ Z₂ ∨ v ∈ H''.V ∧ v ∈ Z₂)
    (hH'''_E : ∀ (e : Set S), e ∈ H'''.E ↔ e ∈ H.E ∧ ¬e ⊆ Z₂ ∨ e ∈ H''.E ∧ e ⊆ Z₂)
    (this : LocallyConnectedSpace S)
    (hU'''_iff_notZ₂ : ∀ x ∉ Z₂, x ∈ H'''.U ↔ x ∈ H.U)
    (hU'''_iff_Z₂ : ∀ x ∈ Z₂, x ∈ H'''.U ↔ x ∈ H''.U) :
    ∀ a ∈ H.A, Disjoint a Z₂ → a ∈ H'''.A := by
  subst Z₂
  let Z₂ := atomZone H' d' z₂ lam₂
  intro a ha hdisj
  rcases ha with (⟨v, hvH, rfl⟩ | heH) | hrH
  · have hvnot : v ∉ Z₂ := Set.disjoint_left.mp hdisj rfl
    exact Or.inl (Or.inl ⟨v, (hH'''_V v).mpr (Or.inl ⟨hvH, hvnot⟩), rfl⟩)
  · obtain ⟨x, hxe⟩ := heH.1
    have henot : ¬ a ⊆ Z₂ := fun hsub => Set.disjoint_left.mp hdisj hxe (hsub hxe)
    exact Or.inl (Or.inr ((hH'''_E a).mpr (Or.inl ⟨heH, henot⟩)))
  · refine Or.inr (region_mem_of_disjoint_U hrH ?_ ?_)
    · refine Set.disjoint_left.mpr fun x hxr hxU''' => ?_
      have hx_notZ₂ : x ∉ Z₂ := Set.disjoint_left.mp hdisj hxr
      exact region_subset hrH hxr ((hU'''_iff_notZ₂ x hx_notZ₂).mp hxU''')
    · intro x hx_diff
      have hx_U : x ∈ H.U := closure_atom_diff_subset_U H (Or.inr hrH) hx_diff
      by_cases hxZ₂ : x ∈ Z₂
      · rcases hRearr₁.atomZone_dichotomy.1 a (Or.inr hrH) with ⟨_, hsub₁⟩ | ⟨_, _, haH'⟩
        · exact (Set.disjoint_left.mp hDisj_cl (closure_mono hsub₁ hx_diff.1)
            (subset_closure hxZ₂)).elim
        · rcases hRearr₂.atomZone_dichotomy.1 a haH' with ⟨_, hsub₂⟩ | ⟨_, _, haH''⟩
          · obtain ⟨y, hyr⟩ := region_nonempty hrH
            exact (Set.disjoint_left.mp hdisj hyr (hsub₂ hyr)).elim
          · exact (hU'''_iff_Z₂ x hxZ₂).mpr (closure_atom_diff_subset_U H'' haH'' hx_diff)
      · exact (hU'''_iff_notZ₂ x hxZ₂).mpr hx_U

private theorem second_drawing_atoms_off_first_zone_survive
    {α : Type u}
    {β : Type v}
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {G : Graph α β}
    {H : Drawing S}
    {H' : Drawing S}
    {H'' : Drawing S}
    {η : SpanEmbedding H G}
    {η' : SpanEmbedding H' G}
    {η'' : SpanEmbedding H'' G}
    {θ_star : ℕ}
    {θ : ℕ}
    {lam₁ : ℕ}
    {lam₂ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {d' : Set S → Set S → ℕ}
    {d'' : Set S → Set S → ℕ}
    {z₁ : Set S}
    {z₂ : Set S}
    (hRearr₁ : IsRearrangedWithin G H H' η η' θ_star θ lam₁ T_star T T' d d' z₁)
    (hRearr₂ : IsRearrangedWithin G H' H'' η' η'' θ_star (θ - (4 * lam₁ + 2)) lam₂ T_star T' T''
      d' d'' z₂)
    (Z₁ : Set S)
    (hZoneEqZ₁ : Z₁ = atomZone H d z₁ lam₁)
    (Z₂ : Set S)
    (hZoneEqZ₂ : Z₂ = atomZone H' d' z₂ lam₂)
    (hDisj_cl : Disjoint (closure (atomZone H d z₁ lam₁)) (closure (atomZone H' d' z₂ lam₂)))
    (hDisj_Z : Disjoint Z₁ Z₂)
    (H''' : Drawing S)
    (vMap''' : S → α)
    (eMap''' : Set S → β)
    (hV_notZ₁ : ∀ v ∉ Z₁, (v ∈ H'''.V ↔ v ∈ H''.V) ∧ (v ∈ H'''.V → vMap''' v = η''.vMap v))
    (hE_notZ₁ : ∀ (e : Set S), ¬e ⊆ Z₁ → (e ∈ H'''.E ↔ e ∈ H''.E) ∧ (e ∈ H'''.E → eMap''' e =
      η''.eMap e))
    (this : LocallyConnectedSpace S)
    (hU'''_iff_notZ₂ : ∀ x ∉ Z₂, x ∈ H'''.U ↔ x ∈ H.U)
    (hU'''_iff_notZ₁ : ∀ x ∉ Z₁, x ∈ H'''.U ↔ x ∈ H''.U) :
    ∀ a ∈ H''.A, Disjoint a Z₁ → a ∈ H'''.A := by
  subst Z₂
  let Z₂ := atomZone H' d' z₂ lam₂
  subst Z₁
  let Z₁ := atomZone H d z₁ lam₁
  intro a ha hdisj
  rcases ha with (⟨v, hvH'', rfl⟩ | heH'') | hrH''
  · have hvnot : v ∉ Z₁ := Set.disjoint_left.mp hdisj rfl
    exact Or.inl (Or.inl ⟨v, (hV_notZ₁ v hvnot).1.mpr hvH'', rfl⟩)
  · obtain ⟨x, hxe⟩ := heH''.1
    have henot : ¬ a ⊆ Z₁ := fun hsub => Set.disjoint_left.mp hdisj hxe (hsub hxe)
    exact Or.inl (Or.inr ((hE_notZ₁ a henot).1.mpr heH''))
  · refine Or.inr (region_mem_of_disjoint_U hrH'' ?_ ?_)
    · refine Set.disjoint_left.mpr fun x hxr hxU''' => ?_
      have hx_notZ₁ : x ∉ Z₁ := Set.disjoint_left.mp hdisj hxr
      exact region_subset hrH'' hxr ((hU'''_iff_notZ₁ x hx_notZ₁).mp hxU''')
    · intro x hx_diff
      have hx_U'' : x ∈ H''.U := closure_atom_diff_subset_U H'' (Or.inr hrH'') hx_diff
      by_cases hxZ₁ : x ∈ Z₁
      · rcases hRearr₂.atomZone_dichotomy.2.1 a (Or.inr hrH'') with hsub₂ | ⟨_, haH', _⟩
        · exact (Set.disjoint_left.mp hDisj_cl (subset_closure hxZ₁) (closure_mono hsub₂
            hx_diff.1)).elim
        · rcases hRearr₁.atomZone_dichotomy.2.1 a haH' with hsub₁ | ⟨_, haH, _⟩
          · obtain ⟨y, hyr⟩ := region_nonempty hrH''
            exact (Set.disjoint_left.mp hdisj hyr (hsub₁ hyr)).elim
          · have hx_notZ₂ : x ∉ Z₂ := Set.disjoint_left.mp hDisj_Z hxZ₁
            exact (hU'''_iff_notZ₂ x hx_notZ₂).mpr (closure_atom_diff_subset_U H haH hx_diff)
      · exact (hU'''_iff_notZ₁ x hxZ₁).mpr hx_U''

private theorem retained_edges_preserve_outer_endpoints
    {α : Type u}
    {β : Type v}
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {G : Graph α β}
    {H : Drawing S}
    {H' : Drawing S}
    {H'' : Drawing S}
    {η : SpanEmbedding H G}
    {η' : SpanEmbedding H' G}
    {η'' : SpanEmbedding H'' G}
    {θ_star : ℕ}
    {θ : ℕ}
    {lam₁ : ℕ}
    {lam₂ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {d' : Set S → Set S → ℕ}
    {d'' : Set S → Set S → ℕ}
    {z₁ : Set S}
    {z₂ : Set S}
    (hRearr₁ : IsRearrangedWithin G H H' η η' θ_star θ lam₁ T_star T T' d d' z₁)
    (hRearr₂ : IsRearrangedWithin G H' H'' η' η'' θ_star (θ - (4 * lam₁ + 2)) lam₂ T_star T' T''
      d' d'' z₂)
    (Z₁ : Set S) (hZoneEqZ₁ : Z₁ = atomZone H d z₁ lam₁)
    (Z₂ : Set S) (hZoneEqZ₂ : Z₂ = atomZone H' d' z₂ lam₂)
    (hH_edge_cl_disj_Z₁ : ∀ e ∈ H.E, ¬Disjoint (closure e) Z₂ → Disjoint (closure e) Z₁)
    (V''' : Set S) (hV : V''' = {v ∈ H.V | v ∉ Z₂} ∪ {v ∈ H''.V | v ∈ Z₂}) :
    ∀ e ∈ H.E, ¬e ⊆ Z₂ → closure e ∩ H.V ⊆ H.V ∩ V''' := by
  subst V'''
  subst Z₁ Z₂
  let Z₁ := atomZone H d z₁ lam₁
  let Z₂ := atomZone H' d' z₂ lam₂
  rintro e heH hnot v ⟨hv_cl, hvH⟩
  refine ⟨hvH, ?_⟩
  by_cases hvZ₂ : v ∈ Z₂
  · right
    have hdisj₁ : Disjoint (closure e) Z₁ :=
      hH_edge_cl_disj_Z₁ e heH (Set.not_disjoint_iff.mpr ⟨v, hv_cl, hvZ₂⟩)
    have he_notZ₁ : ¬ e ⊆ Z₁ := by
      obtain ⟨x, hxe⟩ := heH.1
      exact fun hsub => Set.disjoint_left.mp hdisj₁ (subset_closure hxe) (hsub hxe)
    rcases hRearr₁.atomZone_dichotomy.2.2.2.2.1 e heH with ⟨_, hZ₁⟩ | ⟨_, _, heH', _⟩
    · exact (he_notZ₁ hZ₁).elim
    · rcases hRearr₂.atomZone_dichotomy.2.2.2.2.1 e heH' with ⟨_, hZ₂⟩ | ⟨_, _, heH'', _⟩
      · exact (hnot hZ₂).elim
      · have hvH'' : v ∈ (closure e ∩ H''.V) := by
          rw [closure_inter_V_eq_diff H'' heH'', ← closure_inter_V_eq_diff H heH]
          exact ⟨hv_cl, hvH⟩
        exact ⟨hvH''.2, hvZ₂⟩
  · exact Or.inl ⟨hvH, hvZ₂⟩

private theorem inserted_edges_preserve_inner_endpoints
    {α : Type u}
    {β : Type v}
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {G : Graph α β}
    {H : Drawing S}
    {H' : Drawing S}
    {H'' : Drawing S}
    {η : SpanEmbedding H G}
    {η' : SpanEmbedding H' G}
    {η'' : SpanEmbedding H'' G}
    {θ_star : ℕ}
    {θ : ℕ}
    {lam₁ : ℕ}
    {lam₂ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {d' : Set S → Set S → ℕ}
    {d'' : Set S → Set S → ℕ}
    {z₁ : Set S}
    {z₂ : Set S}
    (hRearr₁ : IsRearrangedWithin G H H' η η' θ_star θ lam₁ T_star T T' d d' z₁)
    (hRearr₂ : IsRearrangedWithin G H' H'' η' η'' θ_star (θ - (4 * lam₁ + 2)) lam₂ T_star T' T''
      d' d'' z₂)
    (Z₂ : Set S) (hZoneEqZ₂ : Z₂ = atomZone H' d' z₂ lam₂)
    (hDisj_cl : Disjoint (closure (atomZone H d z₁ lam₁)) (closure (atomZone H' d' z₂ lam₂)))
    (V''' : Set S) (hV : V''' = {v ∈ H.V | v ∉ Z₂} ∪ {v ∈ H''.V | v ∈ Z₂}) :
    ∀ e ∈ H''.E, e ⊆ Z₂ → closure e ∩ H''.V ⊆ H''.V ∩ V''' := by
  subst V'''
  subst Z₂
  let Z₁ := atomZone H d z₁ lam₁
  let Z₂ := atomZone H' d' z₂ lam₂
  rintro e heH'' hsub v ⟨hv_cl, hvH''⟩
  refine ⟨hvH'', ?_⟩
  by_cases hvZ₂ : v ∈ Z₂
  · exact Or.inr ⟨hvH'', hvZ₂⟩
  · left
    rcases hRearr₂.atomZone_dichotomy.2.2.2.1 v hvH'' with hZ₂ | ⟨_, hvH', _⟩
    · exact (hvZ₂ hZ₂).elim
    · have hv_clZ₂ : v ∈ closure Z₂ := closure_mono hsub hv_cl
      have hv_notZ₁ : v ∉ Z₁ :=
        Set.disjoint_right.mp (hDisj_cl.mono subset_closure Subset.rfl) hv_clZ₂
      rcases hRearr₁.atomZone_dichotomy.2.2.2.1 v hvH' with hZ₁ | ⟨_, hvH, _⟩
      · exact (hv_notZ₁ hZ₁).elim
      · exact ⟨hvH, hvZ₂⟩

private theorem retained_edges_meet_new_vertices_at_old_ends
    {S : Type w}
    [TopologicalSpace S]
    {H : Drawing S}
    {H'' : Drawing S}
    (Z₂ : Set S)
    (hH_edge_disj_Z₂ : ∀ e ∈ H.E, ¬e ⊆ Z₂ → Disjoint e Z₂)
    (V''' : Set S) (hV : V''' = {v ∈ H.V | v ∉ Z₂} ∪ {v ∈ H''.V | v ∈ Z₂})
    (A₁ : Drawing S)
    (M₂ : Drawing S)
    (hA₁_V : A₁.V = H.V ∩ V''')
    (hA₁_E : A₁.E = {e | e ∈ H.E ∧ ¬e ⊆ Z₂})
    (hM₂_V : M₂.V = H''.V ∩ V''') :
    ∀ e₁ ∈ A₁.E, closure e₁ ∩ M₂.V ⊆ A₁.V := by
  subst V'''
  rw [hA₁_E, hM₂_V, hA₁_V]
  rintro e₁ ⟨he₁, hnot₁⟩ x ⟨hx_cl, hxH'', hxV⟩
  have hx_not_e₁ : x ∉ e₁ := by
    intro hxe₁
    have hx_notZ₂ : x ∉ Z₂ := Set.disjoint_left.mp (hH_edge_disj_Z₂ e₁ he₁ hnot₁) hxe₁
    have hxH : x ∈ H.V := (hxV.resolve_right fun h => hx_notZ₂ h.2).1
    exact (he₁.2.1 hxe₁).2 hxH
  have hx_diff : x ∈ closure e₁ ∩ H.V := by
    rw [closure_inter_V_eq_diff H he₁]
    exact ⟨hx_cl, hx_not_e₁⟩
  exact ⟨hx_diff.2, hxV⟩

private theorem inserted_edges_meet_old_vertices_at_new_ends
    {S : Type w}
    [TopologicalSpace S]
    {H : Drawing S}
    {H'' : Drawing S}
    (Z₂ : Set S)
    (V''' : Set S) (hV : V''' = {v ∈ H.V | v ∉ Z₂} ∪ {v ∈ H''.V | v ∈ Z₂})
    (A₁ : Drawing S)
    (M₂ : Drawing S)
    (hA₁_V : A₁.V = H.V ∩ V''')
    (hM₂_V : M₂.V = H''.V ∩ V''')
    (hM₂_E : M₂.E = {e | e ∈ H''.E ∧ e ⊆ Z₂}) :
    ∀ e₂ ∈ M₂.E, closure e₂ ∩ A₁.V ⊆ M₂.V := by
  subst V'''
  rw [hM₂_E, hA₁_V, hM₂_V]
  rintro e₂ ⟨he₂, hsub₂⟩ x ⟨hx_cl, hxH, hxV⟩
  have hx_not_e₂ : x ∉ e₂ := by
    intro hxe₂
    have hxZ₂ : x ∈ Z₂ := hsub₂ hxe₂
    have hxH'' : x ∈ H''.V := (hxV.resolve_left fun h => h.2 hxZ₂).1
    exact (he₂.2.1 hxe₂).2 hxH''
  have hx_diff : x ∈ closure e₂ ∩ H''.V := by
    rw [closure_inter_V_eq_diff H'' he₂]
    exact ⟨hx_cl, hx_not_e₂⟩
  exact ⟨hx_diff.2, hxV⟩

private theorem retained_and_inserted_edge_intersections
    {S : Type w}
    [TopologicalSpace S]
    {H : Drawing S}
    {H'' : Drawing S}
    (Z₂ : Set S)
    (hH_edge_disj_Z₂ : ∀ e ∈ H.E, ¬e ⊆ Z₂ → Disjoint e Z₂)
    (V''' : Set S)
    (A₁ : Drawing S)
    (M₂ : Drawing S)
    (hA₁_ends : ∀ e ∈ H.E, ¬e ⊆ Z₂ → closure e ∩ H.V ⊆ H.V ∩ V''')
    (hM₂_ends : ∀ e ∈ H''.E, e ⊆ Z₂ → closure e ∩ H''.V ⊆ H''.V ∩ V''')
    (hA₁_V : A₁.V = H.V ∩ V''')
    (hA₁_E : A₁.E = {e | e ∈ H.E ∧ ¬e ⊆ Z₂})
    (hM₂_V : M₂.V = H''.V ∩ V''')
    (hM₂_E : M₂.E = {e | e ∈ H''.E ∧ e ⊆ Z₂})
    (h1_union : ∀ e₁ ∈ A₁.E, closure e₁ ∩ M₂.V ⊆ A₁.V)
    (h2_union : ∀ e₂ ∈ M₂.E, closure e₂ ∩ A₁.V ⊆ M₂.V) :
    ∀ e₁ ∈ A₁.E, ∀ e₂ ∈ M₂.E, closure e₁ ∩ closure e₂ ⊆ A₁.V ∩ M₂.V := by
  intro e₁ he₁ e₂ he₂ x ⟨hx_cl₁, hx_cl₂⟩
  have ⟨he₁H, hnot₁⟩ : e₁ ∈ H.E ∧ ¬ e₁ ⊆ Z₂ := by rwa [hA₁_E] at he₁
  have ⟨he₂H'', hsub₂⟩ : e₂ ∈ H''.E ∧ e₂ ⊆ Z₂ := by rwa [hM₂_E] at he₂
  have hx_not_e₂ : x ∉ e₂ := by
    intro hxe₂
    have hxZ₂ : x ∈ Z₂ := hsub₂ hxe₂
    have hx_not_e₁ : x ∉ e₁ :=
      fun hxe₁ => Set.disjoint_left.mp (hH_edge_disj_Z₂ e₁ he₁H hnot₁) hxe₁ hxZ₂
    have hx_H : x ∈ closure e₁ ∩ H.V := by
      rw [closure_inter_V_eq_diff H he₁H]
      exact ⟨hx_cl₁, hx_not_e₁⟩
    have hxA₁ : x ∈ A₁.V := hA₁_V ▸ hA₁_ends e₁ he₁H hnot₁ hx_H
    have hxM₂ : x ∈ M₂.V := h2_union e₂ he₂ ⟨hx_cl₂, hxA₁⟩
    exact (he₂H''.2.1 hxe₂).2 (hM₂_V ▸ hxM₂).1
  have hx_H'' : x ∈ closure e₂ ∩ H''.V := by
    rw [closure_inter_V_eq_diff H'' he₂H'']
    exact ⟨hx_cl₂, hx_not_e₂⟩
  have hxM₂ : x ∈ M₂.V := hM₂_V ▸ hM₂_ends e₂ he₂H'' hsub₂ hx_H''
  exact ⟨h1_union e₁ he₁ ⟨hx_cl₁, hxM₂⟩, hxM₂⟩

private theorem outside_inner_zone_union_agrees_with_original
    {S : Type w}
    [TopologicalSpace S]
    {H : Drawing S}
    {H'' : Drawing S}
    (Z₂ : Set S)
    (H''' : Drawing S)
    (hH'''_V : ∀ (v : S), v ∈ H'''.V ↔ v ∈ H.V ∧ v ∉ Z₂ ∨ v ∈ H''.V ∧ v ∈ Z₂)
    (hH'''_E : ∀ (e : Set S), e ∈ H'''.E ↔ e ∈ H.E ∧ ¬e ⊆ Z₂ ∨ e ∈ H''.E ∧ e ⊆ Z₂) :
    ∀ x ∉ Z₂, x ∈ H'''.U ↔ x ∈ H.U := by
  intro x hx_notZ₂
  rw [mem_U_iff_mem_V_or_mem_E H''' x, mem_U_iff_mem_V_or_mem_E H x]
  constructor
  · rintro (hxV''' | ⟨e, he''', hxe⟩)
    · exact Or.inl (((hH'''_V x).mp hxV''').resolve_right (fun h => hx_notZ₂ h.2) |>.1)
    · exact Or.inr ⟨e, ((hH'''_E e).mp he''').resolve_right (fun h => hx_notZ₂ (h.2 hxe)) |>.1,
        hxe⟩
  · rintro (hxVH | ⟨e, heH, hxe⟩)
    · exact Or.inl ((hH'''_V x).mpr (Or.inl ⟨hxVH, hx_notZ₂⟩))
    · have henot : ¬ e ⊆ Z₂ := fun hsub => hx_notZ₂ (hsub hxe)
      exact Or.inr ⟨e, (hH'''_E e).mpr (Or.inl ⟨heH, henot⟩), hxe⟩

private theorem inside_inner_zone_union_agrees_with_replacement
    {α : Type u}
    {β : Type v}
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {G : Graph α β}
    {H : Drawing S}
    {H' : Drawing S}
    {H'' : Drawing S}
    {η' : SpanEmbedding H' G}
    {η'' : SpanEmbedding H'' G}
    {θ_star : ℕ}
    {θ : ℕ}
    {lam₁ : ℕ}
    {lam₂ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d' : Set S → Set S → ℕ}
    {d'' : Set S → Set S → ℕ}
    {z₂ : Set S}
    (hRearr₂ : IsRearrangedWithin G H' H'' η' η'' θ_star (θ - (4 * lam₁ + 2)) lam₂ T_star T' T''
      d' d'' z₂)
    (Z₂ : Set S) (hZoneEqZ₂ : Z₂ = atomZone H' d' z₂ lam₂)
    (hH_edge_disj_Z₂ : ∀ e ∈ H.E, ¬e ⊆ Z₂ → Disjoint e Z₂)
    (H''' : Drawing S)
    (hH'''_V : ∀ (v : S), v ∈ H'''.V ↔ v ∈ H.V ∧ v ∉ Z₂ ∨ v ∈ H''.V ∧ v ∈ Z₂)
    (hH'''_E : ∀ (e : Set S), e ∈ H'''.E ↔ e ∈ H.E ∧ ¬e ⊆ Z₂ ∨ e ∈ H''.E ∧ e ⊆ Z₂) :
    ∀ x ∈ Z₂, x ∈ H'''.U ↔ x ∈ H''.U := by
  subst Z₂
  intro x hxZ₂
  rw [mem_U_iff_mem_V_or_mem_E H''' x, mem_U_iff_mem_V_or_mem_E H'' x]
  constructor
  · rintro (hxV''' | ⟨e, he''', hxe⟩)
    · exact Or.inl (((hH'''_V x).mp hxV''').resolve_left (fun h => h.2 hxZ₂) |>.1)
    · rcases (hH'''_E e).mp he''' with ⟨heH, hnotZ₂⟩ | ⟨heH'', _⟩
      · exact (Set.disjoint_left.mp (hH_edge_disj_Z₂ e heH hnotZ₂) hxe hxZ₂).elim
      · exact Or.inr ⟨e, heH'', hxe⟩
  · rintro (hxVH'' | ⟨e, heH'', hxe⟩)
    · exact Or.inl ((hH'''_V x).mpr (Or.inr ⟨hxVH'', hxZ₂⟩))
    · rcases hRearr₂.atomZone_dichotomy.2.2.2.2.2 e heH'' with hsub₂ | ⟨hdisj₂, _⟩
      · exact Or.inr ⟨e, (hH'''_E e).mpr (Or.inr ⟨heH'', hsub₂⟩), hxe⟩
      · exact (Set.disjoint_left.mp hdisj₂ hxe hxZ₂).elim

private theorem outside_outer_zone_union_agrees_with_replacement
    {α : Type u}
    {β : Type v}
    {S : Type w}
    [TopologicalSpace S]
    {G : Graph α β}
    {H : Drawing S}
    {H'' : Drawing S}
    {η'' : SpanEmbedding H'' G}
    (Z₁ : Set S)
    (Z₂ : Set S)
    (H''' : Drawing S)
    (hH'''_V : ∀ (v : S), v ∈ H'''.V ↔ v ∈ H.V ∧ v ∉ Z₂ ∨ v ∈ H''.V ∧ v ∈ Z₂)
    (hH'''_E : ∀ (e : Set S), e ∈ H'''.E ↔ e ∈ H.E ∧ ¬e ⊆ Z₂ ∨ e ∈ H''.E ∧ e ⊆ Z₂)
    (vMap''' : S → α)
    (eMap''' : Set S → β)
    (hV_notZ₁ : ∀ v ∉ Z₁, (v ∈ H'''.V ↔ v ∈ H''.V) ∧ (v ∈ H'''.V → vMap''' v = η''.vMap v))
    (hE_notZ₁ : ∀ (e : Set S), ¬e ⊆ Z₁ → (e ∈ H'''.E ↔ e ∈ H''.E) ∧ (e ∈ H'''.E → eMap''' e =
      η''.eMap e))
    (hU'''_iff_notZ₂ : ∀ x ∉ Z₂, x ∈ H'''.U ↔ x ∈ H.U)
    (hU'''_iff_Z₂ : ∀ x ∈ Z₂, x ∈ H'''.U ↔ x ∈ H''.U) :
    ∀ x ∉ Z₁, x ∈ H'''.U ↔ x ∈ H''.U := by
  intro x hx_notZ₁
  by_cases hxZ₂ : x ∈ Z₂
  · exact hU'''_iff_Z₂ x hxZ₂
  · rw [hU'''_iff_notZ₂ x hxZ₂, mem_U_iff_mem_V_or_mem_E H x, mem_U_iff_mem_V_or_mem_E H'' x]
    constructor
    · rintro (hxVH | ⟨e, heH, hxe⟩)
      · have hxVH'' : x ∈ H''.V := (hV_notZ₁ x hx_notZ₁).1.mp ((hH'''_V x).mpr
          (Or.inl ⟨hxVH, hxZ₂⟩))
        exact Or.inl hxVH''
      · have henot₁ : ¬ e ⊆ Z₁ := fun hsub => hx_notZ₁ (hsub hxe)
        have henot₂ : ¬ e ⊆ Z₂ := fun hsub => hxZ₂ (hsub hxe)
        have heH'' : e ∈ H''.E := (hE_notZ₁ e henot₁).1.mp ((hH'''_E e).mpr (Or.inl ⟨heH, henot₂⟩))
        exact Or.inr ⟨e, heH'', hxe⟩
    · rintro (hxVH'' | ⟨e, heH'', hxe⟩)
      · have hxV''' : x ∈ H'''.V := (hV_notZ₁ x hx_notZ₁).1.mpr hxVH''
        exact Or.inl (((hH'''_V x).mp hxV''').resolve_right (fun h => hxZ₂ h.2) |>.1)
      · have henot₁ : ¬ e ⊆ Z₁ := fun hsub => hx_notZ₁ (hsub hxe)
        have he''' : e ∈ H'''.E := (hE_notZ₁ e henot₁).1.mpr heH''
        exact Or.inr ⟨e, ((hH'''_E e).mp he''').resolve_right (fun h => hxZ₂ (h.2 hxe)) |>.1, hxe⟩

private theorem combined_drawing_edge_cases
    {α : Type u}
    {β : Type v}
    {S : Type w}
    [TopologicalSpace S]
    {G : Graph α β}
    {H : Drawing S}
    {H'' : Drawing S}
    {η'' : SpanEmbedding H'' G}
    (Z₁ : Set S)
    (Z₂ : Set S)
    (hDisj_cl : Disjoint (closure Z₁) (closure Z₂))
    (hH_edge_cl_disj_Z₁ : ∀ e ∈ H.E, ¬Disjoint (closure e) Z₂ → Disjoint (closure e) Z₁)
    (H''' : Drawing S)
    (hH'''_E : ∀ (e : Set S), e ∈ H'''.E ↔ e ∈ H.E ∧ ¬e ⊆ Z₂ ∨ e ∈ H''.E ∧ e ⊆ Z₂)
    (eMap''' : Set S → β)
    (heMap'''_Z₂ : ∀ e ⊆ Z₂, eMap''' e = η''.eMap e)
    (hE_notZ₁ : ∀ (e : Set S), ¬e ⊆ Z₁ → (e ∈ H'''.E ↔ e ∈ H''.E) ∧ (e ∈ H'''.E → eMap''' e =
      η''.eMap e)) :
    ∀ e ∈ H'''.E, e ∈ H.E ∧ ¬e ⊆ Z₂ ∧ Disjoint (closure e) Z₂ ∨ e ∈ H''.E ∧ Disjoint (closure e)
      Z₁ ∧ eMap''' e = η''.eMap e := by
  intro e he
  rcases (hH'''_E e).mp he with ⟨heH, hnotZ₂⟩ | ⟨heH'', heZ₂⟩
  · by_cases hdisj : Disjoint (closure e) Z₂
    · exact Or.inl ⟨heH, hnotZ₂, hdisj⟩
    · right
      have hdisj₁ : Disjoint (closure e) Z₁ := hH_edge_cl_disj_Z₁ e heH hdisj
      have he_notZ₁ : ¬ e ⊆ Z₁ := by
        obtain ⟨x, hxe⟩ := heH.1
        exact fun hsub => Set.disjoint_left.mp hdisj₁ (subset_closure hxe) (hsub hxe)
      exact ⟨(hE_notZ₁ e he_notZ₁).1.mp he, hdisj₁, (hE_notZ₁ e he_notZ₁).2 he⟩
  · right
    exact ⟨heH'', hDisj_cl.symm.mono (closure_mono heZ₂) subset_closure, heMap'''_Z₂ e heZ₂⟩

private theorem combined_image_graph_edges
    {α : Type u}
    {β : Type v}
    {S : Type w}
    [TopologicalSpace S]
    {G : Graph α β}
    (H''' : Drawing S)
    (vMap''' : S → α)
    (eMap''' : Set S → β)
    (hE_inc_G : ∀ e ∈ H'''.E, eMap''' e ∈ E(G) ∧ (∀ (x y : α), G.IsLink (eMap''' e) x y → x ∈
      vMap''' '' H'''.V ∧ y ∈ vMap''' '' H'''.V) ∧ ∀ v ∈ H'''.V, G.Inc (eMap''' e) (vMap''' v) ↔ v
      ∈ closure e) :
    E((G.induce (vMap''' '' H'''.V)).restrict (eMap''' '' H'''.E)) = eMap''' '' H'''.E := by
  apply Subset.antisymm
  · intro b hb
    rw [edge_mem_iff_exists_isLink] at hb
    obtain ⟨x, y, hb, _⟩ := hb
    exact hb
  · rintro b ⟨e, he''', rfl⟩
    obtain ⟨heG, hends, _⟩ := hE_inc_G e he'''
    obtain ⟨x, y, hlinkG⟩ := (G.edge_mem_iff_exists_isLink _).mp heG
    obtain ⟨hx_im, hy_im⟩ := hends x y hlinkG
    rw [edge_mem_iff_exists_isLink]
    exact ⟨x, y, ⟨e, he''', rfl⟩, hlinkG, hx_im, hy_im⟩

private theorem glue_drawings_along_zone
    {S : Type w} [TopologicalSpace S] [T2Space S] (H H'' : Drawing S) (Z₂ : Set S)
    (hH_edge_disj_Z₂ : ∀ e ∈ H.E, ¬ e ⊆ Z₂ → Disjoint e Z₂)
    (V''' : Set S) (hV : V''' = {v ∈ H.V | v ∉ Z₂} ∪ {v ∈ H''.V | v ∈ Z₂})
    (hA₁_ends : ∀ e ∈ H.E, ¬ e ⊆ Z₂ → closure e ∩ H.V ⊆ H.V ∩ V''')
    (hM₂_ends : ∀ e ∈ H''.E, e ⊆ Z₂ → closure e ∩ H''.V ⊆ H''.V ∩ V''') :
    ∃ H''' : Drawing S,
      (∀ v, v ∈ H'''.V ↔ (v ∈ H.V ∧ v ∉ Z₂) ∨ (v ∈ H''.V ∧ v ∈ Z₂)) ∧
      (∀ e, e ∈ H'''.E ↔ (e ∈ H.E ∧ ¬ e ⊆ Z₂) ∨ (e ∈ H''.E ∧ e ⊆ Z₂)) := by
  subst V'''
  let V''' : Set S := {v ∈ H.V | v ∉ Z₂} ∪ {v ∈ H''.V | v ∈ Z₂}
  let A₁ := H.span (H.V ∩ V''') {e ∈ H.E | ¬ e ⊆ Z₂}
  let M₂ := H''.span (H''.V ∩ V''') {e ∈ H''.E | e ⊆ Z₂}
  have hA₁_V : A₁.V = H.V ∩ V''' := by
    rw [Drawing.span_V, Drawing.spanV]
    ext v
    simp only [mem_union, mem_inter_iff, mem_ofPred_eq, mem_iUnion, exists_prop]
    refine ⟨?_, fun ⟨hvH, hvV⟩ => Or.inl ⟨⟨hvH, hvV⟩, hvH⟩⟩
    rintro (⟨⟨hvH, hvV⟩, _⟩ | ⟨e, ⟨⟨heH, hnot⟩, _⟩, hv_cl, hvH⟩)
    · exact ⟨hvH, hvV⟩
    · exact hA₁_ends e heH hnot ⟨hv_cl, hvH⟩
  have hA₁_E : A₁.E = {e ∈ H.E | ¬ e ⊆ Z₂} := by
    rw [Drawing.span_E]
    ext e
    simp only [mem_inter_iff, mem_ofPred_eq, and_iff_left_iff_imp]
    exact And.left
  have hM₂_V : M₂.V = H''.V ∩ V''' := by
    rw [Drawing.span_V, Drawing.spanV]
    ext v
    simp only [mem_union, mem_inter_iff, mem_ofPred_eq, mem_iUnion, exists_prop]
    refine ⟨?_, fun ⟨hvH'', hvV⟩ => Or.inl ⟨⟨hvH'', hvV⟩, hvH''⟩⟩
    rintro (⟨⟨hvH'', hvV⟩, _⟩ | ⟨e, ⟨⟨heH'', hsub⟩, _⟩, hv_cl, hvH''⟩)
    · exact ⟨hvH'', hvV⟩
    · exact hM₂_ends e heH'' hsub ⟨hv_cl, hvH''⟩
  have hM₂_E : M₂.E = {e ∈ H''.E | e ⊆ Z₂} := by
    rw [Drawing.span_E]
    ext e
    simp only [mem_inter_iff, mem_ofPred_eq, and_iff_left_iff_imp]
    exact And.left
  have h1_union : ∀ e₁ ∈ A₁.E, closure e₁ ∩ M₂.V ⊆ A₁.V := by
    exact retained_edges_meet_new_vertices_at_old_ends (S := S) (H := H) (H'' := H'') Z₂
      hH_edge_disj_Z₂ V''' rfl A₁ M₂ hA₁_V hA₁_E hM₂_V
  have h2_union : ∀ e₂ ∈ M₂.E, closure e₂ ∩ A₁.V ⊆ M₂.V := by
    exact inserted_edges_meet_old_vertices_at_new_ends (S := S) (H := H) (H'' := H'') Z₂ V''' rfl
      A₁ M₂ hA₁_V hM₂_V hM₂_E
  have h3_union : ∀ e₁ ∈ A₁.E, ∀ e₂ ∈ M₂.E, closure e₁ ∩ closure e₂ ⊆ A₁.V ∩ M₂.V := by
    exact retained_and_inserted_edge_intersections (S := S) (H := H) (H'' := H'') Z₂
      hH_edge_disj_Z₂ V''' A₁ M₂ hA₁_ends hM₂_ends hA₁_V hA₁_E hM₂_V hM₂_E h1_union h2_union
  refine ⟨unionDrawing A₁ M₂ h1_union h2_union h3_union, fun v => ?_, fun e => ?_⟩
  · change v ∈ A₁.V ∪ M₂.V ↔ v ∈ V'''
    rw [hA₁_V, hM₂_V]
    refine ⟨fun h => h.elim And.right And.right, fun hv => ?_⟩
    rcases hv with ⟨hvH, hvnot⟩ | ⟨hvH'', hvZ₂⟩
    · exact Or.inl ⟨hvH, Or.inl ⟨hvH, hvnot⟩⟩
    · exact Or.inr ⟨hvH'', Or.inr ⟨hvH'', hvZ₂⟩⟩
  · have hEq := unionDrawing_E A₁ M₂ h1_union h2_union h3_union
    rw [hEq, hA₁_E, hM₂_E, mem_union]
    rfl

/-- Construction of the combined drawing `H''' = A₁ ∪ M₂` and its embedding `η''' : SpanEmbedding
H''' G`
in the proof of `(5.2)` (pages 131–132), together with its agreement properties outside `Z₂` (with
`H, η`) and outside `Z₁` (with `H'', η''`). -/
theorem exists_rearranged_H'''_η'''
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {G : Graph α β} {H H' H'' : Drawing S}
    {η : SpanEmbedding H G} {η' : SpanEmbedding H' G} {η'' : SpanEmbedding H'' G}
    {θ_star θ lam lam₁ lam₂ μ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' d'' : Set S → Set S → ℕ} {z₁ z₂ : Set S}
    (hFlat : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (hθ_lt : 4 * lam + 2 < θ)
    (hlam₁ : 4 ≤ lam₁) (hlam₂ : 4 ≤ lam₂)
    (hlam : 6 * lam₁ + 5 * lam₂ + 3 * μ + 4 ≤ lam)
    (hRearr₁ : IsRearrangedWithin G H H' η η' θ_star θ lam₁ T_star T T' d d' z₁)
    (hRearr₂ : IsRearrangedWithin G H' H'' η' η'' θ_star (θ - (4 * lam₁ + 2)) lam₂ T_star T' T'' d'
      d'' z₂)
    (hStep : IsMuSteppedSpan G H'' η'' d'' μ) :
    let Z₁ := atomZone H d z₁ lam₁
    let Z₂ := atomZone H' d' z₂ lam₂
    ∃ (H''' : Drawing S) (η''' : SpanEmbedding H''' G),
      (∀ v, v ∈ H'''.V ↔ (v ∈ H.V ∧ v ∉ Z₂) ∨ (v ∈ H''.V ∧ v ∈ Z₂)) ∧
      (∀ e, e ∈ H'''.E ↔ (e ∈ H.E ∧ ¬ e ⊆ Z₂) ∨ (e ∈ H''.E ∧ e ⊆ Z₂)) ∧
      (∀ v, v ∉ Z₂ → (v ∈ H'''.V ↔ v ∈ H.V) ∧ η'''.vMap v = η.vMap v) ∧
      (∀ e, ¬ e ⊆ Z₂ → (e ∈ H'''.E ↔ e ∈ H.E) ∧ η'''.eMap e = η.eMap e) ∧
      (∀ x, x ∉ Z₂ → (x ∈ H'''.U ↔ x ∈ H.U)) ∧
      (∀ v, v ∉ Z₁ → (v ∈ H'''.V ↔ v ∈ H''.V) ∧ (v ∈ H'''.V → η'''.vMap v = η''.vMap v)) ∧
      (∀ e, ¬ e ⊆ Z₁ → (e ∈ H'''.E ↔ e ∈ H''.E) ∧ (e ∈ H'''.E → η'''.eMap e = η''.eMap e)) ∧
      (∀ x, x ∉ Z₁ → (x ∈ H'''.U ↔ x ∈ H''.U)) ∧
      (∀ a ∈ H.A, Disjoint a Z₂ → a ∈ H'''.A) ∧
      (∀ a ∈ H.A, a ∉ H'''.A → a ⊆ Z₂) ∧
      (∀ a ∈ H'''.A, a ∉ H.A → a ⊆ Z₂) ∧
      (∀ a ∈ H'''.A, a ∉ H''.A → a ⊆ Z₁) := by
  intro Z₁ Z₂
  have hS : IsClosedSurface S :=
    ⟨hFlat.isSpan.isSurface.1, hFlat.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hFlat.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hFlat.isSpan.isConnected
  have hMetric : HasTangleMetric H θ T d := hRearr₁.isCompression.hasMetric
  obtain ⟨_, hd_refl, _⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
  obtain ⟨τ, hτ_z₂⟩ := atom_nonempty hRearr₂.z_mem
  obtain ⟨z₃, hz₃, hτ_z₃⟩ := exists_atom_of_point H τ
  obtain ⟨_, _, _, hClaim6, hClosureDist, hDisj_cl, _⟩ :=
    lemma_5_2_claims_3_to_6 hFlat hθ_lt hlam₁ hlam₂ hlam hRearr₁ hRearr₂ hStep hτ_z₂ hz₃ hτ_z₃
  have hDisj_Z : Disjoint Z₁ Z₂ :=
    hDisj_cl.mono subset_closure subset_closure
  -- Any edge `e ∈ H.E` with `¬ e ⊆ Z₂` has `Disjoint e Z₂`, and if `¬ Disjoint (closure e) Z₂`
  -- then `Disjoint (closure e) Z₁`
  have hH_edge_disj_Z₂ : ∀ e ∈ H.E, ¬ e ⊆ Z₂ → Disjoint e Z₂ := by
    intro e he hnot
    rcases hRearr₁.atomZone_dichotomy.2.2.2.2.1 e he with ⟨_, hsub₁⟩ | ⟨_, _, heH', _⟩
    · exact hDisj_Z.mono hsub₁ Subset.rfl
    · rcases hRearr₂.atomZone_dichotomy.2.2.2.2.1 e heH' with ⟨_, hsub₂⟩ | ⟨_, hdisj₂, _, _⟩
      · exact (hnot hsub₂).elim
      · exact hdisj₂
  have hH_edge_cl_disj_Z₁ : ∀ e ∈ H.E, ¬ Disjoint (closure e) Z₂ → Disjoint (closure e) Z₁ := by
    intro e he hnot_disj
    obtain ⟨p, hp_cl, hpZ₂⟩ := Set.not_disjoint_iff.mp hnot_disj
    refine Set.disjoint_left.mpr fun q hq_cl hqZ₁ => ?_
    obtain ⟨a_p, ha_p, hp_a⟩ := exists_atom_of_point H p
    obtain ⟨a_q, ha_q, hq_a⟩ := exists_atom_of_point H q
    have heA : e ∈ H.A := Or.inl (Or.inr he)
    have hd_pe : d a_p e ≤ 3 := atom_closure_dist_le_three hS hMetric a_p ha_p e heA ⟨p, hp_a,
      hp_cl⟩
    have hd_qe : d a_q e ≤ 3 := atom_closure_dist_le_three hS hMetric a_q ha_q e heA ⟨q, hq_a,
      hq_cl⟩
    obtain ⟨_, _, _, hd_symm, hd_tri, _⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
    have hsym := hd_symm e heA a_p ha_p
    have htri := hd_tri a_q ha_q e heA a_p ha_p
    have h6 := hClaim6 q hqZ₁ p hpZ₂
    rw [pointDist_eq_of_mem_atom ha_q ha_p hq_a hp_a] at h6
    omega
  let V''' : Set S := {v ∈ H.V | v ∉ Z₂} ∪ {v ∈ H''.V | v ∈ Z₂}
  have hA₁_ends : ∀ e ∈ H.E, ¬ e ⊆ Z₂ → closure e ∩ H.V ⊆ H.V ∩ V''' := by
    exact retained_edges_preserve_outer_endpoints (α := α) (β := β) (S := S) (G := G) (H := H) (H'
      := H') (H'' := H'') (η := η) (η' := η') (η'' := η'') (θ_star := θ_star) (θ := θ) (lam₁ :=
      lam₁) (lam₂ := lam₂) (T_star := T_star) (T := T) (T' := T') (T'' := T'') (d := d) (d' := d')
      (d'' := d'') (z₁ := z₁) (z₂ := z₂) hRearr₁ hRearr₂ Z₁ rfl Z₂ rfl hH_edge_cl_disj_Z₁ V''' rfl
  have hM₂_ends : ∀ e ∈ H''.E, e ⊆ Z₂ → closure e ∩ H''.V ⊆ H''.V ∩ V''' := by
    exact inserted_edges_preserve_inner_endpoints (α := α) (β := β) (S := S) (G := G) (H := H) (H'
      := H') (H'' := H'') (η := η) (η' := η') (η'' := η'') (θ_star := θ_star) (θ := θ) (lam₁ :=
      lam₁) (lam₂ := lam₂) (T_star := T_star) (T := T) (T' := T') (T'' := T'') (d := d) (d' := d')
      (d'' := d'') (z₁ := z₁) (z₂ := z₂) hRearr₁ hRearr₂ Z₂ rfl hDisj_cl V''' rfl
  obtain ⟨H''', hH'''_V, hH'''_E⟩ :=
    glue_drawings_along_zone H H'' Z₂ hH_edge_disj_Z₂ V''' rfl hA₁_ends hM₂_ends
  -- Define `vMap'''` and `eMap'''` as opaque witnesses
  obtain ⟨vMap''', hvMap'''_Z₂, hvMap'''_notZ₂⟩ :
      ∃ vMap''' : S → α,
        (∀ v, v ∈ Z₂ → vMap''' v = η''.vMap v) ∧
        (∀ v, v ∉ Z₂ → vMap''' v = η.vMap v) := by
    classical
    exact ⟨fun v => if v ∈ Z₂ then η''.vMap v else η.vMap v,
      fun _ hv => ite_eq_left_iff.mpr fun h => (h hv).elim,
      fun _ hv => ite_eq_right_iff.mpr fun h => (hv h).elim⟩
  obtain ⟨eMap''', heMap'''_Z₂, heMap'''_notZ₂⟩ :
      ∃ eMap''' : Set S → β,
        (∀ e, e ⊆ Z₂ → eMap''' e = η''.eMap e) ∧
        (∀ e, ¬ e ⊆ Z₂ → eMap''' e = η.eMap e) := by
    classical
    exact ⟨fun e => if e ⊆ Z₂ then η''.eMap e else η.eMap e,
      fun _ he => ite_eq_left_iff.mpr fun h => (h he).elim,
      fun _ he => ite_eq_right_iff.mpr fun h => (he h).elim⟩
  -- Agreement with `H'', η''` outside `Z₁`
  have hV_notZ₁ : ∀ v, v ∉ Z₁ → (v ∈ H'''.V ↔ v ∈ H''.V) ∧ (v ∈ H'''.V → vMap''' v = η''.vMap v)
    := by
    exact outer_vertices_follow_second_rearrangement (α := α) (β := β) (S := S) (G := G) (H := H)
      (H' := H') (H'' := H'') (η := η) (η' := η') (η'' := η'') (θ_star := θ_star) (θ := θ) (lam₁
      := lam₁) (lam₂ := lam₂) (T_star := T_star) (T := T) (T' := T') (T'' := T'') (d := d) (d' :=
      d') (d'' := d'') (z₁ := z₁) (z₂ := z₂) hRearr₁ hRearr₂ Z₁ rfl Z₂ rfl H''' hH'''_V vMap'''
      hvMap'''_Z₂ hvMap'''_notZ₂
  have hE_notZ₁ : ∀ e, ¬ e ⊆ Z₁ → (e ∈ H'''.E ↔ e ∈ H''.E) ∧ (e ∈ H'''.E → eMap''' e = η''.eMap e)
    := by
    exact outer_edges_follow_second_rearrangement (α := α) (β := β) (S := S) (G := G) (H := H) (H'
      := H') (H'' := H'') (η := η) (η' := η') (η'' := η'') (θ_star := θ_star) (θ := θ) (lam₁ :=
      lam₁) (lam₂ := lam₂) (T_star := T_star) (T := T) (T' := T') (T'' := T'') (d := d) (d' := d')
      (d'' := d'') (z₁ := z₁) (z₂ := z₂) hRearr₁ hRearr₂ Z₁ rfl Z₂ rfl H''' hH'''_E eMap'''
      heMap'''_Z₂ heMap'''_notZ₂
  -- Injectivity of `vMap'''` on `H'''.V`
  have hinj_v : InjOn vMap''' H'''.V := by
    exact combined_drawing_vertex_map_is_injective (α := α) (β := β) (S := S) (G := G) (H := H)
      (H' := H') (H'' := H'') (η := η) (η' := η') (η'' := η'') (θ_star := θ_star) (θ := θ) (lam :=
      lam) (lam₁ := lam₁) (lam₂ := lam₂) (μ := μ) (T_star := T_star) (T := T) (T' := T') (T'' :=
      T'') (d := d) (d' := d') (d'' := d'') (z₁ := z₁) (z₂ := z₂) hFlat hθ_lt hlam₁ hlam₂ hlam
      hRearr₁ hRearr₂ hStep Z₁ rfl Z₂ rfl hd_refl z₃ H''' hH'''_V vMap''' hvMap'''_Z₂
      hvMap'''_notZ₂ hV_notZ₁
  -- Every `e ∈ H'''.E` either has `e ∈ H.E ∧ ¬ e ⊆ Z₂ ∧ Disjoint (closure e) Z₂` or `e ∈ H''.E ∧
  -- Disjoint (closure e) Z₁`
  have hE'''_cases : ∀ e ∈ H'''.E,
      (e ∈ H.E ∧ ¬ e ⊆ Z₂ ∧ Disjoint (closure e) Z₂) ∨
      (e ∈ H''.E ∧ Disjoint (closure e) Z₁ ∧ eMap''' e = η''.eMap e) := by
    exact combined_drawing_edge_cases Z₁ Z₂ hDisj_cl hH_edge_cl_disj_Z₁ H''' hH'''_E eMap'''
      heMap'''_Z₂ hE_notZ₁
  -- Incidence characterization in `G` for `e ∈ H'''.E`
  have hE_inc_G : ∀ e ∈ H'''.E, eMap''' e ∈ E(G) ∧
      (∀ x y, G.IsLink (eMap''' e) x y → x ∈ vMap''' '' H'''.V ∧ y ∈ vMap''' '' H'''.V) ∧
      (∀ v ∈ H'''.V, G.Inc (eMap''' e) (vMap''' v) ↔ v ∈ closure e) := by
    exact combined_drawing_incidence_matches_graph (α := α) (β := β) (S := S) (G := G) (H := H)
      (H'' := H'') (η := η) (η'' := η'') Z₁ Z₂ H''' hH'''_V vMap''' hvMap'''_notZ₂ eMap'''
      heMap'''_notZ₂ hV_notZ₁ hinj_v hE'''_cases
  -- Injectivity of `eMap'''` on `H'''.E`
  have hinj_e : InjOn eMap''' H'''.E := by
    exact combined_drawing_edge_map_is_injective (α := α) (β := β) (S := S) (G := G) (H := H) (H'
      := H') (H'' := H'') (η := η) (η' := η') (η'' := η'') (θ_star := θ_star) (θ := θ) (lam₁
        := lam₁) (lam₂ := lam₂) (T_star := T_star) (T := T) (T' := T') (d := d)
      (d' := d') (z₁ := z₁) (z₂ := z₂) hlam₁ hRearr₁ Z₁ rfl Z₂ rfl hS hMetric z₃ hDisj_cl H'''
      hH'''_V vMap''' eMap''' heMap'''_notZ₂ hE_notZ₁ hE'''_cases hE_inc_G
  -- Construct `η''' : SpanEmbedding H''' G`
  let imageGraph''' := (G.induce (vMap''' '' H'''.V)).restrict (eMap''' '' H'''.E)
  have hV_sub_G : vMap''' '' H'''.V ⊆ V(G) := by
    rintro _ ⟨v, hv''', rfl⟩
    rcases (hH'''_V v).mp hv''' with ⟨hvH, hvnot⟩ | ⟨hvH'', hvZ₂⟩
    · rw [hvMap'''_notZ₂ v hvnot]
      exact η.imageGraph_le.1 (η.bijOn_v.mapsTo hvH)
    · rw [hvMap'''_Z₂ v hvZ₂]
      exact η''.imageGraph_le.1 (η''.bijOn_v.mapsTo hvH'')
  have hE_im_eq : E(imageGraph''') = eMap''' '' H'''.E := by
    exact combined_image_graph_edges (α := α) (β := β) (S := S) (G := G) H''' vMap''' eMap'''
      hE_inc_G
  let η''' : SpanEmbedding H''' G := {
    imageGraph := imageGraph'''
    vMap := vMap'''
    eMap := eMap'''
    imageGraph_le := Graph.restrict_le.trans (Graph.induce_le hV_sub_G)
    bijOn_v := by
      have hV_eq : V(imageGraph''') = vMap''' '' H'''.V := by simp [imageGraph''']
      rw [hV_eq]
      exact hinj_v.bijOn_image
    bijOn_e := by
      rw [hE_im_eq]
      exact hinj_e.bijOn_image
    inc_iff := fun e he''' v hv''' => by
      rw [← (hE_inc_G e he''').2.2 v hv''']
      constructor
      · rintro ⟨w, _, hlinkG, _, _⟩
        exact ⟨w, hlinkG⟩
      · rintro ⟨w, hlinkG⟩
        obtain ⟨_, hw_im⟩ := (hE_inc_G e he''').2.1 (vMap''' v) w hlinkG
        exact ⟨w, ⟨e, he''', rfl⟩, hlinkG, ⟨v, hv''', rfl⟩, hw_im⟩
  }
  -- Atom agreement properties
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hU'''_iff_notZ₂ : ∀ x, x ∉ Z₂ → (x ∈ H'''.U ↔ x ∈ H.U) := by
    exact outside_inner_zone_union_agrees_with_original (S := S) (H := H) (H'' := H'') Z₂ H'''
      hH'''_V hH'''_E
  have hU'''_iff_Z₂ : ∀ x, x ∈ Z₂ → (x ∈ H'''.U ↔ x ∈ H''.U) := by
    exact inside_inner_zone_union_agrees_with_replacement (α := α) (β := β) (S := S) (G := G) (H
      := H) (H' := H') (H'' := H'') (η' := η') (η'' := η'') (θ_star := θ_star) (θ := θ) (lam₁ :=
      lam₁) (lam₂ := lam₂) (T_star := T_star) (T' := T') (T'' := T'') (d' := d') (d'' := d'') (z₂
      := z₂) hRearr₂ Z₂ rfl hH_edge_disj_Z₂ H''' hH'''_V hH'''_E
  have hU'''_iff_notZ₁ : ∀ x, x ∉ Z₁ → (x ∈ H'''.U ↔ x ∈ H''.U) := by
    exact outside_outer_zone_union_agrees_with_replacement (α := α) (β := β) (S := S) (G := G) (H
      := H) (H'' := H'') (η'' := η'') Z₁ Z₂ H''' hH'''_V hH'''_E vMap''' eMap''' hV_notZ₁ hE_notZ₁
      hU'''_iff_notZ₂ hU'''_iff_Z₂
  have hH_atom_disj_Z₂ : ∀ a ∈ H.A, Disjoint a Z₂ → a ∈ H'''.A := by
    exact first_drawing_atoms_off_second_zone_survive (α := α) (β := β) (S := S) (G := G) (H := H)
      (H' := H') (H'' := H'') (η := η) (η' := η') (η'' := η'') (θ_star := θ_star) (θ := θ) (lam₁
      := lam₁) (lam₂ := lam₂) (T_star := T_star) (T := T) (T' := T') (T'' := T'') (d := d) (d' :=
      d') (d'' := d'') (z₁ := z₁) (z₂ := z₂) hRearr₁ hRearr₂ Z₂ rfl hDisj_cl H''' hH'''_V hH'''_E
      this hU'''_iff_notZ₂ hU'''_iff_Z₂
  have hH_atom_compl : ∀ a ∈ H.A, a ∉ H'''.A → a ⊆ Z₂ := by
    intro a ha hnot
    rcases hRearr₁.atomZone_dichotomy.1 a ha with ⟨_, hsub₁⟩ | ⟨_, _, haH'⟩
    · exact (hnot (hH_atom_disj_Z₂ a ha (hDisj_Z.mono hsub₁ Subset.rfl))).elim
    · rcases hRearr₂.atomZone_dichotomy.1 a haH' with ⟨_, hsub₂⟩ | ⟨_, hdisj₂, _⟩
      · exact hsub₂
      · exact (hnot (hH_atom_disj_Z₂ a ha hdisj₂)).elim
  have hH''_atom_disj_Z₁ : ∀ a ∈ H''.A, Disjoint a Z₁ → a ∈ H'''.A := by
    exact second_drawing_atoms_off_first_zone_survive (α := α) (β := β) (S := S) (G := G) (H := H)
      (H' := H') (H'' := H'') (η := η) (η' := η') (η'' := η'') (θ_star := θ_star) (θ := θ) (lam₁
      := lam₁) (lam₂ := lam₂) (T_star := T_star) (T := T) (T' := T') (T'' := T'') (d := d) (d' :=
      d') (d'' := d'') (z₁ := z₁) (z₂ := z₂) hRearr₁ hRearr₂ Z₁ rfl Z₂ rfl hDisj_cl hDisj_Z H'''
      vMap''' eMap''' hV_notZ₁ hE_notZ₁ this hU'''_iff_notZ₂ hU'''_iff_notZ₁
  have hH''_atom_compl : ∀ a ∈ H''.A, a ∉ H'''.A → a ⊆ Z₁ := by
    intro a ha hnot
    rcases hRearr₂.atomZone_dichotomy.2.1 a ha with hsub₂ | ⟨_, haH', _⟩
    · exact (hnot (hH''_atom_disj_Z₁ a ha (hDisj_Z.symm.mono hsub₂ Subset.rfl))).elim
    · rcases hRearr₁.atomZone_dichotomy.2.1 a haH' with hsub₁ | ⟨hdisj₁, _⟩
      · exact hsub₁
      · exact (hnot (hH''_atom_disj_Z₁ a ha hdisj₁)).elim
  exact ⟨H''', η''', hH'''_V, hH'''_E,
    fun v hvnot => ⟨⟨fun h => ((hH'''_V v).mp h).resolve_right (fun h2 => hvnot h2.2) |>.1,
      fun h => (hH'''_V v).mpr (Or.inl ⟨h, hvnot⟩)⟩, hvMap'''_notZ₂ v hvnot⟩,
    fun e henot => ⟨⟨fun h => ((hH'''_E e).mp h).resolve_right (fun h2 => henot h2.2) |>.1,
      fun h => (hH'''_E e).mpr (Or.inl ⟨h, henot⟩)⟩, heMap'''_notZ₂ e henot⟩,
    hU'''_iff_notZ₂,
    hV_notZ₁, hE_notZ₁, hU'''_iff_notZ₁,
    hH_atom_disj_Z₂,
    hH_atom_compl,
    atom_subset_of_compl_subset hH_atom_compl,
    atom_subset_of_compl_subset hH''_atom_compl⟩

/-- If `Δ` is a dial for `F, Γ₁` and `Γ₁, Γ₂` have the same vertices, edges, and `U` inside `Δ`,
then `Δ` is a dial for `F, Γ₂`. -/
theorem isDial_congr_of_subset {S : Type w} [TopologicalSpace S] [T2Space S]
    {Γ₁ Γ₂ : Drawing S} {F Δ : Set S} (hDial : IsDial Γ₁ F Δ)
    (hV : ∀ v ∈ Δ, v ∈ Γ₁.V ↔ v ∈ Γ₂.V)
    (hE₁ : ∀ e ∈ Γ₁.E, e ⊆ Δ → e ∈ Γ₂.E)
    (hE₂ : ∀ e ∈ Γ₂.E, e ⊆ Δ → e ∈ Γ₁.E)
    (hU : ∀ x ∈ Δ, x ∈ Γ₁.U ↔ x ∈ Γ₂.U) :
    IsDial Γ₂ F Δ := by
  have hF_sub : F ⊆ Δ := by
    rw [← hDial.2.1]
    exact inter_subset_left.trans hDial.1.isClosed.closure_subset
  have hFV_eq : F ∩ Γ₁.V = F ∩ Γ₂.V := by
    ext x
    exact ⟨fun ⟨hxF, hxV⟩ => ⟨hxF, (hV x (hF_sub hxF)).mp hxV⟩,
      fun ⟨hxF, hxV⟩ => ⟨hxF, (hV x (hF_sub hxF)).mpr hxV⟩⟩
  have hΔU_eq : Δ ∩ Γ₁.U = Δ ∩ Γ₂.U := by
    ext x
    exact ⟨fun ⟨hxΔ, hxU⟩ => ⟨hxΔ, (hU x hxΔ).mp hxU⟩,
      fun ⟨hxΔ, hxU⟩ => ⟨hxΔ, (hU x hxΔ).mpr hxU⟩⟩
  have hinter_eq : Γ₁.interSet Δ = Γ₂.interSet Δ := by
    apply Drawing.ext_of_V_E
    · rw [Drawing.interSet, Drawing.interSet, Drawing.span_V, Drawing.span_V,
        Drawing.spanV, Drawing.spanV]
      ext x
      simp only [mem_union, mem_inter_iff, mem_iUnion₂, mem_ofPred_eq]
      constructor
      · rintro (⟨⟨hxV, hxΔ⟩, _⟩ | ⟨e, ⟨⟨heE, heΔ⟩, _⟩, hxcl, hxV⟩)
        · exact Or.inl ⟨⟨(hV x hxΔ).mp hxV, hxΔ⟩, (hV x hxΔ).mp hxV⟩
        · have hxΔ : x ∈ Δ := hDial.1.isClosed.closure_subset_iff.mpr heΔ hxcl
          exact Or.inl ⟨⟨(hV x hxΔ).mp hxV, hxΔ⟩, (hV x hxΔ).mp hxV⟩
      · rintro (⟨⟨hxV, hxΔ⟩, _⟩ | ⟨e, ⟨⟨heE, heΔ⟩, _⟩, hxcl, hxV⟩)
        · exact Or.inl ⟨⟨(hV x hxΔ).mpr hxV, hxΔ⟩, (hV x hxΔ).mpr hxV⟩
        · have hxΔ : x ∈ Δ := hDial.1.isClosed.closure_subset_iff.mpr heΔ hxcl
          exact Or.inl ⟨⟨(hV x hxΔ).mpr hxV, hxΔ⟩, (hV x hxΔ).mpr hxV⟩
    · rw [Drawing.interSet, Drawing.interSet, Drawing.span_E, Drawing.span_E]
      ext e
      simp only [mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun ⟨⟨heE, heΔ⟩, _⟩ => ⟨⟨hE₁ e heE heΔ, heΔ⟩, hE₁ e heE heΔ⟩,
        fun ⟨⟨heE, heΔ⟩, _⟩ => ⟨⟨hE₂ e heE heΔ, heΔ⟩, hE₂ e heE heΔ⟩⟩
  refine ⟨hDial.1, hDial.2.1, ?_⟩
  rw [← hΔU_eq, ← hFV_eq, ← hinter_eq]
  exact hDial.2.2

/-- If `Δ` is a dial for `F, Γ`, `W` is preconnected, and `Disjoint F W`, then `W ⊆ Δ` or
`Disjoint W Δ`. -/
theorem subset_or_disjoint_of_isDial {S : Type w} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {F Δ W : Set S} (hDial : IsDial Γ F Δ)
    (hW : IsPreconnected W) (hdisj : Disjoint F W) :
    W ⊆ Δ ∨ Disjoint W Δ := by
  by_cases hsub : W ⊆ Δ
  · exact Or.inl hsub
  · right
    refine Set.disjoint_left.mpr fun x hxW hxΔ => ?_
    obtain ⟨y, hyW, hy_notΔ⟩ := Set.not_subset.mp hsub
    have hcov : W ⊆ (closure (univ \ Δ))ᶜ ∪ Δᶜ := by
      intro z hzW
      by_cases hzΔ : z ∈ Δ
      · left
        intro hz_cl
        have hz_bd : z ∈ subBd Δ := ⟨subset_closure hzΔ, hz_cl⟩
        exact Set.disjoint_left.mp hdisj (hDial.2.1 ▸ hz_bd) hzW
      · exact Or.inr hzΔ
    have hx_U₁ : x ∈ (closure (univ \ Δ))ᶜ :=
      (hcov hxW).resolve_right (not_not.mpr hxΔ)
    obtain ⟨z, _, hz₁, hz₂⟩ :=
      hW (closure (univ \ Δ))ᶜ Δᶜ isClosed_closure.isOpen_compl hDial.1.isClosed.isOpen_compl
        hcov ⟨x, hxW, hx_U₁⟩ ⟨y, hyW, hy_notΔ⟩
    exact hz₁ (subset_closure ⟨mem_univ z, hz₂⟩)

/-- If `F` is preconnected, `x₁ ∈ F ∩ W`, and `x₂ ∈ F \ closure W`, then `(F ∩ frontier
W).Nonempty`. -/
theorem nonempty_inter_frontier_of_isPreconnected {S : Type w} [TopologicalSpace S]
    {F W : Set S} (hF : IsPreconnected F) {x₁ x₂ : S}
    (hx₁ : x₁ ∈ F ∩ W) (hx₂ : x₂ ∈ F \ closure W) :
    (F ∩ frontier W).Nonempty := by
  by_contra hEmp
  have hdisj : Disjoint F (frontier W) :=
    disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hEmp)
  have hcov : F ⊆ interior W ∪ (closure W)ᶜ := by
    intro z hzF
    by_cases hz_cl : z ∈ closure W
    · exact Or.inl (by_contra fun hz_int => Set.disjoint_left.mp hdisj hzF ⟨hz_cl, hz_int⟩)
    · exact Or.inr hz_cl
  have hx₁_int : x₁ ∈ interior W :=
    (hcov hx₁.1).resolve_right (not_not.mpr (subset_closure hx₁.2))
  obtain ⟨z, _, hz_int, hz_compl⟩ :=
    hF (interior W) (closure W)ᶜ isOpen_interior isClosed_closure.isOpen_compl
      hcov ⟨x₁, hx₁.1, hx₁_int⟩ ⟨x₂, hx₂.1, hx₂.2⟩
  exact hz_compl (subset_closure (interior_subset hz_int))

private theorem combined_rearrangement_is_rigid
    {α : Type u}
    {β : Type v}
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {G : Graph α β}
    {H : Drawing S}
    {H' : Drawing S}
    {H'' : Drawing S}
    {H''' : Drawing S}
    {η : SpanEmbedding H G}
    {η' : SpanEmbedding H' G}
    {η'' : SpanEmbedding H'' G}
    {θ_star : ℕ}
    {θ : ℕ}
    {lam : ℕ}
    {lam₁ : ℕ}
    {lam₂ : ℕ}
    {μ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {d' : Set S → Set S → ℕ}
    {d'' : Set S → Set S → ℕ}
    {z₁ : Set S}
    {z₂ : Set S}
    (hFlat : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (hθ_lt : 4 * lam + 2 < θ)
    (hlam₁ : 4 ≤ lam₁)
    (hlam₂ : 4 ≤ lam₂)
    (hlam : 6 * lam₁ + 5 * lam₂ + 3 * μ + 4 ≤ lam)
    (hRearr₁ : IsRearrangedWithin G H H' η η' θ_star θ lam₁ T_star T T' d d' z₁)
    (hRearr₂ : IsRearrangedWithin G H' H'' η' η'' θ_star (θ - (4 * lam₁ + 2)) lam₂ T_star T' T''
      d' d'' z₂)
    (hV_notZ₂ : ∀ v ∉ atomZone H' d' z₂ lam₂, v ∈ H'''.V ↔ v ∈ H.V)
    (hE_notZ₂ : ∀ (e : Set S), ¬e ⊆ atomZone H' d' z₂ lam₂ → (e ∈ H'''.E ↔ e ∈ H.E))
    (hU_notZ₂ : ∀ x ∉ atomZone H' d' z₂ lam₂, x ∈ H'''.U ↔ x ∈ H.U)
    (hV_notZ₁ : ∀ v ∉ atomZone H d z₁ lam₁, v ∈ H'''.V ↔ v ∈ H''.V)
    (hE_notZ₁ : ∀ (e : Set S), ¬e ⊆ atomZone H d z₁ lam₁ → (e ∈ H'''.E ↔ e ∈ H''.E))
    (hU_notZ₁ : ∀ x ∉ atomZone H d z₁ lam₁, x ∈ H'''.U ↔ x ∈ H''.U)
    (hS : IsClosedSurface S)
    [hConn : ConnectedSpace S]
    (hMetric : HasTangleMetric H θ T d)
    (hMetric' : HasTangleMetric H' (θ - (4 * lam₁ + 2)) T' d')
    (hd_refl : ∀ a ∈ H.A, d a a = 0)
    (τ : S)
    (hτ_z₂ : τ ∈ z₂)
    (z₃ : Set S)
    (hz₃ : z₃ ∈ H.A)
    (hτ_z₃ : τ ∈ z₃)
    (hCentersFar : lam - lam₁ < d z₁ z₃)
    (σ₁ : S)
    (hσ₁_z₁ : σ₁ ∈ z₁)
    (hσ₁_Z₁ : σ₁ ∈ (atomZone H d z₁ lam₁))
    (hZ₁_sub_plus : (atomZone H d z₁ lam₁) ⊆ (atomZone H d z₁ (lam₁ + 4)))
    (hZone_disj_Z₂ : ∀ (k : ℕ), k + 3 ≤ lam - 2 * lam₁ - lam₂ - 6 → Disjoint (closure (atomZone H
      d z₁ k)) (closure (atomZone H' d' z₂ lam₂))) :
    IsRigid H''' := by
  let Z₁ := atomZone H d z₁ lam₁
  let Z₂ := atomZone H' d' z₂ lam₂
  let Z₁_plus := atomZone H d z₁ (lam₁ + 4)
  intro F hF hFU hFV
  have hF_pre : IsPreconnected F := by
    obtain ⟨φ⟩ := hF
    have h : F = range (fun z : Circle => (φ z).1) := by
      ext x
      exact ⟨fun hx => ⟨φ.symm ⟨x, hx⟩, by simp⟩, fun ⟨z, hz⟩ => hz ▸ (φ z).2⟩
    rw [h]
    exact isPreconnected_range (continuous_subtype_val.comp φ.continuous)
  -- Show `Disjoint F Z₂` or `Disjoint F Z₁_plus`
  have hDisj_or : Disjoint F Z₂ ∨ Disjoint F Z₁_plus := by
    by_contra hnot
    have hF_Z₂ : ¬ Disjoint F Z₂ := fun h => hnot (Or.inl h)
    have hF_Z₁p : ¬ Disjoint F Z₁_plus := fun h => hnot (Or.inr h)
    obtain ⟨x₂, hx₂F, hx₂Z₂⟩ := Set.not_disjoint_iff.mp hF_Z₂
    obtain ⟨x₁, hx₁F, hx₁Z₁p⟩ := Set.not_disjoint_iff.mp hF_Z₁p
    have hband : ∀ i : Fin 3,
        ∃ p ∈ F ∩ H'''.V, ∃ a_p ∈ H.A, p ∈ a_p ∧
          lam₁ + 4 + 6 * i.1 ≤ d z₁ a_p + 2 ∧ d z₁ a_p ≤ lam₁ + 4 + 6 * i.1 + 3 := by
      intro i
      let k := lam₁ + 4 + 6 * i.1
      let W := atomZone H d z₁ k
      have hsub_W : Z₁_plus ⊆ W := fun x ⟨a, ha, hle, hxa⟩ => ⟨a, ha, by omega, hxa⟩
      have hx₁W : x₁ ∈ F ∩ W := ⟨hx₁F, hsub_W hx₁Z₁p⟩
      have hdisj_W : Disjoint (closure W) (closure Z₂) := by
        have : i.1 < 3 := i.2
        exact hZone_disj_Z₂ k (by omega)
      have hx₂_notW : x₂ ∈ F \ closure W :=
        ⟨hx₂F, fun hx₂cl => Set.disjoint_left.mp hdisj_W hx₂cl (subset_closure hx₂Z₂)⟩
      obtain ⟨p, hpF, hp_fr⟩ := nonempty_inter_frontier_of_isPreconnected hF_pre hx₁W hx₂_notW
      obtain ⟨a_p, ha_p, hp_a⟩ := exists_atom_of_point H p
      obtain ⟨hp_HU, hbounds⟩ :=
        frontier_atomZone_subset_U k hS hConn hMetric hRearr₁.z_mem p hp_fr
      have hp_notZ₂ : p ∉ Z₂ := fun hpZ₂ =>
        Set.disjoint_left.mp hdisj_W hp_fr.1 (subset_closure hpZ₂)
      have hp_U''' : p ∈ H'''.U := (hU_notZ₂ p hp_notZ₂).mpr hp_HU
      exact ⟨p, ⟨hpF, hFU ⟨hpF, hp_U'''⟩⟩, a_p, ha_p, hp_a, hbounds a_p ha_p hp_a⟩
    obtain ⟨p₀, hp₀, a₀, ha₀, hp₀_a₀, _, hd₀_le⟩ := hband 0
    obtain ⟨p₁, hp₁, a₁, ha₁, hp₁_a₁, hd₁_ge, hd₁_le⟩ := hband 1
    obtain ⟨p₂, hp₂, a₂, ha₂, hp₂_a₂, hd₂_ge, _⟩ := hband 2
    have hp₀₁ : p₀ ≠ p₁ := by
      rintro rfl
      have hEq := atom_eq_of_mem ha₀ ha₁ hp₀_a₀ hp₁_a₁
      subst hEq; omega
    have hp₀₂ : p₀ ≠ p₂ := by
      rintro rfl
      have hEq := atom_eq_of_mem ha₀ ha₂ hp₀_a₀ hp₂_a₂
      subst hEq; omega
    have hp₁₂ : p₁ ≠ p₂ := by
      rintro rfl
      have hEq := atom_eq_of_mem ha₁ ha₂ hp₁_a₁ hp₂_a₂
      subst hEq; omega
    have hsub_three : ({p₀, p₁, p₂} : Set S) ⊆ F ∩ H'''.V := by
      rintro x (rfl | rfl | rfl)
      · exact hp₀
      · exact hp₁
      · exact hp₂
    have hfin_FV : (F ∩ H'''.V).Finite := H'''.finite_V.subset inter_subset_right
    have hcard_le := Set.ncard_le_ncard hsub_three hfin_FV
    rw [Set.ncard_insert_of_notMem (by simp [hp₀₁, hp₀₂]),
      Set.ncard_insert_of_notMem (by simp [hp₁₂]), Set.ncard_singleton] at hcard_le
    omega
  rcases hDisj_or with hDisj_FZ₂ | hDisj_FZ₁p
  · -- Case 1: `Disjoint F Z₂`
    have hFU_H : F ∩ H.U ⊆ H.V := by
      rintro x ⟨hxF, hxHU⟩
      have hx_notZ₂ : x ∉ Z₂ := Set.disjoint_left.mp hDisj_FZ₂ hxF
      exact (hV_notZ₂ x hx_notZ₂).mp (hFU ⟨hxF, (hU_notZ₂ x hx_notZ₂).mpr hxHU⟩)
    have hFV_eq : F ∩ H.V = F ∩ H'''.V := by
      ext x
      exact ⟨fun ⟨hxF, hxV⟩ => ⟨hxF, (hV_notZ₂ x (Set.disjoint_left.mp hDisj_FZ₂ hxF)).mpr hxV⟩,
        fun ⟨hxF, hxV⟩ => ⟨hxF, (hV_notZ₂ x (Set.disjoint_left.mp hDisj_FZ₂ hxF)).mp hxV⟩⟩
    obtain ⟨Δ, hDial⟩ := hFlat.isSpan.isRigid F hF hFU_H (hFV_eq ▸ hFV)
    have hZ₂_pre : IsPreconnected Z₂ :=
      isPreconnected_atomZone hS hConn hMetric' hRearr₂.z_mem (by omega)
    have hDisj_Z₂_Δ : Disjoint Z₂ Δ := by
      rcases subset_or_disjoint_of_isDial hDial hZ₂_pre hDisj_FZ₂ with hsub_Z₂ | hdisj
      · exfalso
        obtain ⟨_, _, _, hd_symm, hd_tri, _⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
        have hd_inc := atom_closure_dist_le_three hS hMetric
        have hd'_inc := atom_closure_dist_le_three hS hMetric'
        obtain ⟨r, hrH, hτ_r⟩ := exists_region_closure_mem_of_closedSurface hS H τ
        have hrA : r ∈ H.A := Or.inr hrH
        have hdr₃ : d z₃ r ≤ 3 := hd_inc z₃ hz₃ r hrA ⟨τ, hτ_z₃, hτ_r⟩
        have htri := hd_tri z₁ hRearr₁.z_mem r hrA z₃ hz₃
        have hsymm : d r z₃ = d z₃ r := hd_symm r hrA z₃ hz₃
        have hrH' : r ∈ H'.A := hRearr₁.atom_mem r hrA (by omega)
        have hdr' : d' z₂ r ≤ 3 := hd'_inc z₂ hRearr₂.z_mem r hrH' ⟨τ, hτ_z₂, hτ_r⟩
        have hr_sub_Z₂ : r ⊆ Z₂ := fun y hy => ⟨r, hrH', by omega, hy⟩
        have hcl_r_sub_Δ : closure r ⊆ Δ :=
          hDial.1.isClosed.closure_subset_iff.mpr (hr_sub_Z₂.trans hsub_Z₂)
        exact not_closure_region_subset_of_isDial hS hF hFU_H hDial hrH hcl_r_sub_Δ
      · exact hdisj
    refine ⟨Δ, isDial_congr_of_subset hDial
      (fun v hvΔ => (hV_notZ₂ v (Set.disjoint_right.mp hDisj_Z₂_Δ hvΔ)).symm)
      (fun e heH heΔ => (hE_notZ₂ e fun heZ₂ => ?_).mpr heH)
      (fun e he''' heΔ => (hE_notZ₂ e fun heZ₂ => ?_).mp he''')
      (fun x hxΔ => (hU_notZ₂ x (Set.disjoint_right.mp hDisj_Z₂_Δ hxΔ)).symm)⟩
    · obtain ⟨x, hxe⟩ := heH.1
      exact Set.disjoint_left.mp hDisj_Z₂_Δ (heZ₂ hxe) (heΔ hxe)
    · obtain ⟨x, hxe⟩ := he'''.1
      exact Set.disjoint_left.mp hDisj_Z₂_Δ (heZ₂ hxe) (heΔ hxe)
  · -- Case 2: `Disjoint F Z₁_plus`
    have hDisj_FZ₁ : Disjoint F Z₁ := hDisj_FZ₁p.mono Subset.rfl hZ₁_sub_plus
    have hFU_H'' : F ∩ H''.U ⊆ H''.V := by
      rintro x ⟨hxF, hxH''U⟩
      have hx_notZ₁ : x ∉ Z₁ := Set.disjoint_left.mp hDisj_FZ₁ hxF
      exact (hV_notZ₁ x hx_notZ₁).mp (hFU ⟨hxF, (hU_notZ₁ x hx_notZ₁).mpr hxH''U⟩)
    have hFV_eq : F ∩ H''.V = F ∩ H'''.V := by
      ext x
      exact ⟨fun ⟨hxF, hxV⟩ => ⟨hxF, (hV_notZ₁ x (Set.disjoint_left.mp hDisj_FZ₁ hxF)).mpr hxV⟩,
        fun ⟨hxF, hxV⟩ => ⟨hxF, (hV_notZ₁ x (Set.disjoint_left.mp hDisj_FZ₁ hxF)).mp hxV⟩⟩
    obtain ⟨Δ, hDial⟩ := hRearr₂.isSpan'.isRigid F hF hFU_H'' (hFV_eq ▸ hFV)
    have hZ₁p_pre : IsPreconnected Z₁_plus :=
      isPreconnected_atomZone hS hConn hMetric hRearr₁.z_mem (by omega)
    have hDisj_Z₁p_Δ : Disjoint Z₁_plus Δ := by
      rcases subset_or_disjoint_of_isDial hDial hZ₁p_pre hDisj_FZ₁p with hsub_Z₁p | hdisj
      · exfalso
        obtain ⟨r'', hr'', hσ₁_r''⟩ := exists_region_closure_mem_of_closedSurface hS H'' σ₁
        have hdisj_Z₁p_Z₂ : Disjoint (closure Z₁_plus) (closure Z₂) := hZone_disj_Z₂ (lam₁ + 4)
          (by omega)
        have hfr_sub : frontier Z₁_plus ⊆ H''.U := by
          intro y hy_fr
          obtain ⟨a_y, ha_y, hy_a⟩ := exists_atom_of_point H y
          obtain ⟨hy_HU, hbounds⟩ :=
            frontier_atomZone_subset_U (lam₁ + 4) hS hConn hMetric hRearr₁.z_mem y hy_fr
          have := hbounds a_y ha_y hy_a
          have hy_notZ₁ : y ∉ Z₁ := by
            rw [mem_atomZone_iff_of_mem_atom ha_y hy_a]; omega
          have hy_notZ₂ : y ∉ Z₂ := fun hyZ₂ =>
            Set.disjoint_left.mp hdisj_Z₁p_Z₂ hy_fr.1 (subset_closure hyZ₂)
          exact (hU_notZ₁ y hy_notZ₁).mp ((hU_notZ₂ y hy_notZ₂).mpr hy_HU)
        have hσ₁_int : σ₁ ∈ interior Z₁_plus := by
          have hσ₁_cl : σ₁ ∈ closure Z₁_plus := subset_closure (hZ₁_sub_plus hσ₁_Z₁)
          by_contra hnot_int
          have hσ₁_fr : σ₁ ∈ frontier Z₁_plus := ⟨hσ₁_cl, hnot_int⟩
          obtain ⟨_, hbounds⟩ :=
            frontier_atomZone_subset_U (lam₁ + 4) hS hConn hMetric hRearr₁.z_mem σ₁ hσ₁_fr
          have := hbounds z₁ hRearr₁.z_mem hσ₁_z₁
          rw [hd_refl z₁ hRearr₁.z_mem] at this
          omega
        obtain ⟨p, hp_int, hp_r''⟩ :=
          mem_closure_iff.mp hσ₁_r'' (interior Z₁_plus) isOpen_interior hσ₁_int
        have hr''_sub_cl : r'' ⊆ closure Z₁_plus := by
          intro q hq_r''
          by_contra hq_not_cl
          have hp_mem : p ∈ r'' ∩ Z₁_plus := ⟨hp_r'', interior_subset hp_int⟩
          have hq_mem : q ∈ r'' \ closure Z₁_plus := ⟨hq_r'', hq_not_cl⟩
          obtain ⟨y, hy_r'', hy_fr⟩ :=
            nonempty_inter_frontier_of_isPreconnected (region_isPreconnected hr'') hp_mem hq_mem
          exact region_subset hr'' hy_r'' (hfr_sub hy_fr)
        have hcl_r''_sub_Δ : closure r'' ⊆ Δ :=
          hDial.1.isClosed.closure_subset_iff.mpr
            (hr''_sub_cl.trans (hDial.1.isClosed.closure_subset_iff.mpr hsub_Z₁p))
        exact not_closure_region_subset_of_isDial hS hF hFU_H'' hDial hr'' hcl_r''_sub_Δ
      · exact hdisj
    have hDisj_Z₁_Δ : Disjoint Z₁ Δ := hDisj_Z₁p_Δ.mono hZ₁_sub_plus Subset.rfl
    refine ⟨Δ, isDial_congr_of_subset hDial
      (fun v hvΔ => (hV_notZ₁ v (Set.disjoint_right.mp hDisj_Z₁_Δ hvΔ)).symm)
      (fun e heH'' heΔ => (hE_notZ₁ e fun heZ₁ => ?_).mpr heH'')
      (fun e he''' heΔ => (hE_notZ₁ e fun heZ₁ => ?_).mp he''')
      (fun x hxΔ => (hU_notZ₁ x (Set.disjoint_right.mp hDisj_Z₁_Δ hxΔ)).symm)⟩
    · obtain ⟨x, hxe⟩ := heH''.1
      exact Set.disjoint_left.mp hDisj_Z₁_Δ (heZ₁ hxe) (heΔ hxe)
    · obtain ⟨x, hxe⟩ := he'''.1
      exact Set.disjoint_left.mp hDisj_Z₁_Δ (heZ₁ hxe) (heΔ hxe)

/-- Claim (8) of the proof of `(5.2)` (page 131): `H'''` is rigid and 2-cell. -/
theorem isRigid_and_isTwoCell_H'''
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {G : Graph α β} {H H' H'' H''' : Drawing S}
    {η : SpanEmbedding H G} {η' : SpanEmbedding H' G} {η'' : SpanEmbedding H'' G}
    {θ_star θ lam lam₁ lam₂ μ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' d'' : Set S → Set S → ℕ} {z₁ z₂ : Set S}
    (hFlat : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (hθ_lt : 4 * lam + 2 < θ)
    (hlam₁ : 4 ≤ lam₁) (hlam₂ : 4 ≤ lam₂)
    (hlam : 6 * lam₁ + 5 * lam₂ + 3 * μ + 4 ≤ lam)
    (hRearr₁ : IsRearrangedWithin G H H' η η' θ_star θ lam₁ T_star T T' d d' z₁)
    (hRearr₂ : IsRearrangedWithin G H' H'' η' η'' θ_star (θ - (4 * lam₁ + 2)) lam₂ T_star T' T'' d'
      d'' z₂)
    (hStep : IsMuSteppedSpan G H'' η'' d'' μ)
    (hV_notZ₂ : ∀ v, v ∉ atomZone H' d' z₂ lam₂ → (v ∈ H'''.V ↔ v ∈ H.V))
    (hE_notZ₂ : ∀ e, ¬ e ⊆ atomZone H' d' z₂ lam₂ → (e ∈ H'''.E ↔ e ∈ H.E))
    (hU_notZ₂ : ∀ x, x ∉ atomZone H' d' z₂ lam₂ → (x ∈ H'''.U ↔ x ∈ H.U))
    (hV_notZ₁ : ∀ v, v ∉ atomZone H d z₁ lam₁ → (v ∈ H'''.V ↔ v ∈ H''.V))
    (hE_notZ₁ : ∀ e, ¬ e ⊆ atomZone H d z₁ lam₁ → (e ∈ H'''.E ↔ e ∈ H''.E))
    (hU_notZ₁ : ∀ x, x ∉ atomZone H d z₁ lam₁ → (x ∈ H'''.U ↔ x ∈ H''.U)) :
    IsRigid H''' ∧ (PaintingOrDrawing.drawing H''').IsTwoCell := by
  let Z₁ := atomZone H d z₁ lam₁
  let Z₂ := atomZone H' d' z₂ lam₂
  let Z₁_plus := atomZone H d z₁ (lam₁ + 4)
  have hS : IsClosedSurface S :=
    ⟨hFlat.isSpan.isSurface.1, hFlat.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hFlat.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hFlat.isSpan.isConnected
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hMetric : HasTangleMetric H θ T d := hRearr₁.isCompression.hasMetric
  have hMetric' : HasTangleMetric H' (θ - (4 * lam₁ + 2)) T' d' := hRearr₁.isCompression.hasMetric'
  obtain ⟨_, hd_refl, _⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
  obtain ⟨τ, hτ_z₂⟩ := atom_nonempty hRearr₂.z_mem
  obtain ⟨z₃, hz₃, hτ_z₃⟩ := exists_atom_of_point H τ
  obtain ⟨hCentersFar, _, _, hClaim6, hClosureDist, hDisj_cl, hz₂_eq_z₃⟩ :=
    lemma_5_2_claims_3_to_6 hFlat hθ_lt hlam₁ hlam₂ hlam hRearr₁ hRearr₂ hStep hτ_z₂ hz₃ hτ_z₃
  have hDisj_Z : Disjoint Z₁ Z₂ := hDisj_cl.mono subset_closure subset_closure
  obtain ⟨σ₁, hσ₁_z₁⟩ := atom_nonempty hRearr₁.z_mem
  have hσ₁_Z₁ : σ₁ ∈ Z₁ := by
    apply (mem_atomZone_iff_of_mem_atom hRearr₁.z_mem hσ₁_z₁).mpr
    rw [hd_refl z₁ hRearr₁.z_mem]
    omega
  have hZ₁_sub_plus : Z₁ ⊆ Z₁_plus := fun x ⟨a, ha, hle, hxa⟩ => ⟨a, ha, by omega, hxa⟩
  -- Any `atomZone H d z₁ k` with `k + 3 ≤ lam - 2 * lam₁ - lam₂ - 6` has closure disjoint from
  -- `closure Z₂`
  have hZone_disj_Z₂ : ∀ k : ℕ, k + 3 ≤ lam - 2 * lam₁ - lam₂ - 6 →
      Disjoint (closure (atomZone H d z₁ k)) (closure Z₂) := by
    intro k hk
    refine Set.disjoint_left.mpr fun x hx₁ hx₂ => ?_
    obtain ⟨a_x, ha_x, hx_a⟩ := exists_atom_of_point H x
    have hd_le : d z₁ a_x ≤ k + 3 :=
      (closure_atomZone_props hS hConn hMetric hRearr₁.z_mem x hx₁).2 a_x ha_x hx_a
    have hpt_le : pointDist H d σ₁ x ≤ k + 3 := by
      rwa [pointDist_eq_of_mem_atom hRearr₁.z_mem ha_x hσ₁_z₁ hx_a]
    have hpt_gt := hClosureDist σ₁ (subset_closure hσ₁_Z₁) x hx₂
    omega
  have hRigid : IsRigid H''' := by
    exact combined_rearrangement_is_rigid (α := α) (β := β) (S := S) (G := G) (H := H) (H' := H')
      (H'' := H'') (H''' := H''') (η := η) (η' := η') (η'' := η'') (θ_star := θ_star) (θ := θ)
      (lam := lam) (lam₁ := lam₁) (lam₂ := lam₂) (μ := μ) (T_star := T_star) (T := T) (T' := T')
      (T'' := T'') (d := d) (d' := d') (d'' := d'') (z₁ := z₁) (z₂ := z₂) hFlat hθ_lt hlam₁ hlam₂
      hlam hRearr₁ hRearr₂ hV_notZ₂ hE_notZ₂ hU_notZ₂ hV_notZ₁ hE_notZ₁ hU_notZ₁ hS hMetric
      hMetric' hd_refl τ hτ_z₂ z₃ hz₃ hτ_z₃ hCentersFar σ₁ hσ₁_z₁ hσ₁_Z₁ hZ₁_sub_plus
      hZone_disj_Z₂
  have hU'''_ne : H'''.U.Nonempty := by
    have hdisj_Z₁p_Z₂ : Disjoint (closure Z₁_plus) (closure Z₂) := hZone_disj_Z₂ (lam₁ + 4)
      (by omega)
    have hτ_Z₂ : τ ∈ Z₂ := by
      obtain ⟨_, hd'_refl, _⟩ := gm11_theorem_9_1 H' (θ - (4 * lam₁ + 2)) T' d' hS hConn hMetric'
      exact (mem_atomZone_iff_of_mem_atom hRearr₂.z_mem hτ_z₂).mpr
        (by rw [hd'_refl z₂ hRearr₂.z_mem]; omega)
    have hσ₁_mem : σ₁ ∈ univ ∩ Z₁_plus := ⟨mem_univ _, hZ₁_sub_plus hσ₁_Z₁⟩
    have hτ_mem : τ ∈ univ \ closure Z₁_plus :=
      ⟨mem_univ _, fun hcl => Set.disjoint_left.mp hdisj_Z₁p_Z₂ hcl (subset_closure hτ_Z₂)⟩
    obtain ⟨y, _, hy_fr⟩ :=
      nonempty_inter_frontier_of_isPreconnected isPreconnected_univ hσ₁_mem hτ_mem
    obtain ⟨hy_HU, _⟩ :=
      frontier_atomZone_subset_U (lam₁ + 4) hS hConn hMetric hRearr₁.z_mem y hy_fr
    have hy_notZ₂ : y ∉ Z₂ := fun hyZ₂ =>
      Set.disjoint_left.mp hdisj_Z₁p_Z₂ hy_fr.1 (subset_closure hyZ₂)
    exact ⟨y, (hU_notZ₂ y hy_notZ₂).mpr hy_HU⟩
  refine ⟨hRigid, hConn, fun r hr => ?_⟩
  have h_od := open_disc S r hS hConn
    ⟨region_nonempty hr, region_isPreconnected hr⟩ (region_isOpen hr)
    (fun F hFr hF => by
      have hFU_emp : F ∩ H'''.U = ∅ :=
        eq_empty_iff_forall_notMem.mpr fun x ⟨hxF, hxU⟩ => region_subset hr (hFr hxF) hxU
      have hFU : F ∩ H'''.U ⊆ H'''.V := by rw [hFU_emp]; exact empty_subset _
      have hFV_emp : F ∩ H'''.V = ∅ :=
        eq_empty_of_subset (inter_subset_inter_right F H'''.V_subset_U) hFU_emp
      have hFV_card : (F ∩ H'''.V).ncard ≤ 2 := by rw [hFV_emp, Set.ncard_empty]; omega
      obtain ⟨Δ, hΔ, hbd_Δ, hDial_cases⟩ := hRigid F hF hFU hFV_card
      have hΔ_disj : Disjoint Δ H'''.U := by
        rcases hDial_cases with h1 | ⟨u₁, u₂, hu12, hJV_eq, _⟩
        · exact disjoint_left.mpr fun x hxΔ hxU =>
            (eq_empty_iff_forall_notMem.mp hFU_emp x) ⟨h1 ⟨hxΔ, hxU⟩, hxU⟩
        · exfalso
          have h1 : (F ∩ H'''.V).ncard = 0 := by rw [hFV_emp, Set.ncard_empty]
          have h2 : (F ∩ H'''.V).ncard = 2 := by rw [hJV_eq, Set.ncard_pair hu12]
          omega
      obtain ⟨φ⟩ := hF
      have hpF : (φ 1).1 ∈ F := (φ 1).2
      have hpΔ : (φ 1).1 ∈ Δ := by
        have hp_bd : (φ 1).1 ∈ subBd Δ := hbd_Δ ▸ hpF
        exact hΔ.isClosed.closure_subset hp_bd.1
      have hΔ_r : Δ ⊆ r :=
        subset_region hr hΔ.isPathConnected.isConnected.isPreconnected hΔ_disj hpΔ (hFr hpF)
      exact ⟨Δ, hΔ_r, hΔ, (IsClosedDisc.subBd_eq_discBd hS hΔ).symm.trans hbd_Δ⟩)
  rcases h_od with ⟨_, hr_univ⟩ | hr_disc
  · exfalso
    obtain ⟨x, hx⟩ := hU'''_ne
    exact region_subset hr (hr_univ ▸ mem_univ x) hx
  · exact hr_disc

/-- For any walk `W : GraphWalk G x y` and any vertex `b ∈ W.support`, `W` splits as `W₁.append W₂`
at `b`. -/
theorem exists_append_eq_of_mem_support {G : Graph α β} {x y b : α}
    (W : GraphWalk G x y) (hb : b ∈ W.support) :
    ∃ (W₁ : GraphWalk G x b) (W₂ : GraphWalk G b y), W = W₁.append W₂ := by
  induction W with
  | @nil u hu =>
    rw [GraphWalk.support_nil, List.mem_singleton] at hb
    subst hb
    exact ⟨.nil hu, .nil hu, rfl⟩
  | @cons u v z e hlink r ih =>
    rw [GraphWalk.support_cons, List.mem_cons] at hb
    rcases hb with rfl | hbr
    · exact ⟨.nil hlink.left_mem, .cons hlink r, rfl⟩
    · obtain ⟨W₁, W₂, rfl⟩ := ih hbr
      exact ⟨.cons hlink W₁, W₂, rfl⟩

theorem eq_of_start_mem_right_of_append_isSimple {G : Graph α β} {x c y : α}
    (A : GraphWalk G x c) (R : GraphWalk G c y)
    (hSim : (A.append R).IsSimple) (hx : x ∈ R.support) : x = c := by
  cases A with
  | nil _ => rfl
  | cons hlink A' =>
    exfalso
    exact (List.nodup_cons.mp hSim).1 ((GraphWalk.mem_support_append A' R).mpr (Or.inr hx))

theorem eq_of_end_mem_left_of_append_isSimple {G : Graph α β} {x d y : α}
    (L : GraphWalk G x d) (B : GraphWalk G d y)
    (hSim : (L.append B).IsSimple) (hy : y ∈ L.support) : y = d := by
  induction L with
  | nil _ =>
    rw [GraphWalk.support_nil, List.mem_singleton] at hy
    exact hy
  | cons _ L' ih =>
    rw [GraphWalk.support_cons, List.mem_cons] at hy
    rcases hy with rfl | hyL'
    · exfalso
      exact (List.nodup_cons.mp hSim).1 (L'.append B).end_mem_support
    · exact ih B (List.nodup_cons.mp hSim).2 hyL'

theorem append_assoc_walk {G : Graph α β} {x y z w : α}
    (A : GraphWalk G x y) (B : GraphWalk G y z) (C : GraphWalk G z w) :
    (A.append B).append C = A.append (B.append C) := by
  induction A with
  | nil _ => rfl
  | cons _ _ ih => simp [GraphWalk.append, ih]

/-- In a simple walk `W : GraphWalk G x y`, for any two vertices `a, b ∈ W.support`, there is a
walk `W' : GraphWalk G a b` in `W` such that neither `x` nor `y` lies in `W'.support` unless it is
`a` or `b`. -/
theorem exists_subwalk_between_of_isSimple {G : Graph α β} {x y a b : α}
    (W : GraphWalk G x y) (hSim : W.IsSimple) (ha : a ∈ W.support) (hb : b ∈ W.support) :
    ∃ W' : GraphWalk G a b,
      (∀ w ∈ W'.support, w ∈ W.support) ∧
      (x ∈ W'.support → x = a ∨ x = b) ∧
      (y ∈ W'.support → y = a ∨ y = b) := by
  obtain ⟨W₁, W₂, rfl⟩ := exists_append_eq_of_mem_support W hb
  rcases (GraphWalk.mem_support_append W₁ W₂).mp ha with ha₁ | ha₂
  · obtain ⟨A, W', rfl⟩ := exists_append_eq_of_mem_support W₁ ha₁
    have hEq := append_assoc_walk A W' W₂
    refine ⟨W', fun w hw => (GraphWalk.mem_support_append _ _).mpr
      (Or.inl ((GraphWalk.mem_support_append _ _).mpr (Or.inr hw))),
      fun hx => Or.inl (eq_of_start_mem_right_of_append_isSimple A (W'.append W₂) (hEq ▸ hSim)
        ((GraphWalk.mem_support_append W' W₂).mpr (Or.inl hx))),
      fun hy => Or.inr (eq_of_end_mem_left_of_append_isSimple (A.append W') W₂ hSim
        ((GraphWalk.mem_support_append A W').mpr (Or.inr hy)))⟩
  · obtain ⟨W', B, rfl⟩ := exists_append_eq_of_mem_support W₂ ha₂
    have hEq := (append_assoc_walk W₁ W' B).symm
    refine ⟨W'.reverse, fun w hw => ?_, fun hx => Or.inr ?_, fun hy => Or.inl ?_⟩
    · rw [GraphWalk.support_reverse, List.mem_reverse] at hw
      exact (GraphWalk.mem_support_append _ _).mpr
        (Or.inr ((GraphWalk.mem_support_append _ _).mpr (Or.inl hw)))
    · rw [GraphWalk.support_reverse, List.mem_reverse] at hx
      exact eq_of_start_mem_right_of_append_isSimple W₁ (W'.append B) hSim
        ((GraphWalk.mem_support_append W' B).mpr (Or.inl hx))
    · rw [GraphWalk.support_reverse, List.mem_reverse] at hy
      exact eq_of_end_mem_left_of_append_isSimple (W₁.append W') B (hEq ▸ hSim)
        ((GraphWalk.mem_support_append W₁ W').mpr (Or.inr hy))

theorem walk_map_le {G H : Graph α β} (hle : H ≤ G) {x y : α} (W : GraphWalk H x y) :
    ∃ W' : GraphWalk G x y, W'.support = W.support := by
  induction W with
  | nil hu => exact ⟨.nil (hle.vertexSet_mono hu), rfl⟩
  | cons hlink r ih =>
    obtain ⟨r', hr'⟩ := ih
    exact ⟨.cons ((hle.isLink_iff hlink.edge_mem).mp hlink) r', by simp [hr']⟩

theorem IsLambdaCompression.trans {S : Type w} [TopologicalSpace S] [T2Space S]
    {H₀ H₁ H₂ : Drawing S} {θ₀ lam₁ lam₂ : ℕ}
    {T₀ T₁ T₂ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d₀ d₁ d₂ : Set S → Set S → ℕ}
    (h₁ : IsLambdaCompression H₀ H₁ θ₀ lam₁ T₀ T₁ d₀ d₁)
    (h₂ : IsLambdaCompression H₁ H₂ (θ₀ - lam₁) lam₂ T₁ T₂ d₁ d₂) :
    IsLambdaCompression H₀ H₂ θ₀ (lam₁ + lam₂) T₀ T₂ d₀ d₂ := by
  have hlt := h₂.lam_lt
  have hsub : θ₀ - lam₁ - lam₂ = θ₀ - (lam₁ + lam₂) := by omega
  refine ⟨by omega, h₁.hasMetric, hsub ▸ h₂.hasMetric', fun σ₁ σ₂ => ?_⟩
  have hle₁ := h₁.dist_le σ₁ σ₂
  have hle₂ := h₂.dist_le σ₁ σ₂
  omega

theorem pointDist_symm {S : Type w} [TopologicalSpace S] [T2Space S]
    {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S) (hMetric : HasTangleMetric H θ T d)
    (x y : S) :
    pointDist H d x y = pointDist H d y x := by
  obtain ⟨_, _, _, hd_symm, _⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
  obtain ⟨ax, hax, hx⟩ := exists_atom_of_point H x
  obtain ⟨ay, hay, hy⟩ := exists_atom_of_point H y
  rw [pointDist_eq_of_mem_atom hax hay hx hy, pointDist_eq_of_mem_atom hay hax hy hx,
    hd_symm ax hax ay hay]

theorem IsFlatSpan.not_isMuSteppedSpan_of_le
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {G : Graph α β} {H H' : Drawing S} {η : SpanEmbedding H G} {η' : SpanEmbedding H' G}
    {θ_star θ lam lam₁ μ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {z : Set S}
    (hFlat : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (hθ_lt : 4 * lam + 2 < θ) (hle : lam₁ ≤ lam)
    (hRearr : IsRearrangedWithin G H H' η η' θ_star θ lam₁ T_star T T' d d' z) :
    ¬ IsMuSteppedSpan G H' η' d' μ := by
  intro ⟨P, u, v, hu, hv, hP, hdist⟩
  have hS : IsClosedSurface S :=
    ⟨hFlat.isSpan.isSurface.1, hFlat.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hFlat.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hFlat.isSpan.isConnected
  obtain ⟨_, hd_refl, _⟩ := gm11_theorem_9_1 H θ T d hS hConn hRearr.isCompression.hasMetric
  obtain ⟨d'', hRearr'', hd''_eq, _⟩ :=
    hRearr.truncation_of_dist_le hRearr.z_mem hle (by rw [hd_refl z hRearr.z_mem]; omega) hθ_lt
  have hdist'' : μ ≤ d'' {u} {v} := by
    rw [hd''_eq {u} (Or.inl (Or.inl ⟨u, hu, rfl⟩)) {v} (Or.inl (Or.inl ⟨v, hv, rfl⟩))]
    have := hFlat.order_ge
    omega
  exact hFlat.no_stepped_rearrangement hRearr'' ⟨P, u, v, hu, hv, hP, hdist''⟩

theorem isHPathWithEnds_congr_of_disjoint_Z
    {S : Type w} [TopologicalSpace S]
    {G P : Graph α β} {Γ₁ Γ₂ : Drawing S}
    {η₁ : SpanEmbedding Γ₁ G} {η₂ : SpanEmbedding Γ₂ G}
    {u v : S} {Z : Set S}
    (hu : u ∈ Γ₁.V) (hv : v ∈ Γ₁.V)
    (hP : IsHPathWithEnds G η₁.imageGraph P (η₁.vMap u) (η₁.vMap v))
    (hV_notZ : ∀ w, w ∉ Z → (w ∈ Γ₂.V ↔ w ∈ Γ₁.V) ∧ (w ∈ Γ₂.V → η₂.vMap w = η₁.vMap w))
    (hE_notZ : ∀ e, ¬ e ⊆ Z → (e ∈ Γ₂.E ↔ e ∈ Γ₁.E) ∧ (e ∈ Γ₂.E → η₂.eMap e = η₁.eMap e))
    (hE_ends_Z : ∀ e ∈ Γ₂.E, e ⊆ Z → ∃ w ∈ Γ₂.V ∩ closure e, w ∈ Z)
    (hDisj₁ : Disjoint V(P) (η₁.vMap '' (Γ₁.V ∩ Z)))
    (hDisj₂ : Disjoint V(P) (η₂.vMap '' (Γ₂.V ∩ Z))) :
    u ∉ Z ∧ v ∉ Z ∧ u ∈ Γ₂.V ∧ v ∈ Γ₂.V ∧
      IsHPathWithEnds G η₂.imageGraph P (η₂.vMap u) (η₂.vMap v) := by
  have hu_notZ : u ∉ Z := fun huZ =>
    Set.disjoint_left.mp hDisj₁ hP.2.1.left_mem ⟨u, ⟨hu, huZ⟩, rfl⟩
  have hv_notZ : v ∉ Z := fun hvZ =>
    Set.disjoint_left.mp hDisj₁ hP.2.1.right_mem ⟨v, ⟨hv, hvZ⟩, rfl⟩
  have hu₂ : u ∈ Γ₂.V := (hV_notZ u hu_notZ).1.mpr hu
  have hv₂ : v ∈ Γ₂.V := (hV_notZ v hv_notZ).1.mpr hv
  have hu_map : η₂.vMap u = η₁.vMap u := (hV_notZ u hu_notZ).2 hu₂
  have hv_map : η₂.vMap v = η₁.vMap v := (hV_notZ v hv_notZ).2 hv₂
  refine ⟨hu_notZ, hv_notZ, hu₂, hv₂, η₂.imageGraph_le, ?_⟩
  rw [hu_map, hv_map]
  refine ⟨hP.2.1, hP.2.2.1, hu_map ▸ η₂.bijOn_v.mapsTo hu₂, hv_map ▸ η₂.bijOn_v.mapsTo hv₂, ?_, ?_⟩
  · rw [← hP.2.2.2.2.2.1]
    ext x
    simp only [mem_inter_iff]
    refine ⟨fun ⟨hxP, hx₂⟩ => ⟨hxP, ?_⟩, fun ⟨hxP, hx₁⟩ => ⟨hxP, ?_⟩⟩
    · obtain ⟨w, hw₂, rfl⟩ := η₂.bijOn_v.surjOn hx₂
      have hw_notZ : w ∉ Z := fun hwZ =>
        Set.disjoint_left.mp hDisj₂ hxP ⟨w, ⟨hw₂, hwZ⟩, rfl⟩
      rw [(hV_notZ w hw_notZ).2 hw₂]
      exact η₁.bijOn_v.mapsTo ((hV_notZ w hw_notZ).1.mp hw₂)
    · obtain ⟨w, hw₁, rfl⟩ := η₁.bijOn_v.surjOn hx₁
      have hw_notZ : w ∉ Z := fun hwZ =>
        Set.disjoint_left.mp hDisj₁ hxP ⟨w, ⟨hw₁, hwZ⟩, rfl⟩
      have hw₂ : w ∈ Γ₂.V := (hV_notZ w hw_notZ).1.mpr hw₁
      rw [← (hV_notZ w hw_notZ).2 hw₂]
      exact η₂.bijOn_v.mapsTo hw₂
  · refine Set.disjoint_left.mpr fun b hbP hb₂ => ?_
    obtain ⟨e, he₂, rfl⟩ := η₂.bijOn_e.surjOn hb₂
    by_cases heZ : e ⊆ Z
    · obtain ⟨w, ⟨hw₂, hwe⟩, hwZ⟩ := hE_ends_Z e he₂ heZ
      obtain ⟨z, hlink_im⟩ := (η₂.inc_iff e he₂ w hw₂).mpr hwe
      have hlinkG : G.IsLink (η₂.eMap e) (η₂.vMap w) z :=
        (η₂.imageGraph_le.isLink_iff hlink_im.edge_mem).mp hlink_im
      obtain ⟨x, y, hlinkP⟩ := (P.edge_mem_iff_exists_isLink _).mp hbP
      have hlinkP_G : G.IsLink (η₂.eMap e) x y := (hP.2.1.le.isLink_iff hbP).mp hlinkP
      have hw_VP : η₂.vMap w ∈ V(P) := by
        rcases hlinkG.eq_and_eq_or_eq_and_eq hlinkP_G with ⟨hEq, _⟩ | ⟨hEq, _⟩
        · exact hEq ▸ hlinkP.left_mem
        · exact hEq ▸ hlinkP.right_mem
      exact Set.disjoint_left.mp hDisj₂ hw_VP ⟨w, ⟨hw₂, hwZ⟩, rfl⟩
    · have he₁ : e ∈ Γ₁.E := (hE_notZ e heZ).1.mp he₂
      have he_map : η₂.eMap e = η₁.eMap e := (hE_notZ e heZ).2 he₂
      exact Set.disjoint_left.mp hP.2.2.2.2.2.2 hbP (he_map ▸ η₁.bijOn_e.mapsTo he₁)

private theorem short_path_meets_first_extended_zone
    {α : Type u}
    {β : Type v}
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {G : Graph α β}
    {H : Drawing S}
    {H' : Drawing S}
    {H'' : Drawing S}
    {η : SpanEmbedding H G}
    {η' : SpanEmbedding H' G}
    {η'' : SpanEmbedding H'' G}
    {θ_star : ℕ}
    {θ : ℕ}
    {lam : ℕ}
    {lam₁ : ℕ}
    {lam₂ : ℕ}
    {μ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {d' : Set S → Set S → ℕ}
    {d'' : Set S → Set S → ℕ}
    {z₁ : Set S}
    {z₂ : Set S}
    (hFlat : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (hθ_lt : 4 * lam + 2 < θ)
    (hlam₁ : 4 ≤ lam₁)
    (hlam₂ : 4 ≤ lam₂)
    (hlam : 6 * lam₁ + 5 * lam₂ + 3 * μ + 4 ≤ lam)
    (hRearr₁ : IsRearrangedWithin G H H' η η' θ_star θ lam₁ T_star T T' d d' z₁)
    (hRearr₂ : IsRearrangedWithin G H' H'' η' η'' θ_star (θ - (4 * lam₁ + 2)) lam₂ T_star T' T''
      d' d'' z₂)
    (hS : IsClosedSurface S)
    [hConn : ConnectedSpace S]
    (hMetric : HasTangleMetric H θ T d)
    (z₃ : Set S)
    (hClaim6 : ∀ σ₁ ∈ atomZone H d z₁ lam₁, ∀ σ₂ ∈ atomZone H' d' z₂ lam₂, lam - 2 * lam₁ - lam₂ <
      pointDist H d σ₁ σ₂)
    (hDisj_Z : Disjoint (atomZone H d z₁ lam₁) (atomZone H' d' z₂ lam₂))
    (H''' : Drawing S)
    (η''' : SpanEmbedding H''' G)
    (hnotZ₂_V : ∀ v ∉ atomZone H' d' z₂ lam₂, (v ∈ H'''.V ↔ v ∈ H.V) ∧ η'''.vMap v = η.vMap v)
    (hnotZ₂_E : ∀ (e : Set S), ¬e ⊆ atomZone H' d' z₂ lam₂ → (e ∈ H'''.E ↔ e ∈ H.E) ∧ η'''.eMap e
      = η.eMap e)
    (hnotZ₁_V : ∀ v ∉ atomZone H d z₁ lam₁, (v ∈ H'''.V ↔ v ∈ H''.V) ∧ (v ∈ H'''.V → η'''.vMap v =
      η''.vMap v))
    (hnotZ₁_E : ∀ (e : Set S), ¬e ⊆ atomZone H d z₁ lam₁ → (e ∈ H'''.E ↔ e ∈ H''.E) ∧ (e ∈ H'''.E
      → η'''.eMap e = η''.eMap e))
    (hH'''_atom_compl_H : ∀ a ∈ H'''.A, a ∉ H.A → a ⊆ atomZone H' d' z₂ lam₂)
    (hH'''_atom_compl_H'' : ∀ a ∈ H'''.A, a ∉ H''.A → a ⊆ atomZone H d z₁ lam₁)
    (hθ₃_lt : 4 * (lam₂ + 2) + 2 < θ)
    (T''' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d''' : Set S → Set S → ℕ)
    (hComp''' : IsLambdaCompression H H''' θ (4 * (lam₂ + 2) + 2) T T''' d d''')
    (hRearr''' : IsRearrangedWithin G H H''' η η''' θ_star θ (lam₂ + 2) T_star T T''' d d''' z₃)
    (hMetric''' : HasTangleMetric H''' (θ - (4 * (lam₂ + 2) + 2)) T''' d''')
    (P : Graph α β)
    (u : S)
    (v : S)
    (hu : u ∈ H''.V)
    (hv : v ∈ H''.V)
    (hP : IsHPathWithEnds G η''.imageGraph P (η''.vMap u) (η''.vMap v))
    (hdist : μ ≤ d'' {u} {v})
    (hS₁_sub_X₁ : (η.vMap '' (H.V ∩ (atomZone H d z₁ lam₁)) ∪ η'.vMap '' (H'.V ∩ (atomZone H d z₁
      lam₁))) ⊆ (η.vMap '' ({s | s ∈ H.V ∧ ∃ σ₁ ∈ (atomZone H d z₁ lam₁), pointDist H d σ₁ s ≤ μ +
      4}) ∪ η'.vMap '' (H'.V ∩ (atomZone H d z₁ lam₁))))
    (hord_ge : 4 * lam + μ + 2 ≤ θ) :
    (V(P) ∩ (η.vMap '' ({s | s ∈ H.V ∧ ∃ σ₁ ∈ (atomZone H d z₁ lam₁), pointDist H d σ₁ s ≤ μ + 4})
      ∪ η'.vMap '' (H'.V ∩ (atomZone H d z₁ lam₁)))).Nonempty := by
  let Z₁ := atomZone H d z₁ lam₁
  let Z₂ := atomZone H' d' z₂ lam₂
  let lam₃ := lam₂ + 2
  let S₁_v := {s | s ∈ H.V ∧ ∃ σ₁ ∈ Z₁, pointDist H d σ₁ s ≤ μ + 4}
  let S₁ := η.vMap '' (H.V ∩ Z₁) ∪ η'.vMap '' (H'.V ∩ Z₁)
  let X₁ := η.vMap '' S₁_v ∪ η'.vMap '' (H'.V ∩ Z₁)
  by_cases hDisj_S₁ : Disjoint V(P) S₁
  · have hE_ends_Z₁''' : ∀ e ∈ H'''.E, e ⊆ Z₁ → ∃ w ∈ H'''.V ∩ closure e, w ∈ Z₁ := by
      intro e he''' heZ₁
      obtain ⟨σ, hσe⟩ := he'''.1
      have he_notZ₂ : ¬ e ⊆ Z₂ := fun heZ₂ =>
        Set.disjoint_left.mp hDisj_Z (heZ₁ hσe) (heZ₂ hσe)
      have heH : e ∈ H.E := (hnotZ₂_E e he_notZ₂).1.mp he'''
      obtain ⟨w, hwe, hwVH⟩ := edge_closure_inter_V_nonempty heH
      have hle_e : d z₁ e ≤ lam₁ :=
        (mem_atomZone_iff_of_mem_atom (Or.inl (Or.inr heH)) hσe).mp (heZ₁ hσe)
      have hle_w : d z₁ {w} ≤ lam₁ :=
        dist_vertex_le_of_dist_edge_le hS hConn hMetric hRearr₁.z_mem heH hwVH hwe (by omega) hle_e
      have hwZ₁ : w ∈ Z₁ := ⟨{w}, Or.inl (Or.inl ⟨w, hwVH, rfl⟩), hle_w, rfl⟩
      have hw_notZ₂ : w ∉ Z₂ := Set.disjoint_left.mp hDisj_Z hwZ₁
      exact ⟨w, ⟨(hnotZ₂_V w hw_notZ₂).1.mpr hwVH, hwe⟩, hwZ₁⟩
    have hDisj₁'' : Disjoint V(P) (η''.vMap '' (H''.V ∩ Z₁)) := by
      refine hDisj_S₁.mono_right (Subset.trans ?_ subset_union_right)
      rintro x ⟨w, ⟨hwV'', hwZ₁⟩, rfl⟩
      have hw_notZ₂ : w ∉ Z₂ := Set.disjoint_left.mp hDisj_Z hwZ₁
      rcases hRearr₂.atomZone_dichotomy.2.2.2.1 w hwV'' with hwZ₂ | ⟨_, hwV', _, hmap⟩
      · exact (hw_notZ₂ hwZ₂).elim
      · exact ⟨w, ⟨hwV', hwZ₁⟩, hmap.symm⟩
    have hDisj₂''' : Disjoint V(P) (η'''.vMap '' (H'''.V ∩ Z₁)) := by
      refine hDisj_S₁.mono_right (Subset.trans ?_ subset_union_left)
      rintro x ⟨w, ⟨hwV''', hwZ₁⟩, rfl⟩
      have hw_notZ₂ : w ∉ Z₂ := Set.disjoint_left.mp hDisj_Z hwZ₁
      exact ⟨w, ⟨(hnotZ₂_V w hw_notZ₂).1.mp hwV''', hwZ₁⟩, (hnotZ₂_V w hw_notZ₂).2.symm⟩
    obtain ⟨hu_notZ₁, hv_notZ₁, hu''', hv''', hP'''⟩ :=
      isHPathWithEnds_congr_of_disjoint_Z hu hv hP hnotZ₁_V hnotZ₁_E hE_ends_Z₁''' hDisj₁''
        hDisj₂'''
    have hd'''_lt_μ : pointDist H''' d''' u v < μ := by
      rw [pointDist_eq_of_mem_atom (Or.inl (Or.inl ⟨u, hu''', rfl⟩)) (Or.inl (Or.inl ⟨v, hv''',
        rfl⟩)) rfl rfl]
      by_contra hnot
      exact hFlat.not_isMuSteppedSpan_of_le hθ_lt (by omega) hRearr'''
        ⟨P, u, v, hu''', hv''', hP''', Nat.le_of_not_lt hnot⟩
    have hd''_ge_μ : μ ≤ pointDist H'' d'' u v := by
      rwa [pointDist_eq_of_mem_atom (Or.inl (Or.inl ⟨u, hu, rfl⟩)) (Or.inl (Or.inl ⟨v, hv,
        rfl⟩)) rfl rfl]
    have hExists_σ₁ : ∃ σ₁ ∈ Z₁, pointDist H''' d''' u σ₁ < μ := by
      by_contra hnot
      push Not at hnot
      have hle'' := pointDist_le_of_common_compression hS hConn
        hComp''' (hRearr₁.isCompression.trans hRearr₂.isCompression)
        hH'''_atom_compl_H''
        (fun σ₁ hσ₁ => lt_of_lt_of_le hd'''_lt_μ (hnot σ₁ hσ₁))
        (by omega)
      omega
    obtain ⟨σ₁, hσ₁, hpt'''_uσ₁⟩ := hExists_σ₁
    have hpt'''_σ₁u : pointDist H''' d''' σ₁ u < μ := by
      rwa [pointDist_symm hS hConn hMetric''' σ₁ u]
    have hle_H : pointDist H d σ₁ u ≤ pointDist H''' d''' σ₁ u := by
      refine theorem_4_2_proof H''' H Z₂ (θ - (4 * lam₃ + 2)) θ (4 * lam₃ + 2) T''' T d''' d σ₁ u
        hS hConn hMetric''' hMetric
        hH'''_atom_compl_H (Or.inr hComp''')
        (fun σ₂ hσ₂ => ?_) (by omega)
      have hgt := hClaim6 σ₁ hσ₁ σ₂ hσ₂
      have hcomp_le := hComp'''.dist_le σ₁ σ₂
      omega
    have hpt_σ₁u : pointDist H d σ₁ u ≤ μ + 4 := by omega
    have hu_notZ₂ : u ∉ Z₂ := by
      intro huZ₂
      have := hClaim6 σ₁ hσ₁ u huZ₂
      omega
    have huH : u ∈ H.V := (hnotZ₂_V u hu_notZ₂).1.mp hu'''
    have hu_map : η.vMap u = η''.vMap u := by
      rw [← (hnotZ₂_V u hu_notZ₂).2, (hnotZ₁_V u hu_notZ₁).2 hu''']
    exact ⟨η''.vMap u, hP.2.1.left_mem, Or.inl ⟨u, ⟨huH, σ₁, hσ₁, hpt_σ₁u⟩, hu_map⟩⟩
  · obtain ⟨x, hxP, hxS₁⟩ := Set.not_disjoint_iff.mp hDisj_S₁
    exact ⟨x, hxP, hS₁_sub_X₁ hxS₁⟩

private theorem short_path_meets_second_extended_zone
    {α : Type u}
    {β : Type v}
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {G : Graph α β}
    {H : Drawing S}
    {H' : Drawing S}
    {H'' : Drawing S}
    {η : SpanEmbedding H G}
    {η' : SpanEmbedding H' G}
    {η'' : SpanEmbedding H'' G}
    {θ_star : ℕ}
    {θ : ℕ}
    {lam : ℕ}
    {lam₁ : ℕ}
    {lam₂ : ℕ}
    {μ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {d' : Set S → Set S → ℕ}
    {d'' : Set S → Set S → ℕ}
    {z₁ : Set S}
    {z₂ : Set S}
    (hFlat : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (hθ_lt : 4 * lam + 2 < θ)
    (hlam₁ : 4 ≤ lam₁)
    (hlam₂ : 4 ≤ lam₂)
    (hlam : 6 * lam₁ + 5 * lam₂ + 3 * μ + 4 ≤ lam)
    (hRearr₁ : IsRearrangedWithin G H H' η η' θ_star θ lam₁ T_star T T' d d' z₁)
    (hRearr₂ : IsRearrangedWithin G H' H'' η' η'' θ_star (θ - (4 * lam₁ + 2)) lam₂ T_star T' T''
      d' d'' z₂)
    (hS : IsClosedSurface S)
    [hConn : ConnectedSpace S]
    (hMetric : HasTangleMetric H θ T d)
    (hMetric' : HasTangleMetric H' (θ - (4 * lam₁ + 2)) T' d')
    (hMetric'' : HasTangleMetric H'' (θ - (4 * lam₁ + 2) - (4 * lam₂ + 2)) T'' d'')
    (τ : S)
    (hτ_z₂ : τ ∈ z₂)
    (_z₃ : Set S)
    (hClaim4 : ∀ σ₁ ∈ atomZone H d z₁ lam₁, lam - 2 * lam₁ < pointDist H d τ σ₁ ∧ lam - 6 * lam₁ -
      2 < pointDist H' d' τ σ₁)
    (hClaim6 : ∀ σ₁ ∈ atomZone H d z₁ lam₁, ∀ σ₂ ∈ atomZone H' d' z₂ lam₂, lam - 2 * lam₁ - lam₂ <
      pointDist H d σ₁ σ₂)
    (hDisj_Z : Disjoint (atomZone H d z₁ lam₁) (atomZone H' d' z₂ lam₂))
    (H''' : Drawing S)
    (η''' : SpanEmbedding H''' G)
    (hnotZ₂_V : ∀ v ∉ atomZone H' d' z₂ lam₂, (v ∈ H'''.V ↔ v ∈ H.V) ∧ η'''.vMap v = η.vMap v)
    (hnotZ₁_V : ∀ v ∉ atomZone H d z₁ lam₁, (v ∈ H'''.V ↔ v ∈ H''.V) ∧ (v ∈ H'''.V → η'''.vMap v =
      η''.vMap v))
    (hd'_symm : ∀ a ∈ H'.A, ∀ b ∈ H'.A, d' a b = d' b a)
    (hd'_tri : ∀ a ∈ H'.A, ∀ b ∈ H'.A, ∀ c ∈ H'.A, d' a c ≤ d' a b + d' b c)
    (P : Graph α β)
    (u : S)
    (v : S)
    (hu : u ∈ H''.V)
    (hv : v ∈ H''.V)
    (hP : IsHPathWithEnds G η''.imageGraph P (η''.vMap u) (η''.vMap v))
    (hdist : μ ≤ d'' {u} {v})
    (hS₂_sub_X₂ : (η.vMap '' (H.V ∩ (atomZone H' d' z₂ lam₂)) ∪ η''.vMap '' (H''.V ∩ (atomZone H'
      d' z₂ lam₂))) ⊆ (η.vMap '' ({s | s ∈ H.V ∧ ∃ σ₂ ∈ (atomZone H' d' z₂ lam₂), pointDist H d σ₂
      s ≤ μ + 4}) ∪ η''.vMap '' (H''.V ∩ (atomZone H' d' z₂ lam₂))))
    (hord_ge : 4 * lam + μ + 2 ≤ θ) :
    (V(P) ∩ (η.vMap '' ({s | s ∈ H.V ∧ ∃ σ₂ ∈ (atomZone H' d' z₂ lam₂), pointDist H d σ₂ s ≤ μ +
      4}) ∪ η''.vMap '' (H''.V ∩ (atomZone H' d' z₂ lam₂)))).Nonempty := by
  let Z₁ := atomZone H d z₁ lam₁
  let Z₂ := atomZone H' d' z₂ lam₂
  let S₂_v := {s | s ∈ H.V ∧ ∃ σ₂ ∈ Z₂, pointDist H d σ₂ s ≤ μ + 4}
  let S₂ := η.vMap '' (H.V ∩ Z₂) ∪ η''.vMap '' (H''.V ∩ Z₂)
  let X₂ := η.vMap '' S₂_v ∪ η''.vMap '' (H''.V ∩ Z₂)
  by_cases hDisj_S₂ : Disjoint V(P) S₂
  · have hV_notZ₂' : ∀ w, w ∉ Z₂ → (w ∈ H'.V ↔ w ∈ H''.V) ∧ (w ∈ H'.V → η'.vMap w = η''.vMap w)
      := by
      intro w hw_notZ₂
      constructor
      · refine ⟨fun hwH' => ?_, fun hwH'' => ?_⟩
        · rcases hRearr₂.atomZone_dichotomy.2.2.1 w hwH' with ⟨_, hwZ₂⟩ | ⟨_, _, hwH'', _⟩
          · exact (hw_notZ₂ hwZ₂).elim
          · exact hwH''
        · rcases hRearr₂.atomZone_dichotomy.2.2.2.1 w hwH'' with hwZ₂ | ⟨_, hwH', _⟩
          · exact (hw_notZ₂ hwZ₂).elim
          · exact hwH'
      · intro hwH'
        rcases hRearr₂.atomZone_dichotomy.2.2.1 w hwH' with ⟨_, hwZ₂⟩ | ⟨_, _, _, hmap⟩
        · exact (hw_notZ₂ hwZ₂).elim
        · exact hmap.symm
    have hE_notZ₂' : ∀ e, ¬ e ⊆ Z₂ → (e ∈ H'.E ↔ e ∈ H''.E) ∧ (e ∈ H'.E → η'.eMap e = η''.eMap e)
      := by
      intro e he_notZ₂
      constructor
      · refine ⟨fun heH' => ?_, fun heH'' => ?_⟩
        · rcases hRearr₂.atomZone_dichotomy.2.2.2.2.1 e heH' with ⟨_, heZ₂⟩ | ⟨_, _, heH'', _⟩
          · exact (he_notZ₂ heZ₂).elim
          · exact heH''
        · rcases hRearr₂.atomZone_dichotomy.2.2.2.2.2 e heH'' with heZ₂ | ⟨_, heH', _⟩
          · exact (he_notZ₂ heZ₂).elim
          · exact heH'
      · intro heH'
        rcases hRearr₂.atomZone_dichotomy.2.2.2.2.1 e heH' with ⟨_, heZ₂⟩ | ⟨_, _, _, hmap⟩
        · exact (he_notZ₂ heZ₂).elim
        · exact hmap.symm
    have hE_ends_Z₂' : ∀ e ∈ H'.E, e ⊆ Z₂ → ∃ w ∈ H'.V ∩ closure e, w ∈ Z₂ := by
      intro e he' heZ₂
      obtain ⟨w, hwe, hwV'⟩ := edge_closure_inter_V_nonempty he'
      obtain ⟨σ, hσe⟩ := he'.1
      have hle_e : d' z₂ e ≤ lam₂ :=
        (mem_atomZone_iff_of_mem_atom (Or.inl (Or.inr he')) hσe).mp (heZ₂ hσe)
      have hle_w : d' z₂ {w} ≤ lam₂ :=
        dist_vertex_le_of_dist_edge_le hS hConn hMetric' hRearr₂.z_mem he' hwV' hwe (by omega) hle_e
      exact ⟨w, ⟨hwV', hwe⟩, ⟨{w}, Or.inl (Or.inl ⟨w, hwV', rfl⟩), hle_w, rfl⟩⟩
    have hDisj₁ : Disjoint V(P) (η''.vMap '' (H''.V ∩ Z₂)) :=
      hDisj_S₂.mono_right subset_union_right
    have hDisj₂ : Disjoint V(P) (η'.vMap '' (H'.V ∩ Z₂)) := by
      refine hDisj_S₂.mono_right (Subset.trans ?_ subset_union_left)
      rintro x ⟨w, ⟨hwV', hwZ₂⟩, rfl⟩
      have hw_notZ₁ : w ∉ Z₁ := Set.disjoint_right.mp hDisj_Z hwZ₂
      rcases hRearr₁.atomZone_dichotomy.2.2.2.1 w hwV' with hwZ₁ | ⟨_, hwVH, _, hmap⟩
      · exact (hw_notZ₁ hwZ₁).elim
      · exact ⟨w, ⟨hwVH, hwZ₂⟩, hmap.symm⟩
    obtain ⟨hu_notZ₂, hv_notZ₂, hu', hv', hP'⟩ :=
      isHPathWithEnds_congr_of_disjoint_Z hu hv hP hV_notZ₂' hE_notZ₂' hE_ends_Z₂' hDisj₁ hDisj₂
    have hd'_lt_μ : pointDist H' d' u v < μ := by
      rw [pointDist_eq_of_mem_atom (Or.inl (Or.inl ⟨u, hu', rfl⟩)) (Or.inl (Or.inl ⟨v, hv',
        rfl⟩)) rfl rfl]
      by_contra hnot
      exact hFlat.not_isMuSteppedSpan_of_le hθ_lt (by omega) hRearr₁
        ⟨P, u, v, hu', hv', hP', Nat.le_of_not_lt hnot⟩
    have hd''_ge_μ : μ ≤ pointDist H'' d'' u v := by
      rwa [pointDist_eq_of_mem_atom (Or.inl (Or.inl ⟨u, hu, rfl⟩)) (Or.inl (Or.inl ⟨v, hv,
        rfl⟩)) rfl rfl]
    have hExists_σ₂ : ∃ σ₂ ∈ Z₂, pointDist H' d' u σ₂ < μ := by
      by_contra hnot
      push Not at hnot
      have hle'' := theorem_4_2_proof H' H'' Z₂ (θ - (4 * lam₁ + 2))
        (θ - (4 * lam₁ + 2) - (4 * lam₂ + 2)) (4 * lam₂ + 2) T' T'' d' d'' u v
        hS hConn hMetric' hMetric''
        (fun a ha hnotA => (hRearr₂.atomZone_dichotomy.1 a ha).resolve_right (fun h
          => hnotA h.2.2) |>.2)
        (Or.inl hRearr₂.isCompression)
        (fun σ₂ hσ₂ => lt_of_lt_of_le hd'_lt_μ (hnot σ₂ hσ₂))
        (by omega)
      omega
    obtain ⟨σ₂, hσ₂, hpt'_uσ₂⟩ := hExists_σ₂
    have hpt'_σ₂u : pointDist H' d' σ₂ u < μ := by
      rwa [pointDist_symm hS hConn hMetric' σ₂ u]
    have hle_H : pointDist H d σ₂ u ≤ pointDist H' d' σ₂ u := by
      refine theorem_4_2_proof H' H Z₁ (θ - (4 * lam₁ + 2)) θ (4 * lam₁ + 2) T' T d' d σ₂ u
        hS hConn hMetric' hMetric
        (fun a' ha' hnotA => (hRearr₁.atomZone_dichotomy.2.1 a' ha').resolve_right fun h
          => hnotA h.2.1)
        (Or.inr hRearr₁.isCompression)
        (fun σ₁ hσ₁ => ?_) (by omega)
      have h4 := (hClaim4 σ₁ hσ₁).2
      obtain ⟨a_σ₁, ha_σ₁, hσ₁_a⟩ := exists_atom_of_point H' σ₁
      obtain ⟨a_σ₂, ha_σ₂, hσ₂_a⟩ := exists_atom_of_point H' σ₂
      have hd'_σ₂ : d' z₂ a_σ₂ ≤ lam₂ := (mem_atomZone_iff_of_mem_atom ha_σ₂ hσ₂_a).mp hσ₂
      rw [pointDist_eq_of_mem_atom hRearr₂.z_mem ha_σ₁ hτ_z₂ hσ₁_a] at h4
      rw [pointDist_eq_of_mem_atom ha_σ₂ ha_σ₁ hσ₂_a hσ₁_a]
      have hsym := hd'_symm z₂ hRearr₂.z_mem a_σ₁ ha_σ₁
      have htri := hd'_tri a_σ₁ ha_σ₁ a_σ₂ ha_σ₂ z₂ hRearr₂.z_mem
      have hsym2 := hd'_symm a_σ₂ ha_σ₂ z₂ hRearr₂.z_mem
      have hsym3 := hd'_symm a_σ₁ ha_σ₁ a_σ₂ ha_σ₂
      omega
    have hpt_σ₂u : pointDist H d σ₂ u ≤ μ + 4 := by omega
    have hu_notZ₁ : u ∉ Z₁ := by
      intro huZ₁
      have := hClaim6 u huZ₁ σ₂ hσ₂
      rw [pointDist_symm hS hConn hMetric u σ₂] at this
      omega
    have huH : u ∈ H.V := (hnotZ₂_V u hu_notZ₂).1.mp ((hnotZ₁_V u hu_notZ₁).1.mpr hu)
    have hu_map : η.vMap u = η''.vMap u := by
      rw [← (hnotZ₂_V u hu_notZ₂).2, (hnotZ₁_V u hu_notZ₁).2 ((hnotZ₁_V u hu_notZ₁).1.mpr hu)]
    exact ⟨η''.vMap u, hP.2.1.left_mem, Or.inl ⟨u, ⟨huH, σ₂, hσ₂, hpt_σ₂u⟩, hu_map⟩⟩
  · obtain ⟨x, hxP, hxS₂⟩ := Set.not_disjoint_iff.mp hDisj_S₂
    exact ⟨x, hxP, hS₂_sub_X₂ hxS₂⟩

/-- Core contradiction of `(5.2)` (pages 130–133): if `H', η', T'` is obtained from `H, η, T` by
rearranging within `λ₁` of `z₁`, and `H'', η'', T''` is obtained from `H', η', T'` by rearranging
within `λ₂` of `z₂`, then `H'', η'', T''` is not `μ`-stepped. -/
theorem not_isMuSteppedSpan_of_rearranged_twice
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {G : Graph α β} {H H' H'' : Drawing S}
    {η : SpanEmbedding H G} {η' : SpanEmbedding H' G} {η'' : SpanEmbedding H'' G}
    {θ_star θ lam lam₁ lam₂ μ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' d'' : Set S → Set S → ℕ} {z₁ z₂ : Set S}
    (hFlat : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (hθ_lt : 4 * lam + 2 < θ)
    (hlam₁ : 4 ≤ lam₁) (hlam₂ : 4 ≤ lam₂)
    (hlam : 6 * lam₁ + 5 * lam₂ + 3 * μ + 4 ≤ lam)
    (hRearr₁ : IsRearrangedWithin G H H' η η' θ_star θ lam₁ T_star T T' d d' z₁)
    (hRearr₂ : IsRearrangedWithin G H' H'' η' η'' θ_star (θ - (4 * lam₁ + 2)) lam₂ T_star T' T'' d'
      d'' z₂) :
    ¬ IsMuSteppedSpan G H'' η'' d'' μ := by
  intro hStep
  let Z₁ := atomZone H d z₁ lam₁
  let Z₂ := atomZone H' d' z₂ lam₂
  have hS : IsClosedSurface S :=
    ⟨hFlat.isSpan.isSurface.1, hFlat.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hFlat.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hFlat.isSpan.isConnected
  have hMetric : HasTangleMetric H θ T d := hRearr₁.isCompression.hasMetric
  have hMetric' : HasTangleMetric H' (θ - (4 * lam₁ + 2)) T' d' := hRearr₁.isCompression.hasMetric'
  have hMetric'' : HasTangleMetric H'' (θ - (4 * lam₁ + 2) - (4 * lam₂ + 2)) T'' d'' :=
    hRearr₂.isCompression.hasMetric'
  obtain ⟨τ, hτ_z₂⟩ := atom_nonempty hRearr₂.z_mem
  obtain ⟨z₃, hz₃, hτ_z₃⟩ := exists_atom_of_point H τ
  obtain ⟨hClaim3, hClaim4, hClaim5, hClaim6, hClosureDist, hDisj_cl, hz₂_eq_z₃⟩ :=
    lemma_5_2_claims_3_to_6 hFlat hθ_lt hlam₁ hlam₂ hlam hRearr₁ hRearr₂ hStep hτ_z₂ hz₃ hτ_z₃
  have hDisj_Z : Disjoint Z₁ Z₂ := hDisj_cl.mono subset_closure subset_closure
  obtain ⟨H''', η''', hH'''_V, hH'''_E, hnotZ₂_V, hnotZ₂_E, hnotZ₂_U,
      hnotZ₁_V, hnotZ₁_E, hnotZ₁_U, hH_atom_disj_Z₂, hH_atom_compl_Z₂,
      hH'''_atom_compl_H, hH'''_atom_compl_H''⟩ :=
    exists_rearranged_H'''_η''' hFlat hθ_lt hlam₁ hlam₂ hlam hRearr₁ hRearr₂ hStep
  obtain ⟨hRigid''', h2Cell'''⟩ :=
    isRigid_and_isTwoCell_H''' hFlat hθ_lt hlam₁ hlam₂ hlam hRearr₁ hRearr₂ hStep
      (fun v hv => (hnotZ₂_V v hv).1) (fun e he => (hnotZ₂_E e he).1) hnotZ₂_U
      (fun v hv => (hnotZ₁_V v hv).1) (fun e he => (hnotZ₁_E e he).1) hnotZ₁_U
  -- Claims (11) and (12): `H''', η''', T'''` is rearranged from `H, η, T` within `lam₃ = lam₂ + 2`
  -- of `z₃`
  let lam₃ := lam₂ + 2
  have hnotZ₂_of_gt : ∀ a ∈ H.A, lam₃ < d z₃ a → Disjoint a Z₂ := by
    intro a ha hlt
    refine Set.disjoint_left.mpr fun σ hσa hσZ₂ => ?_
    have hle := hClaim5 σ hσZ₂
    rw [pointDist_eq_of_mem_atom hz₃ ha hτ_z₃ hσa] at hle
    omega
  have hAtoms₃ : ∀ a ∈ H.A, lam₃ < d z₃ a → a ∈ H'''.A :=
    fun a ha hlt => hH_atom_disj_Z₂ a ha (hnotZ₂_of_gt a ha hlt)
  have hV₃ : ∀ v ∈ H.V, lam₃ < d z₃ {v} → v ∈ H'''.V ∧ η'''.vMap v = η.vMap v := by
    intro v hv hlt
    have hv_notZ₂ : v ∉ Z₂ :=
      Set.disjoint_left.mp (hnotZ₂_of_gt {v} (Or.inl (Or.inl ⟨v, hv, rfl⟩)) hlt) rfl
    exact ⟨(hnotZ₂_V v hv_notZ₂).1.mpr hv, (hnotZ₂_V v hv_notZ₂).2⟩
  have hE₃ : ∀ e ∈ H.E, lam₃ < d z₃ e → e ∈ H'''.E ∧ η'''.eMap e = η.eMap e := by
    intro e he hlt
    obtain ⟨σ, hσe⟩ := he.1
    have he_notZ₂ : ¬ e ⊆ Z₂ := fun hsub =>
      Set.disjoint_left.mp (hnotZ₂_of_gt e (Or.inl (Or.inr he)) hlt) hσe (hsub hσe)
    exact ⟨(hnotZ₂_E e he_notZ₂).1.mpr he, (hnotZ₂_E e he_notZ₂).2⟩
  have hθ₃_lt : 4 * lam₃ + 2 < θ := by omega
  obtain ⟨_, _, T''', _, d''', _, hComp''', _, _⟩ :=
    theorem_4_5_proof H H''' θ lam₃ T d z₃ hS hConn hMetric hz₃ (by omega) hθ₃_lt
      h2Cell''' hAtoms₃
  have hRearr''' : IsRearrangedWithin G H H''' η η''' θ_star θ lam₃ T_star T T''' d d''' z₃ :=
    theorem_4_6_proof G H H''' η η''' θ_star θ lam₃ T_star T T''' d d''' z₃
      hFlat.isSpan hMetric hz₃ (by omega) hθ₃_lt hRigid''' h2Cell''' hAtoms₃ hV₃ hE₃ hComp'''
  have hMetric''' : HasTangleMetric H''' (θ - (4 * lam₃ + 2)) T''' d''' := hComp'''.hasMetric'
  -- Unpack the `μ`-stepped path `P` of `H'', η''`
  obtain ⟨_, hd_refl, _⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
  obtain ⟨_, _, _, hd'_symm, hd'_tri, _⟩ :=
    gm11_theorem_9_1 H' (θ - (4 * lam₁ + 2)) T' d' hS hConn hMetric'
  obtain ⟨P, u, v, hu, hv, hP, hdist⟩ := hStep
  let S₁_v : Set S := {s ∈ H.V | ∃ σ₁ ∈ Z₁, pointDist H d σ₁ s ≤ μ + 4}
  let S₂_v : Set S := {s ∈ H.V | ∃ σ₂ ∈ Z₂, pointDist H d σ₂ s ≤ μ + 4}
  let S₁ : Set α := (η.vMap '' (H.V ∩ Z₁)) ∪ (η'.vMap '' (H'.V ∩ Z₁))
  let S₂ : Set α := (η.vMap '' (H.V ∩ Z₂)) ∪ (η''.vMap '' (H''.V ∩ Z₂))
  let X₁ : Set α := (η.vMap '' S₁_v) ∪ (η'.vMap '' (H'.V ∩ Z₁))
  let X₂ : Set α := (η.vMap '' S₂_v) ∪ (η''.vMap '' (H''.V ∩ Z₂))
  have hS₁_sub_X₁ : S₁ ⊆ X₁ := by
    rintro x (⟨w, ⟨hwH, hwZ₁⟩, rfl⟩ | hx)
    · refine Or.inl ⟨w, ⟨hwH, w, hwZ₁, ?_⟩, rfl⟩
      rw [pointDist_eq_of_mem_atom (Or.inl (Or.inl ⟨w, hwH, rfl⟩)) (Or.inl (Or.inl ⟨w, hwH,
        rfl⟩)) rfl rfl,
        hd_refl {w} (Or.inl (Or.inl ⟨w, hwH, rfl⟩))]
      exact Nat.zero_le _
    · exact Or.inr hx
  have hS₂_sub_X₂ : S₂ ⊆ X₂ := by
    rintro x (⟨w, ⟨hwH, hwZ₂⟩, rfl⟩ | hx)
    · refine Or.inl ⟨w, ⟨hwH, w, hwZ₂, ?_⟩, rfl⟩
      rw [pointDist_eq_of_mem_atom (Or.inl (Or.inl ⟨w, hwH, rfl⟩)) (Or.inl (Or.inl ⟨w, hwH,
        rfl⟩)) rfl rfl,
        hd_refl {w} (Or.inl (Or.inl ⟨w, hwH, rfl⟩))]
      exact Nat.zero_le _
    · exact Or.inr hx
  have hord_ge := hFlat.order_ge
  -- Claim (13): `(V(P) ∩ X₂).Nonempty`
  have hMeet_X₂ : (V(P) ∩ X₂).Nonempty := by
    exact short_path_meets_second_extended_zone (α := α) (β := β) (S := S) (G := G) (H := H) (H'
      := H') (H'' := H'') (η := η) (η' := η') (η'' := η'') (θ_star := θ_star) (θ := θ) (lam :=
      lam) (lam₁ := lam₁) (lam₂ := lam₂) (μ := μ) (T_star := T_star) (T := T) (T' := T') (T'' :=
      T'') (d := d) (d' := d') (d'' := d'') (z₁ := z₁) (z₂ := z₂) hFlat hθ_lt hlam₁ hlam₂ hlam
      hRearr₁ hRearr₂ hS hMetric hMetric' hMetric'' τ hτ_z₂ z₃ hClaim4 hClaim6 hDisj_Z H''' η'''
      hnotZ₂_V hnotZ₁_V hd'_symm hd'_tri P u v hu hv hP hdist hS₂_sub_X₂ hord_ge
  -- Claim (14): `(V(P) ∩ X₁).Nonempty`
  have hMeet_X₁ : (V(P) ∩ X₁).Nonempty := by
    exact short_path_meets_first_extended_zone (α := α) (β := β) (S := S) (G := G) (H := H) (H' :=
      H') (H'' := H'') (η := η) (η' := η') (η'' := η'') (θ_star := θ_star) (θ := θ) (lam := lam)
      (lam₁ := lam₁) (lam₂ := lam₂) (μ := μ) (T_star := T_star) (T := T) (T' := T') (T'' := T'')
      (d := d) (d' := d') (d'' := d'') (z₁ := z₁) (z₂ := z₂) hFlat hθ_lt hlam₁ hlam₂ hlam hRearr₁
      hRearr₂ hS hMetric z₃ hClaim6 hDisj_Z H''' η''' hnotZ₂_V hnotZ₂_E hnotZ₁_V hnotZ₁_E
      hH'''_atom_compl_H hH'''_atom_compl_H'' hθ₃_lt T''' d''' hComp''' hRearr''' hMetric''' P u v
      hu hv hP hdist hS₁_sub_X₁ hord_ge
  -- Contradiction with Claim (10) (`no_walk_between_X₁_X₂`)
  obtain ⟨a₁, ha₁P, ha₁X₁⟩ := hMeet_X₁
  obtain ⟨a₂, ha₂P, ha₂X₂⟩ := hMeet_X₂
  obtain ⟨hPG, W₀, hW₀_sim, hVP, _⟩ := id hP.2.1
  have ha₁W₀ : a₁ ∈ W₀.support := by rwa [hVP] at ha₁P
  have ha₂W₀ : a₂ ∈ W₀.support := by rwa [hVP] at ha₂P
  obtain ⟨W_P, hWP_sub, hu_WP, hv_WP⟩ :=
    exists_subwalk_between_of_isSimple W₀ hW₀_sim ha₁W₀ ha₂W₀
  obtain ⟨W_G, hWG_sup⟩ := walk_map_le hPG W_P
  refine no_walk_between_X₁_X₂ hFlat hθ_lt hlam₁ hlam₂ hlam hRearr₁ hRearr₂
    ⟨P, u, v, hu, hv, hP, hdist⟩ W_G ha₁X₁ ha₂X₂ fun w hw hw_im => ?_
  rw [hWG_sup] at hw
  obtain ⟨s, hsH, rfl⟩ := η.bijOn_v.surjOn hw_im
  by_cases hsZ₁ : s ∈ Z₁
  · exact Or.inl (hS₁_sub_X₁ (Or.inl ⟨s, ⟨hsH, hsZ₁⟩, rfl⟩))
  · by_cases hsZ₂ : s ∈ Z₂
    · exact Or.inr (hS₂_sub_X₂ (Or.inl ⟨s, ⟨hsH, hsZ₂⟩, rfl⟩))
    · have hs''' : s ∈ H'''.V := (hnotZ₂_V s hsZ₂).1.mpr hsH
      have hs'' : s ∈ H''.V := (hnotZ₁_V s hsZ₁).1.mp hs'''
      have hmap_eq : η.vMap s = η''.vMap s := by
        rw [← (hnotZ₂_V s hsZ₂).2, (hnotZ₁_V s hsZ₁).2 hs''']
      have hwP : η.vMap s ∈ V(P) := by
        rw [hVP]
        exact hWP_sub (η.vMap s) hw
      have hw_ends : η.vMap s ∈ ({η''.vMap u, η''.vMap v} : Set α) :=
        hP.2.2.2.2.2.1 ▸ ⟨hwP, hmap_eq ▸ η''.bijOn_v.mapsTo hs''⟩
      rcases hw_ends with hEq | hEq
      · rcases hu_WP (hEq ▸ hw) with h1 | h2
        · exact Or.inl (hEq.trans h1 ▸ ha₁X₁)
        · exact Or.inr (hEq.trans h2 ▸ ha₂X₂)
      · rcases hv_WP (hEq ▸ hw) with h1 | h2
        · exact Or.inl (hEq.trans h1 ▸ ha₁X₁)
        · exact Or.inr (hEq.trans h2 ▸ ha₂X₂)

/-- Statement of Graph Minors XV, (5.2) (page 129):
"Let $\mathscr{T}^*$ be a tangle in a graph $G$, let $\Sigma$ be a surface, and let $H, \eta,
\mathscr{T}$ be a $(\lambda, \mu)$-flat $\Sigma$-span of order $\theta$. Let $\lambda_1,
\lambda_2 \ge 4$ and $\mu \ge 0$ be integers such that $\lambda \ge 6\lambda_1 + 5\lambda_2
+ 3\mu + 4$. Let $z_1 \in A(H)$, and let $H', \eta', \mathscr{T}'$ be a $\Sigma$-span
obtained from $H, \eta, \mathscr{T}$ by rearranging within $\lambda_1$ of $z_1$. Then $H',
\eta', \mathscr{T}'$ is $(\lambda_2, \mu)$-flat."
(Formalized with `4 * lam + 2 < θ`, matching `(5.1)`, to cover the case `μ = 0` when
`θ = 4 * lam + 2`. See the correction to (5.2) in `corrections/GM15.md`.) -/
def GM15Theorem52Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H H' : Drawing S) (η : SpanEmbedding H G) (η' : SpanEmbedding H' G)
    (θ_star θ lam lam₁ lam₂ μ : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d d' : Set S → Set S → ℕ) (z₁ : Set S),
    IsFlatSpan G H η θ_star θ lam μ T_star T →
    (μ = 0 → 4 * lam + 2 < θ) →
    4 ≤ lam₁ → 4 ≤ lam₂ → 6 * lam₁ + 5 * lam₂ + 3 * μ + 4 ≤ lam →
    IsRearrangedWithin G H H' η η' θ_star θ lam₁ T_star T T' d d' z₁ →
    IsFlatSpan G H' η' θ_star (θ - (4 * lam₁ + 2)) lam₂ μ T_star T'

/-- **Graph Minors XV, (5.2)** (page 129):
If `H, η, T` is a `(λ, μ)`-flat `Σ`-span of order `θ`, `λ₁, λ₂ ≥ 4`,
`λ ≥ 6λ₁ + 5λ₂ + 3μ + 4`, and `H', η', T'` is obtained from `H, η, T` by rearranging within `λ₁`
of `z₁ ∈ A(H)`, then `H', η', T'` is `(λ₂, μ)`-flat.
Proved from `(4.1)`, `(4.2)`, `(4.5)`, `(4.6)`, and Graph Minors XII, `(7.7)`, `(7.10)`, `(7.11)`.
-/
theorem theorem_5_2_proof
     :
    GM15Theorem52Statement.{u, v, w} := by
  intro S _ _ α β G H H' η η' θ_star θ lam lam₁ lam₂ μ T_star T T' d d' z₁
    hFlat hθ_gt hlam₁ hlam₂ hlam hRearr₁
  have hord := hFlat.order_ge
  have hθ_lt : 4 * lam + 2 < θ := by
    by_cases hμ0 : μ = 0
    · exact hθ_gt hμ0
    · omega
  refine ⟨hRearr₁.isSpan', by omega, ?_⟩
  intro H'' η'' T'' d'_any d'' z₂ hRearr₂
  have hS : IsClosedSurface S :=
    ⟨hFlat.isSpan.isSurface.1, hFlat.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hFlat.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hFlat.isSpan.isConnected
  obtain ⟨hd'_eq_A, hd'_eq_pt, _⟩ :=
    tangleMetric_eq_of_hasTangleMetric hS hConn
      hRearr₁.isCompression.hasMetric' hRearr₂.isCompression.hasMetric
  have hRearr₂' :
      IsRearrangedWithin G H' H'' η' η'' θ_star (θ - (4 * lam₁ + 2)) lam₂ T_star T' T'' d' d'' z₂
        := by
    refine ⟨hRearr₂.z_mem, hRearr₂.isSpan, hRearr₂.isSpan',
      fun a ha hlt => hRearr₂.atom_mem a ha (hd'_eq_A z₂ hRearr₂.z_mem a ha ▸ hlt),
      fun v hv hlt => hRearr₂.vMap_eq v hv
        (hd'_eq_A z₂ hRearr₂.z_mem {v} (Or.inl (Or.inl ⟨v, hv, rfl⟩)) ▸ hlt),
      fun e he hlt => hRearr₂.eMap_eq e he
        (hd'_eq_A z₂ hRearr₂.z_mem e (Or.inl (Or.inr he)) ▸ hlt),
      ⟨hRearr₂.isCompression.lam_lt, hRearr₁.isCompression.hasMetric',
        hRearr₂.isCompression.hasMetric', fun σ₁ σ₂ => ?_⟩⟩
    rw [hd'_eq_pt σ₁ σ₂]
    exact hRearr₂.isCompression.dist_le σ₁ σ₂
  exact not_isMuSteppedSpan_of_rearranged_twice hFlat hθ_lt hlam₁ hlam₂ hlam
    hRearr₁ hRearr₂'

end GraphMinor.GM15
