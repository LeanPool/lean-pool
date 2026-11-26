/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section7ProperProof
import LeanPool.GraphMinor.GM16.Metric
import LeanPool.GraphMinor.GM16.Tower
import LeanPool.GraphMinor.GM16.Section8Main
import LeanPool.GraphMinor.GM16.Section6Proof
import LeanPool.GraphMinor.GM16.Section5Five
import LeanPool.GraphMinor.GM16.Section4Proof

import LeanPool.GraphMinor.GM12.Bridge

/-!
# The backward and surface-tower inductions of Graph Minors XVI

Use the proved animal step and proper arrangement to obtain (6.1), then
remove hairs to get (5.1) and horns to get (4.1). The finite surface tower
combines (4.1) with the sphere span to obtain (3.1). Each induction uses
the earlier proofs directly.
-/

public section

namespace GraphMinor.GM16

attribute [local instance] SurfaceTowerFor.topSpace SurfaceTowerFor.t2Space

open Set Function Topology
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14 GraphMinor.GM15

universe u v w u' v'

/-- **Graph Minors XVI, (6.1)** (page 58, proved on page 63 from (7.1), (7.2), and (7.4)):
"Let $\Sigma$ be a surface, and let $p, \tau, \chi, \delta \ge 0$ and $\phi, \psi \ge 1$. Then there
exist $\sigma, \kappa, \rho, \zeta \ge 0$ and $\theta \ge 1$ such that if $\mathscr{T}^*$ is a
tangle
in a graph $G$, and there is an animal with $\chi$ horns and $\delta$ hairs, of strength
$\ge (\theta, \sigma)$, then either
1. there is a $\Sigma'$-span of order $\ge \phi$, for some surface $\Sigma'$ obtained from $\Sigma$
   by adding a handle or a crosscap, or
2. there is an animal with $\chi$ horns and $\delta + 1$ hairs, of strength $\ge (\psi, \tau)$, or
3. there exists $Z \subseteq V(G)$ with $|Z| \le \zeta$, and a $\mathscr{T}^* \setminus Z$-central
   segregation of $G \setminus Z$ of type $(\rho, \kappa)$ with a proper arrangement in $\Sigma$, or
4. $\mathscr{T}^*$ controls a $K_p$-minor of $G$." -/
theorem theorem_6_1_of_7_1_and_7_2
     :
    GM16Theorem61Statement.{u, v, w} := by
  intro S _ _ hS hconn p τ χ δ φ ψ hφ hψ
  let φ' := max φ 3
  let ψ' := max ψ 3
  have hφ'3 : 3 ≤ φ' := le_max_right _ _
  have hψ'3 : 3 ≤ ψ' := le_max_right _ _
  obtain ⟨κ, lam, ρ, θ₂, hθ₂_pos, h72_prop⟩ := GraphMinor.GM16.theorem_7_2_proof.{u, v, w} hS hconn
    p φ' (2 * ψ')
  let θ' := max θ₂ p
  have hθ'_pos : 1 ≤ θ' := le_trans hθ₂_pos (le_max_left _ _)
  obtain ⟨θ, σ, hθ_pos, h71_prop⟩ := GraphMinor.GM16.theorem_7_1_proof.{u, v, w} hS hconn τ χ δ lam
    θ' φ' ψ' hθ'_pos hφ'3 hψ'3
  let ζ := χ + δ ^ 2 * φ' ^ 2 / 2
  refine ⟨σ, κ, ρ, ζ, θ, hθ_pos, ?_⟩
  intro α β G θ_star T_star hT hAnim
  rcases h71_prop G θ_star T_star hT hAnim with
    ⟨S', htopS', ht2S', H', η', θ_span', T', hCS', hconnS', hHandle, hφ'_le, hSpan'⟩ |
    hAnim_next |
    ⟨Z, H_l, η_l, θ_l, T_l, d_l, hZ_sub, hZ_le, hZ_lt, hθ'_le, hLevel⟩
  · exact Or.inl ⟨S', htopS', ht2S', H', η', θ_span', T', hCS', hconnS',
      Or.inl hHandle, (le_max_left _ _).trans hφ'_le, hSpan'⟩
  · exact Or.inr (Or.inl (hAnim_next.mono hψ (le_max_left _ _) le_rfl))
  · have hT_del : IsGraphTangle (GM09.deleteVertices G Z) (θ_star - Z.ncard)
        (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) :=
      isGraphTangle_deleteGraphVerticesTangle hT hZ_sub hZ_lt
    have hθ₂_le : θ₂ ≤ θ_l := (le_max_left _ _).trans hθ'_le
    rcases h72_prop (GM09.deleteVertices G Z) (θ_star - Z.ncard) θ_l
        (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star)
        H_l η_l T_l d_l hT_del hθ₂_le hLevel with
      ⟨S', htopS', ht2S', H', η', θ_span', T', hCS', hconnS', hCross, hφ'_le, hSpan_del⟩ |
      ⟨S_seg, α_disc, α_pt, hCent, hType, hProp⟩ |
      hCtrl_del
    · have hSpan_G : @IsSigmaSpan α β S' htopS' ht2S' G H'
          (@liftSpanEmbedding S' htopS' α β H' (GM09.deleteVertices G Z) G η'
            (G.induce_le sdiff_subset)) θ_star θ_span' T_star T' :=
        @theorem_7_4_proof S' htopS' ht2S' α β G θ_star θ_span' T_star hT Z H' η' T' hZ_sub hZ_lt
          hSpan_del
      exact Or.inl ⟨S', htopS', ht2S', H',
        @liftSpanEmbedding S' htopS' α β H' (GM09.deleteVertices G Z) G η'
          (G.induce_le sdiff_subset),
        θ_span', T', hCS', hconnS', Or.inr hCross, (le_max_left _ _).trans hφ'_le, hSpan_G⟩
    · exact Or.inr (Or.inr (Or.inl ⟨Z, S_seg, α_disc, α_pt,
        hZ_sub, hZ_le, hZ_lt, hCent, hType, hProp⟩))
    · have hp_le_del : V(completeGraph p).ncard ≤ θ_star - Z.ncard := by
        rw [vertexSet_completeGraph_ncard]
        have hp_le_θ' : p ≤ θ_l := (le_max_right _ _).trans hθ'_le
        exact hp_le_θ'.trans hLevel.isSpan.isControlling.theta_le
      exact Or.inr (Or.inr (Or.inr
        (controlsMinor_of_deleteGraphVerticesTangle hT hZ_sub hZ_lt hp_le_del hCtrl_del)))


/-- Graph Minors XVI, (6.1), pages 58 and 63, from the proved animal
step (7.1), the proper arrangement theorem (7.2), and tangle deletion. -/
theorem theorem_6_1_proof : GM16Theorem61Statement.{u, v, w} :=
  theorem_6_1_of_7_1_and_7_2

/-- **Graph Minors XVI, (5.1)** (page 55, proved on page 61 from (6.1) and (6.3)):
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
theorem theorem_5_1_of_6_1_and_6_3
     :
    GM16Theorem51Statement.{u, v, w} := by
  intro S _ _ hS hconn p τ χ φ ψ hφ hψ
  obtain ⟨δ, θ_δ, hθ_δ_pos, h63_prop⟩ := GraphMinor.GM16.theorem_6_3_proof.{u, v, w} hS hconn p τ χ
    ψ hψ
  let σ_δ := τ + 1
  -- By backward induction from m = 0 (corresponding to i = δ hairs) to m = δ (corresponding to i =
  -- 0 hairs):
  have hind : ∀ m : ℕ, m ≤ δ →
      ∃ σ_m κ_m ρ_m ζ_m θ_m : ℕ, 1 ≤ θ_m ∧
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (hT : IsGraphTangle G θ_star T_star),
          HasAnimal S G T_star θ_star χ (δ - m) θ_m σ_m →
          (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S')
            (H' : Drawing S') (η' : SpanEmbedding H' G) (θ_span' : ℕ)
            (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
            IsClosedSurface S' ∧ ConnectedSpace S' ∧
            IsObtainedByAddingHandleOrCrosscap S S' ∧
            φ ≤ θ_span' ∧ IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨
          HasHairlessAnimal S G T_star θ_star (χ + 1) ψ τ ∨
          (∃ (Z : Set α) (S_seg : Set (Society α β))
            (α_disc : Society α β → Set S) (α_pt : α → S),
            Z ⊆ V(G) ∧ Z.ncard ≤ ζ_m ∧ Z.ncard < θ_star ∧
            IsCentralSegregation (deleteVertices G Z)
              (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) S_seg ∧
            IsSegregationOfType (deleteVertices G Z) ρ_m κ_m S_seg ∧
            IsProperArrangement S_seg α_disc α_pt) ∨
          ControlsMinor G (completeGraph p) T_star := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨σ_δ, 0, 0, 0, θ_δ, hθ_δ_pos, ?_⟩
      intro α β G θ_star T_star hT hAnim
      rw [Nat.sub_zero] at hAnim
      rcases h63_prop G θ_star T_star hT hAnim with hOut2 | hOut4
      · exact Or.inr (Or.inl hOut2)
      · exact Or.inr (Or.inr (Or.inr hOut4))
    | succ m ih =>
      intro hm_le
      obtain ⟨σ_next, κ_next, ρ_next, ζ_next, θ_next, hθ_next_pos, hnext⟩ := ih (by omega)
      let i := δ - (m + 1)
      obtain ⟨σ_i, κ_i, ρ_i, ζ_i, θ_i, hθ_i_pos, h61_prop⟩ :=
        GraphMinor.GM16.theorem_6_1_proof.{u, v, w} hS hconn p σ_next χ i φ θ_next hφ hθ_next_pos
      let κ_new := max κ_next κ_i
      let ρ_new := max ρ_next ρ_i
      let ζ_new := max ζ_next ζ_i
      refine ⟨σ_i, κ_new, ρ_new, ζ_new, θ_i, hθ_i_pos, ?_⟩
      intro α β G θ_star T_star hT hAnim
      rcases h61_prop G θ_star T_star hT hAnim with
        hOut1 | hOut2 | ⟨Z, S_seg, α_disc, α_pt, hZ_sub, hZ_le, hZ_lt, hCent, hType, hProp⟩ | hOut4
      · exact Or.inl hOut1
      · have hi_succ : i + 1 = δ - m := by omega
        rw [hi_succ] at hOut2
        rcases hnext G θ_star T_star hT hOut2 with
          hOut1' | hOut2' | ⟨Z, S_seg, α_disc, α_pt, hZ_sub, hZ_le, hZ_lt, hCent, hType, hProp⟩ |
            hOut4'
        · exact Or.inl hOut1'
        · exact Or.inr (Or.inl hOut2')
        · exact Or.inr (Or.inr (Or.inl ⟨Z, S_seg, α_disc, α_pt,
            hZ_sub, hZ_le.trans (le_max_left _ _), hZ_lt, hCent,
            hType.mono (le_max_left _ _) (le_max_left _ _), hProp⟩))
        · exact Or.inr (Or.inr (Or.inr hOut4'))
      · exact Or.inr (Or.inr (Or.inl ⟨Z, S_seg, α_disc, α_pt,
          hZ_sub, hZ_le.trans (le_max_right _ _), hZ_lt, hCent,
          hType.mono (le_max_right _ _) (le_max_right _ _), hProp⟩))
      · exact Or.inr (Or.inr (Or.inr hOut4))
  obtain ⟨σ₀, κ, ρ, ζ, θ₀, hθ₀_pos, hfull⟩ := hind δ le_rfl
  refine ⟨σ₀, κ, ρ, ζ, θ₀, hθ₀_pos, ?_⟩
  intro α β G θ_star T_star hT hAnim
  have hAnim₀ : HasAnimal S G T_star θ_star χ (δ - δ) θ₀ σ₀ := by
    rw [Nat.sub_self]
    exact hAnim
  exact hfull G θ_star T_star hT hAnim₀


/-- Graph Minors XVI, (5.1), pages 55 and 61, by the backward induction
on the number of hairs, using the proved (6.1) and (6.3). -/
theorem theorem_5_1_proof : GM16Theorem51Statement.{u, v, w} :=
  theorem_5_1_of_6_1_and_6_3

/-- **Graph Minors XVI, (4.1)** (page 52, proved on page 58 from (5.1) and (5.5)):
"Let $\Sigma$ be a surface and let $p \ge 0$, $\phi \ge 1$. Then there exist $\kappa, \rho, \zeta
\ge 0$
and $\theta \ge 1$ such that if $\mathscr{T}^*$ is a tangle in a graph $G$, and there is a
$\Sigma$-span of order $\ge \theta$, then either
• there is a $\Sigma'$-span of order $\ge \phi$, for some surface $\Sigma'$ obtained from $\Sigma$
  by adding a handle or crosscap, or
• there exists $Z \subseteq V(G)$ with $|Z| \le \zeta$, and a $\mathscr{T}^* \setminus Z$-central
  segregation of $G \setminus Z$ of type $(\rho, \kappa)$ with a proper arrangement in $\Sigma$, or
• $\mathscr{T}^*$ controls a $K_p$ minor of $G$." -/
theorem theorem_4_1_of_5_1_and_5_5
     :
    GM16Theorem41Statement.{u, v, w} := by
  intro S _ _ hS hconn p φ hφ
  let μ := p * (p - 1) / 2
  obtain ⟨θ_μ, hθ_μ_pos, h55_prop⟩ := GraphMinor.GM16.theorem_5_5_proof.{u, v, w} hS hconn p
  let σ_μ := 4 * p * (p - 1)
  -- By backward induction from m = 0 (corresponding to i = μ) to m = μ (corresponding to i = 0):
  -- For any m ≤ μ, there exist σ_m, κ_m, ρ_m, ζ_m ≥ 0 and θ_m ≥ 1 such that any hairless animal
  -- with (μ - m) horns and strength ≥ (θ_m, σ_m) satisfies one of the three outcomes of (4.1).
  have hind : ∀ m : ℕ, m ≤ μ →
      ∃ σ_m κ_m ρ_m ζ_m θ_m : ℕ, 1 ≤ θ_m ∧
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (hT : IsGraphTangle G θ_star T_star),
          HasHairlessAnimal S G T_star θ_star (μ - m) θ_m σ_m →
          (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S')
            (H' : Drawing S') (η' : SpanEmbedding H' G) (θ_span' : ℕ)
            (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
            IsClosedSurface S' ∧ ConnectedSpace S' ∧
            IsObtainedByAddingHandleOrCrosscap S S' ∧
            φ ≤ θ_span' ∧ IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨
          (∃ (Z : Set α) (S_seg : Set (Society α β))
            (α_disc : Society α β → Set S) (α_pt : α → S),
            Z ⊆ V(G) ∧ Z.ncard ≤ ζ_m ∧ Z.ncard < θ_star ∧
            IsCentralSegregation (deleteVertices G Z)
              (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) S_seg ∧
            IsSegregationOfType (deleteVertices G Z) ρ_m κ_m S_seg ∧
            IsProperArrangement S_seg α_disc α_pt) ∨
          ControlsMinor G (completeGraph p) T_star := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨σ_μ, 0, 0, 0, θ_μ, hθ_μ_pos, ?_⟩
      intro α β G θ_star T_star hT hAnim
      rw [Nat.sub_zero] at hAnim
      exact Or.inr (Or.inr (h55_prop G θ_star T_star hT hAnim))
    | succ m ih =>
      intro hm_le
      obtain ⟨σ_next, κ_next, ρ_next, ζ_next, θ_next, hθ_next_pos, hnext⟩ := ih (by omega)
      let i := μ - (m + 1)
      obtain ⟨σ_i, κ_i, ρ_i, ζ_i, θ_i, hθ_i_pos, h51_prop⟩ :=
        GraphMinor.GM16.theorem_5_1_proof.{u, v, w} hS hconn p σ_next i φ θ_next hφ hθ_next_pos
      let κ_new := max κ_next κ_i
      let ρ_new := max ρ_next ρ_i
      let ζ_new := max ζ_next ζ_i
      refine ⟨σ_i, κ_new, ρ_new, ζ_new, θ_i, hθ_i_pos, ?_⟩
      intro α β G θ_star T_star hT hAnim
      rcases h51_prop G θ_star T_star hT hAnim with
        hOut1 | hOut2 | ⟨Z, S_seg, α_disc, α_pt, hZ_sub, hZ_le, hZ_lt, hCent, hType, hProp⟩ | hOut4
      · exact Or.inl hOut1
      · have hi_succ : i + 1 = μ - m := by omega
        rw [hi_succ] at hOut2
        rcases hnext G θ_star T_star hT hOut2 with
          hOut1' | ⟨Z, S_seg, α_disc, α_pt, hZ_sub, hZ_le, hZ_lt, hCent, hType, hProp⟩ | hOut4'
        · exact Or.inl hOut1'
        · exact Or.inr (Or.inl ⟨Z, S_seg, α_disc, α_pt,
            hZ_sub, hZ_le.trans (le_max_left _ _), hZ_lt, hCent,
            hType.mono (le_max_left _ _) (le_max_left _ _), hProp⟩)
        · exact Or.inr (Or.inr hOut4')
      · exact Or.inr (Or.inl ⟨Z, S_seg, α_disc, α_pt,
          hZ_sub, hZ_le.trans (le_max_right _ _), hZ_lt, hCent,
          hType.mono (le_max_right _ _) (le_max_right _ _), hProp⟩)
      · exact Or.inr (Or.inr hOut4)
  obtain ⟨σ₀, κ, ρ, ζ, θ₀, hθ₀_pos, hfull⟩ := hind μ le_rfl
  refine ⟨κ, ρ, ζ, θ₀, hθ₀_pos, ?_⟩
  intro α β G θ_star θ_span T_star H η T hT hθ₀_le hSpan
  obtain ⟨d, hMet⟩ := exists_tangleMetric hS hSpan.isRespectful
  have hAnim₀ : HasHairlessAnimal S G T_star θ_star (μ - μ) θ₀ σ₀ := by
    rw [Nat.sub_self]
    exact hasHairlessAnimal_zero_of_isSigmaSpan hθ₀_pos hθ₀_le hSpan hMet
  exact hfull G θ_star T_star hT hAnim₀


/-- Graph Minors XVI, (4.1), pages 52 and 58, by the backward induction
on the number of horns, using the proved (5.1) and (5.5). -/
theorem theorem_4_1_proof : GM16Theorem41Statement.{u, v, w} :=
  theorem_4_1_of_5_1_and_5_5

/-- **Graph Minors XVI, (3.1)** (page 54, proved from (4.1), (4.2), (4.3), and Graph Minors XII,
(4.2)):
For any finite graph `L` with a surface tower `tower : SurfaceTowerFor L`, there exist
`κ, ρ, ζ ≥ 0` and `θ ≥ 1` such that any tangle `T` of order `≥ θ` in a graph `G` controlling no
`L`-minor admits `Z ⊆ V(G)` with `|Z| ≤ ζ` and a `T \ Z`-central segregation of `G \ Z` of type
`(ρ, κ)` with a proper arrangement in some surface in which `L` cannot be drawn. -/
theorem theorem_3_1_of_tower
    {α' : Type u'} {β' : Type v'} (L : Graph α' β') (hVL : V(L).Finite) (hEL : E(L).Finite)
    (tower : SurfaceTowerFor.{u, v, w, u', v'} L) :
    ∃ κ ρ ζ θ : ℕ, 1 ≤ θ ∧
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_G : ℕ)
        (T : Set (Hypergraph α β × Hypergraph α β))
        (hT : IsGraphTangle G θ_G T),
        θ ≤ θ_G → ¬ ControlsMinor G L T →
        ∃ (Z : Set α) (S_seg : Set (Society α β))
          (S : Type w) (_ : TopologicalSpace S) (_ : T2Space S)
          (α_disc : Society α β → Set S) (α_pt : α → S),
          Z ⊆ V(G) ∧ Z.ncard ≤ ζ ∧ Z.ncard < θ_G ∧
          IsClosedSurface S ∧ ConnectedSpace S ∧ ¬ CanBeDrawnIn S L ∧
          IsCentralSegregation (deleteVertices G Z)
            (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T θ_G) S_seg ∧
          IsSegregationOfType (deleteVertices G Z) ρ κ S_seg ∧
          IsProperArrangement S_seg α_disc α_pt := by
  classical
  have h43 : GM16Theorem43Statement.{u, v, w, u', v'} := theorem_4_3_proof
  obtain ⟨p, hp_ctrl⟩ := GraphMinor.GM12.gm16_theorem42.{u, v, u', v'} L hVL hEL
  -- Inductive step from k = 0 to tower.n:
  -- For any m ≤ tower.n, there exist κ_m, ρ_m, ζ_m ≥ 0 and θ_fn : Fin tower.n → ℕ (with 1 ≤ θ_fn i)
  -- such that if G has a (tower.Surf i)-span of order ≥ θ_fn i for some i with tower.n - m ≤ i.1,
  -- and T controls no L-minor and has order ≥ max p V(L).ncard, then the desired segregation
  -- exists.
  have hind : ∀ m : ℕ, m ≤ tower.n →
      ∃ (κ_m ρ_m ζ_m : ℕ) (θ_fn : Fin tower.n → ℕ),
        (∀ i : Fin tower.n, 1 ≤ θ_fn i) ∧
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_G : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (hT : IsGraphTangle G θ_G T_star),
          p ≤ θ_G → ¬ ControlsMinor G L T_star →
          ∀ (i : Fin tower.n), tower.n - m ≤ i.1 →
          ∀ (H : Drawing (tower.Surf i)) (η : SpanEmbedding H G) (θ_span : ℕ)
            (T : Set (Hypergraph (tower.Surf i) (Set (tower.Surf i)) ×
              Hypergraph (tower.Surf i) (Set (tower.Surf i)))),
            θ_fn i ≤ θ_span → IsSigmaSpan G H η θ_G θ_span T_star T →
            ∃ (Z : Set α) (S_seg : Set (Society α β))
              (S : Type w) (_ : TopologicalSpace S) (_ : T2Space S)
              (α_disc : Society α β → Set S) (α_pt : α → S),
              Z ⊆ V(G) ∧ Z.ncard ≤ κ_m + ρ_m + ζ_m ∧ Z.ncard ≤ ζ_m ∧ Z.ncard < θ_G ∧
              IsClosedSurface S ∧ ConnectedSpace S ∧ ¬ CanBeDrawnIn S L ∧
              IsCentralSegregation (deleteVertices G Z)
                (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_G) S_seg ∧
              IsSegregationOfType (deleteVertices G Z) ρ_m κ_m S_seg ∧
              IsProperArrangement S_seg α_disc α_pt := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨0, 0, 0, fun _ => 1, fun _ => le_rfl, ?_⟩
      intro α β G θ_G T_star hT _ _ i hi
      exact absurd i.2 (not_lt_of_ge (by omega))
    | succ m ih =>
      intro hm_le
      obtain ⟨κ_prev, ρ_prev, ζ_prev, θ_prev, hθ_prev_pos, hprev⟩ := ih (by omega)
      let idx_m : Fin tower.n := ⟨tower.n - (m + 1), by omega⟩
      let φ_m : ℕ := Finset.sup Finset.univ θ_prev + 1
      have hφ_pos : 1 ≤ φ_m := Nat.le_add_left 1 _
      have hφ_ge : ∀ j : Fin tower.n, θ_prev j ≤ φ_m := fun j =>
        (Finset.le_sup (f := θ_prev) (Finset.mem_univ j)).trans (Nat.le_succ _)
      by_cases hdraw : CanBeDrawnIn (tower.Surf idx_m) L
      · obtain ⟨θ_draw, hθ_draw_pos, hno_span⟩ :=
          h43 L (tower.isClosedSurface idx_m) (tower.isConnected idx_m) hVL hEL hdraw
        let θ_new : Fin tower.n → ℕ := fun i => if i = idx_m then θ_draw else θ_prev i
        refine ⟨κ_prev, ρ_prev, ζ_prev, θ_new, fun i => ?_, ?_⟩
        · dsimp [θ_new]
          split_ifs
          · exact hθ_draw_pos
          · exact hθ_prev_pos i
        · intro α β G θ_G T_star hT hp_le hnot_L i hi H η θ_span T hθ_le hSpan
          by_cases hi_eq : i = idx_m
          · subst hi_eq
            have hθ_draw_le : θ_draw ≤ θ_span := by simpa [θ_new] using hθ_le
            exact (hno_span G θ_G T_star H η θ_span T hT hnot_L hθ_draw_le hSpan).elim
          · have hi_gt : tower.n - m ≤ i.1 := by
              have : i.1 ≠ tower.n - (m + 1) := fun h => hi_eq (Fin.ext h)
              omega
            have hθ_prev_le : θ_prev i ≤ θ_span := by simpa [θ_new, hi_eq] using hθ_le
            exact hprev G θ_G T_star hT hp_le hnot_L i hi_gt H η θ_span T hθ_prev_le hSpan
      · obtain ⟨κ_cur, ρ_cur, ζ_cur, θ_cur, hθ_cur_pos, h41_prop⟩ :=
          GraphMinor.GM16.theorem_4_1_proof.{u, v, w} (tower.isClosedSurface idx_m)
            (tower.isConnected idx_m) p φ_m hφ_pos
        let κ_new := max κ_prev κ_cur
        let ρ_new := max ρ_prev ρ_cur
        let ζ_new := max ζ_prev ζ_cur
        let θ_new : Fin tower.n → ℕ := fun i => if i = idx_m then θ_cur else θ_prev i
        refine ⟨κ_new, ρ_new, ζ_new, θ_new, fun i => ?_, ?_⟩
        · dsimp [θ_new]
          split_ifs
          · exact hθ_cur_pos
          · exact hθ_prev_pos i
        · intro α β G θ_G T_star hT hp_le hnot_L i hi H η θ_span T hθ_le hSpan
          by_cases hi_eq : i = idx_m
          · subst hi_eq
            have hθ_cur_le : θ_cur ≤ θ_span := by simpa [θ_new] using hθ_le
            rcases h41_prop G θ_G θ_span T_star H η T hT hθ_cur_le hSpan with
              ⟨S', htopS', ht2S', H', η', θ_span', T', hCS', hconnS', hAdd, hφ_le', hSpan'⟩ |
              ⟨Z, S_seg, α_disc, α_pt, hZ_sub, hZ_le, hZ_lt, hCent, hType, hProp⟩ |
              hCtrlKp
            · obtain ⟨j, hij, H_j, η_j, θ_span_j, T_j, hφ_j, hSpan_j⟩ :=
                tower.step_index idx_m hdraw G θ_G φ_m T_star S' H' η' θ_span' T'
                  hCS' hconnS' hAdd hφ_le' hSpan'
              have hj_ge : tower.n - m ≤ j.1 := by
                have : idx_m.1 < j.1 := hij
                dsimp [idx_m] at this
                omega
              have hθ_prev_j : θ_prev j ≤ θ_span_j := (hφ_ge j).trans hφ_j
              obtain ⟨Z, S_seg, S_out, htop_out, ht2_out, α_disc, α_pt,
                hZ_sub, _, hZ_le, hZ_lt, hCS_out, hconn_out, hnot_draw_out,
                hCent, hType, hProp⟩ :=
                hprev G θ_G T_star hT hp_le hnot_L j hj_ge H_j η_j θ_span_j T_j hθ_prev_j hSpan_j
              have hζ_le : Z.ncard ≤ ζ_new := hZ_le.trans (le_max_left _ _)
              exact ⟨Z, S_seg, S_out, htop_out, ht2_out, α_disc, α_pt,
                hZ_sub, by omega, hζ_le, hZ_lt, hCS_out, hconn_out, hnot_draw_out,
                hCent, hType.mono (le_max_left _ _) (le_max_left _ _), hProp⟩
            · have hζ_le : Z.ncard ≤ ζ_new := hZ_le.trans (le_max_right _ _)
              exact ⟨Z, S_seg, tower.Surf idx_m, tower.topSpace idx_m, tower.t2Space idx_m,
                α_disc, α_pt, hZ_sub, by omega, hζ_le, hZ_lt,
                tower.isClosedSurface idx_m, tower.isConnected idx_m, hdraw,
                hCent, hType.mono (le_max_right _ _) (le_max_right _ _), hProp⟩
            · have hgm12_Kp :
                  GM12.ControlsMinor (Hypergraph.ofGraph G hT.finite_V hT.finite_E) θ_G T_star
                    (completeGraph p) :=
                gm12_controlsMinor_of_controlsMinor hT.finite_V hT.finite_E hCtrlKp
                  (by simpa using hp_le)
              have hgm12_L := hp_ctrl G θ_G T_star hT hgm12_Kp
              exact (hnot_L (controlsMinor_of_gm12 hgm12_L)).elim
          · have hi_gt : tower.n - m ≤ i.1 := by
              have : i.1 ≠ tower.n - (m + 1) := fun h => hi_eq (Fin.ext h)
              omega
            have hθ_prev_le : θ_prev i ≤ θ_span := by simpa [θ_new, hi_eq] using hθ_le
            obtain ⟨Z, S_seg, S_out, htop_out, ht2_out, α_disc, α_pt,
              hZ_sub, _, hZ_le, hZ_lt, hCS_out, hconn_out, hnot_draw_out,
              hCent, hType, hProp⟩ :=
              hprev G θ_G T_star hT hp_le hnot_L i hi_gt H η θ_span T hθ_prev_le hSpan
            have hζ_le : Z.ncard ≤ ζ_new := hZ_le.trans (le_max_left _ _)
            exact ⟨Z, S_seg, S_out, htop_out, ht2_out, α_disc, α_pt,
              hZ_sub, by omega, hζ_le, hZ_lt, hCS_out, hconn_out, hnot_draw_out,
              hCent, hType.mono (le_max_left _ _) (le_max_left _ _), hProp⟩
  obtain ⟨κ, ρ, ζ, θ_fn, hθ_fn_pos, hfull⟩ := hind tower.n le_rfl
  let i₀ : Fin tower.n := ⟨0, tower.one_le_n⟩
  obtain ⟨θ_star₀, hθ_star₀_pos, h42_prop⟩ := GraphMinor.GM16.theorem_4_2_proof.{u, v, w} (θ_fn i₀)
    (hθ_fn_pos i₀)
  let θ := max θ_star₀ p
  refine ⟨κ, ρ, ζ, θ, le_trans hθ_star₀_pos (le_max_left _ _), ?_⟩
  intro α β G θ_G T hT hθ_le hnot_L
  have hθ_star₀_le : θ_star₀ ≤ θ_G := (le_max_left _ _).trans hθ_le
  have hp_le : p ≤ θ_G := (le_max_right _ _).trans hθ_le
  obtain ⟨H₀, η₀, θ_span₀, T₀, hθ₀_le, hSpan₀⟩ :=
    h42_prop G θ_G T hT hθ_star₀_le (tower.Surf i₀)
      (tower.isClosedSurface i₀) (tower.isConnected i₀) tower.isSphere_zero
  obtain ⟨Z, S_seg, S_out, htop_out, ht2_out, α_disc, α_pt,
    hZ_sub, _, hZ_le, hZ_lt, hCS_out, hconn_out, hnot_draw_out, hCent, hType, hProp⟩ :=
    hfull G θ_G T hT hp_le hnot_L i₀ (by omega) H₀ η₀ θ_span₀ T₀ hθ₀_le hSpan₀
  exact ⟨Z, S_seg, S_out, htop_out, ht2_out, α_disc, α_pt,
    hZ_sub, hZ_le, hZ_lt, hCS_out, hconn_out, hnot_draw_out, hCent, hType, hProp⟩

/-- **Graph Minors XVI, (3.1)** (page 49, proved on page 54 from (4.1), (4.2), (4.3), and
Graph Minors XII, (4.2)):
"For any graph $L$, there are integers $\kappa, \rho, \zeta \ge 0$ and $\theta \ge 1$ with the
following property. Let $\mathscr{T}$ be a tangle of order $\ge \theta$ in a graph $G$, controlling
no $L$-minor of $G$. Then there exists $Z \subseteq V(G)$ with $|Z| \le \zeta$, and a
$\mathscr{T} \setminus Z$-central segregation of $G \setminus Z$ of type $(\rho, \kappa)$ which has
a
proper arrangement in some surface in which $L$ cannot be drawn." -/
theorem theorem_3_1_of_statements
     :
    GM16Theorem31Statement.{u, v, w, u', v'} := by
  intro α' β' L hVL hEL
  obtain ⟨tower⟩ := GraphMinor.GM16.surfaceTower.{u, v, w, u', v'} L hVL hEL
  exact theorem_3_1_of_tower L hVL hEL tower


/-- Graph Minors XVI, (3.1), pages 49 and 54, by induction over the
surface tower, starting with the proved sphere span (4.2) and using
the proved animal reduction (4.1). No result of XVI is assumed. -/
theorem theorem_3_1_proof : GM16Theorem31Statement.{u, v, w, u', v'} :=
  theorem_3_1_of_statements

end GraphMinor.GM16
