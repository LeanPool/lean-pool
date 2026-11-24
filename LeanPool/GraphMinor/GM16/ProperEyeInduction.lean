/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.ProperEyeInductionStep
public import LeanPool.GraphMinor.GM15.Section8

import LeanPool.GraphMinor.GM09.Bridge

import LeanPool.GraphMinor.GM12.Section710

import LeanPool.GraphMinor.GM12.Section77

import LeanPool.GraphMinor.GM14.Bridge

import LeanPool.GraphMinor.GM15.Section3Crosscap

import LeanPool.GraphMinor.GM15.Section3Parallel

import LeanPool.GraphMinor.GM15.Section5

import LeanPool.GraphMinor.GM15.Section7

/-!
# Proper arrangements through the downward eye induction

The induction in XV, pages 115–116, repeatedly applies the eye step.
The arrangement outcome keeps the same discs while its numerical bounds
increase. We retain its properness for XVI (7.2), page 62.
-/

public section
namespace GraphMinor.GM16
open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 GM15
universe u v w

private theorem proper_eye_inductive_step
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hSurf : IsSurface S) (hConn : ConnectedSpace S) (hBd : bd S = ∅)
    {κ φ' μ' lam_target θ_target : ℕ}
    (hφ'8 : 8 ≤ φ') (hμ'12 : 12 ≤ μ') (hμ'_even : Even μ')
    (hlam_t : 4 ≤ lam_target) (hθ_t : 4 * lam_target + μ' + 2 ≤ θ_target) :
    ∀ n ≤ κ + 1,
      ∃ (p_n lam_n θ_n : ℕ),
        4 ≤ lam_n ∧ 4 * lam_n + μ' + 2 ≤ θ_n ∧
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G) (θ₀ : ℕ)
          (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (d₀ : Set S → Set S → ℕ),
          IsFlatSpan G H₀ η₀ θ_star θ₀ lam_n μ' T_star T₀ →
          HasTangleMetric H₀ θ₀ T₀ d₀ →
          θ_n ≤ θ₀ →
          HasEyesAtDistance G H₀ η₀ θ₀ T₀ d₀ (κ + 1 - n) θ_n →
          Section7S1 S G θ_star T_star κ μ' lam_target θ_target ∨
          Section7S2 S G θ_star T_star φ' ∨
          (∃ (𝒮 : Set (Society α β)) (disc : Society α β → Set S) (pt : α → S),
            IsCentralSegregation G T_star 𝒮 ∧
            GM15.IsSegregationOfType G p_n κ 𝒮 ∧ IsProperArrangement 𝒮 disc pt) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨0, lam_target, θ_target, hlam_t, hθ_t, ?_⟩
    intro α β G θ_star T_star H₀ η₀ θ₀ T₀ d₀ hFlat₀ hMetric₀ hθ₀_ge hEyes₀
    left
    have h4 : 4 ≤ θ_target := by omega
    exact GraphMinor.GM15.theorem_7_1_proof.{u, v, w} G H₀ η₀ θ_star θ₀ θ_target lam_target μ'
      (κ + 1) T_star T₀ d₀
      hFlat₀ hMetric₀ (by omega) hθ_t h4 hθ₀_ge hEyes₀
  | succ n ih =>
    intro hn1
    have hn : n ≤ κ + 1 := Nat.le_of_succ_le hn1
    obtain ⟨p_n, lam_n, θ_n, hlam_n4, hθ_n_ge, hIH⟩ := ih hn
    let k := κ + 1 - (n + 1)
    have hk_le : k ≤ κ := by omega
    have hk_succ : k + 1 = κ + 1 - n := by omega
    obtain ⟨p_k, lam_k, θ_k, hθ_k_ge, hStep⟩ :=
      proper_eye_induction_step S hSurf hConn hBd k φ' μ' lam_n θ_n hφ'8 hμ'12 hμ'_even hlam_n4
        hθ_n_ge
    let p_next := max p_k p_n
    let lam_next := max lam_k 4
    let θ_next := max θ_k (4 * lam_next + μ' + 2)
    have hlam_next4 : 4 ≤ lam_next := le_max_right _ _
    have hθ_next_ge : 4 * lam_next + μ' + 2 ≤ θ_next := le_max_right _ _
    refine ⟨p_next, lam_next, θ_next, hlam_next4, hθ_next_ge, ?_⟩
    intro α β G θ_star T_star H₀ η₀ θ₀ T₀ d₀ hFlat₀ hMetric₀ hθ₀_ge hEyes₀
    have hθ_k_le_θ_next : θ_k ≤ θ_next := le_max_left _ _
    have hθ_k_le_θ₀ : θ_k ≤ θ₀ := hθ_k_le_θ_next.trans hθ₀_ge
    have hFlat_k : IsFlatSpan G H₀ η₀ θ_star θ₀ lam_k μ' T_star T₀ :=
      hFlat₀.mono_lam_mu (le_max_left _ _) le_rfl (hθ_k_ge.trans hθ_k_le_θ₀)
        (fun _ => by have := hFlat₀.order_ge; omega)
    have hEyes_k : HasEyesAtDistance G H₀ η₀ θ₀ T₀ d₀ k θ_k := by
      rcases hEyes₀ with ⟨r, hr_inj, hr_eye, hr_dist⟩
      exact ⟨r, hr_inj, hr_eye, fun i j hij => hθ_k_le_θ_next.trans (hr_dist i j hij)⟩
    rcases hStep G θ_star T_star H₀ η₀ θ₀ T₀ d₀ hFlat_k hMetric₀ hθ_k_le_θ₀ hEyes_k with
      hS1 | hS2 | hS3
    · rcases hS1 with ⟨H₁, η₁, T₁, d₁, r₁, hFlat₁, hMetric₁, hr₁_inj, hr₁_eye, hr₁_dist⟩
      have hEyes₁ : HasEyesAtDistance G H₁ η₁ θ_n T₁ d₁ (k + 1) θ_n :=
        ⟨r₁, hr₁_inj, hr₁_eye, fun i j hij => le_of_eq (hr₁_dist i j hij).symm⟩
      rw [hk_succ] at hEyes₁
      rcases hIH G θ_star T_star H₁ η₁ θ_n T₁ d₁ hFlat₁ hMetric₁ le_rfl hEyes₁ with
        hOut1 | hOut2 | ⟨S_seg, α_disc, α_pt, hCent, hType, hArr⟩
      · exact Or.inl hOut1
      · exact Or.inr (Or.inl hOut2)
      · exact Or.inr (Or.inr ⟨S_seg, α_disc, α_pt, hCent,
          hType.mono (le_max_right _ _) le_rfl, hArr⟩)
    · exact Or.inr (Or.inl hS2)
    · rcases hS3 with ⟨S_seg, α_disc, α_pt, hCent, hType, hArr⟩
      exact Or.inr (Or.inr ⟨S_seg, α_disc, α_pt, hCent,
        hType.mono (le_max_left _ _) hk_le, hArr⟩)


/-- XV (1.1), pages 115–116, with the properness retained from the actual
arrangement construction, as required in XVI (7.2), page 62. -/
theorem proper_arrangement_or_independent_eyes_or_crosscap
     :
    ∀ (S : Type w) [TopologicalSpace S] [T2Space S],
    IsSurface S → ConnectedSpace S → bd S = ∅ →
    ∀ (κ φ μ : ℕ),
      ∃ (θ lam p : ℕ),
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G) (θ₀ : ℕ)
          (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (d₀ : Set S → Set S → ℕ),
          IsFlatSpan G H₀ η₀ θ_star θ₀ lam μ T_star T₀ →
          HasTangleMetric H₀ θ₀ T₀ d₀ →
          θ ≤ θ₀ →
          (∃ (H' : Drawing S) (η' : SpanEmbedding H' G) (θ' : ℕ)
            (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
            (d' : Set S → Set S → ℕ),
            IsSigmaSpan G H' η' θ_star θ' T_star T' ∧
            HasTangleMetric H' θ' T' d' ∧
            φ ≤ θ' ∧
            HasIndependentEyes G H' η' θ' T' d' (κ + 1)) ∨
          (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'),
            IsObtainedByAddingCrosscap S S' ∧
            ∃ (H' : Drawing S') (η' : SpanEmbedding H' G) (θ' : ℕ)
              (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
               φ ≤ θ' ∧ IsSigmaSpan G H' η' θ_star θ' T_star T') ∨
          (∃ (𝒮 : Set (Society α β)) (disc : Society α β → Set S) (pt : α → S),
            IsCentralSegregation G T_star 𝒮 ∧
            GM15.IsSegregationOfType G p κ 𝒮 ∧ IsProperArrangement 𝒮 disc pt) := by
  have h51 : GM15Theorem51Statement.{u, v, w} :=
    GM15.theorem_5_1_proof
  have h71 : GM15Theorem71Statement.{u, v, w} :=
    GM15.theorem_7_1_proof
  intro S _ _ hSurf hConn hBd κ φ μ
  let μ' : ℕ := 2 * (μ + 6)
  let φ' : ℕ := max φ 8
  let lam_top : ℕ := 4
  let θ_top : ℕ := max φ' (4 * lam_top + μ' + 2)
  have hφ'8 : 8 ≤ φ' := le_max_right _ _
  have hφ_le_φ' : φ ≤ φ' := le_max_left _ _
  have hμ'12 : 12 ≤ μ' := by omega
  have hμ_le_μ' : μ ≤ μ' := by omega
  have hμ'_even : Even μ' := ⟨μ + 6, by ring⟩
  have hθ_top_ge : 4 * lam_top + μ' + 2 ≤ θ_top := le_max_right _ _
  have hφ_le_θ_top : φ ≤ θ_top := hφ_le_φ'.trans (le_max_left _ _)
  obtain ⟨p, lam₀, θ₀_base, hlam₀4, hθ₀_base_ge, hInd⟩ :=
    proper_eye_inductive_step hSurf hConn hBd hφ'8 hμ'12 hμ'_even
      (le_refl 4) hθ_top_ge (κ + 1) le_rfl
  let θ : ℕ := max θ₀_base (4 * lam₀ + μ' + 2)
  refine ⟨θ, lam₀, p, ?_⟩
  intro α β G θ_star T_star H₀ η₀ θ₀ T₀ d₀ hFlat₀ hMetric₀ hθ_le
  have hθ₀_base_le : θ₀_base ≤ θ₀ := (le_max_left _ _).trans hθ_le
  have hord_μ' : 4 * lam₀ + μ' + 2 ≤ θ₀ := (le_max_right _ _).trans hθ_le
  have hFlat_μ' : IsFlatSpan G H₀ η₀ θ_star θ₀ lam₀ μ' T_star T₀ :=
    hFlat₀.mono_mu hμ_le_μ' hord_μ'
  have hEyes0 : HasEyesAtDistance G H₀ η₀ θ₀ T₀ d₀ (κ + 1 - (κ + 1)) θ₀_base := by
    rw [Nat.sub_self]
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  rcases hInd G θ_star T_star H₀ η₀ θ₀ T₀ d₀ hFlat_μ' hMetric₀ hθ₀_base_le hEyes0 with
    ⟨H₁, η₁, T₁, d₁, r₁, hFlat₁, hMetric₁, hr₁_inj, hr₁_eye, hr₁_dist⟩ |
    ⟨S', hTS', hT2S', hCross, H', η', T', hSpan'⟩ | hS3
  · left
    have hθ_top_18 : μ' + 18 ≤ θ_top := by omega
    have hIndEyes : HasIndependentEyes G H₁ η₁ θ_top T₁ d₁ (κ + 1) :=
      independentEyes_of_flatSpan G H₁ η₁ θ_star θ_top μ' κ T_star T₁ d₁ r₁ hFlat₁ hMetric₁
        hμ'12 hθ_top_18 hr₁_inj hr₁_eye hr₁_dist
    exact ⟨H₁, η₁, θ_top, T₁, d₁, hFlat₁.isSpan, hMetric₁, hφ_le_θ_top, hIndEyes⟩
  · right; left
    exact ⟨S', hTS', hT2S', hCross, H', η', φ', T', hφ_le_φ', hSpan'⟩
  · right; right
    exact hS3


end GraphMinor.GM16
