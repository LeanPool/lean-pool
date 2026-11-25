/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.EyeInductionParameters

public import LeanPool.GraphMinor.GM16.ProperLocalAssembly
import LeanPool.GraphMinor.GM15.Section8

import LeanPool.GraphMinor.GM09.Bridge

import LeanPool.GraphMinor.GM12.Section710

import LeanPool.GraphMinor.GM12.Section77

import LeanPool.GraphMinor.GM14.Bridge

import LeanPool.GraphMinor.GM15.Section3Crosscap

import LeanPool.GraphMinor.GM15.Section3Parallel

/-!
# Properness through the eye induction

The induction step in XV (1.2), proved on pages 144–145, either creates
another eye, adds a crosscap, or uses the arrangement from XV (7.7).
We retain the properness of that arrangement in the third outcome,
as required by XVI (7.2), page 62.
-/

public section
namespace GraphMinor.GM16
open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 GM15
universe u v w

/-- The induction step of XV (1.2), retaining the proper arrangement
from XV (7.7) for the use in XVI (7.2), page 62. -/
theorem proper_eye_induction_step
     :
    ∀ (S : Type w) [TopologicalSpace S] [T2Space S],
    IsSurface S → ConnectedSpace S → bd S = ∅ →
    ∀ (k φ μ lam_next θ_next : ℕ),
      8 ≤ φ → 12 ≤ μ → Even μ → 4 ≤ lam_next →
      4 * lam_next + μ + 2 ≤ θ_next →
      ∃ (p_k lam_k θ_k : ℕ),
        4 * lam_k + μ + 2 ≤ θ_k ∧
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G) (θ₀ : ℕ)
          (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (d₀ : Set S → Set S → ℕ),
          IsFlatSpan G H₀ η₀ θ_star θ₀ lam_k μ T_star T₀ →
          HasTangleMetric H₀ θ₀ T₀ d₀ →
          θ_k ≤ θ₀ →
          HasEyesAtDistance G H₀ η₀ θ₀ T₀ d₀ k θ_k →
          Section7S1 S G θ_star T_star k μ lam_next θ_next ∨
          Section7S2 S G θ_star T_star φ ∨
          (∃ (𝒮 : Set (Society α β)) (disc : Society α β → Set S) (pt : α → S),
            IsCentralSegregation G T_star 𝒮 ∧
            GM15.IsSegregationOfType G p_k k 𝒮 ∧ IsProperArrangement 𝒮 disc pt) := by
  have h71 : GM15Theorem71Statement.{u, v, w} :=
    GM15.theorem_7_1_proof
  have h75 : GM15Theorem75Statement.{u, v, w} :=
    GM15.theorem_7_5_proof
  have h79 : GM15Theorem79Statement.{u, v, w} := GM15.theorem_7_9_proof
  have h710 : GM15Theorem710Statement.{u, v, w} :=
    GM15.theorem_7_10_proof
  have h711 : GM15Theorem711Statement.{u, v, w} :=
    GM15.theorem_7_11_proof
  intro S _ _ _ _ _ k φ μ lam' θ' hφ8 hμ12 hμ_even hlam'4 hθ'_ge
  let θ'' := (eyeInductionParameters φ μ θ').enlargedOrder
  let τ₁ := (eyeInductionParameters φ μ θ').firstThreshold
  let τ₂ := (eyeInductionParameters φ μ θ').secondThreshold
  let π := (eyeInductionParameters φ μ θ').transactionSize
  let beta := (eyeInductionParameters φ μ θ').battlefieldSize
  let θ_k := (eyeInductionParameters φ μ θ').order
  let lam_k := (eyeInductionParameters φ μ θ').flatness
  let p_k := (eyeInductionParameters φ μ θ').segregationWidth
  rcases eye_induction_parameter_bounds hφ8 hμ12 hlam'4 hθ'_ge with
    ⟨hθ''_even, hθ'_le_θ'', h4_θ', h4_θ_k, hθ''_ge, hθ''_gt, hφ2, hφ3, hτ₁_ge, hτ₂_ge,
      hπ2, hπ3, hθ_k_ge, hlam_bound_μ, hθ_bound_μ, hθ''_beta, h16beta, h6beta,
      hφ_le, hbeta_lam, h2τ₁_lt, hlam_bound_beta⟩
  refine ⟨p_k, lam_k, θ_k, hθ_k_ge, ?_⟩
  intro α β G θ_star T_star H₀ η₀ θ₀ T₀ d₀ hFlat₀ hMetric₀ hθ₀_ge hEyes₀
  -- Step 1: Apply (7.1) to obtain a `(lam_k, μ)`-flat `Σ`-span `H, η, T` of order `θ_k` with `k`
  -- eyes `r` mutually at distance `θ_k`.
  obtain ⟨H, η, T, d, r, hFlat, hMetric, hr_inj, hr_eye, hr_dist⟩ :=
    h71 G H₀ η₀ θ_star θ₀ θ_k lam_k μ k T_star T₀ d₀ hFlat₀ hMetric₀
      (by omega) hθ_k_ge h4_θ_k hθ₀_ge hEyes₀
  -- Step 2: Check whether `(S1)` holds for `θ''` (which implies `(S1)` for `θ'` by (7.1)).
  by_cases hS1_θ'' : Section7S1 S G θ_star T_star k μ lam' θ''
  · left
    rcases hS1_θ'' with ⟨H₁, η₁, T₁, d₁, r₁, hFlat₁, hMetric₁, hr₁_inj, hr₁_eye, hr₁_dist⟩
    have hEyes_θ' : HasEyesAtDistance G H₁ η₁ θ'' T₁ d₁ (k + 1) θ' :=
      ⟨r₁, hr₁_inj, hr₁_eye, fun i j hij =>
        hθ'_le_θ''.trans (le_of_eq (hr₁_dist i j hij).symm)⟩
    exact h71 G H₁ η₁ θ_star θ'' θ' lam' μ (k + 1) T_star T₁ d₁ hFlat₁ hMetric₁
      (by omega) hθ'_ge h4_θ' hθ'_le_θ'' hEyes_θ'
  · -- Step 3: Since `(S1)` does not hold for `θ''`, apply (7.4) to obtain `S₀, α₀`.
    obtain ⟨η_G0, hη_G0_v, hη_G0_e, hnot_step_G0⟩ :=
      exists_section7G0_embedding G H η θ_star θ_k θ'' lam_k μ k T_star T d r hFlat hMetric
        (by omega)
    obtain ⟨S₀, α₀_disc, α₀_pt, hThree, hLocal, hArr₀, hCompat₀⟩ :=
      GM15.theorem_7_4_proof G H η
        θ_star θ_k θ'' lam_k lam' μ k T_star T d r η_G0
        hFlat hMetric hμ12 hμ_even hlam'4 hθ''_ge hθ''_gt hlam_bound_μ hθ_bound_μ
        hr_inj hr_eye hr_dist hη_G0_v hη_G0_e hnot_step_G0 hS1_θ''
    -- Step 4: Apply (7.5) to obtain the eye data `D i` for `i : Fin k`.
    obtain ⟨D, hDisj_Δ⟩ :=
      h75 G H η θ_star θ_k θ'' lam_k π beta μ k T_star T d r η_G0 S₀ α₀_disc α₀_pt
        hFlat hMetric (by omega) hπ2 hπ3 rfl hθ''_beta h16beta h6beta
        hr_inj hr_eye hr_dist hη_G0_v hη_G0_e hThree hLocal hArr₀ hCompat₀
    -- Step 5: Either no `(G_i*, Ω_i*)` has a crooked transaction of size `π`, or some `i` does.
    by_cases hAllNoCrook :
        ∀ i : Fin k, ∀ P_set : Set (Graph α β),
          (D i).localSociety.IsCrookedTransaction P_set → P_set.ncard ≠ π
    · -- By (7.7), `(S3)` holds.
      right; right
      exact exists_proper_arrangement_of_no_crooked_transactions G H η θ_star θ_k θ'' lam_k π beta
        μ k T_star T d r η_G0 S₀ α₀_disc α₀_pt D
        hFlat hMetric (by omega) hπ2 hπ3 rfl hθ''_beta le_rfl
        hr_inj hr_eye hr_dist hη_G0_v hη_G0_e hThree hLocal hArr₀ hCompat₀ hDisj_Δ hAllNoCrook
    · -- Some `i : Fin k` has a crooked transaction `P_star` of cardinality `π`.
      push Not at hAllNoCrook
      rcases hAllNoCrook with ⟨i, P_star, hCrook_star, hCard_star⟩
      -- By (7.8), obtain `P, X` in `(G₀ ∪ J_i, Ω_i)`.
      obtain ⟨P, X, hTransP, hPathsP, hX_sub, hEndsP, hFreeX, hCases⟩ :=
        GM15.theorem_7_8_proof G H η θ_star θ_k θ'' π beta μ φ τ₁ τ₂ k T_star T d r
          S₀ α₀_disc α₀_pt i (D i) P_star hφ2 hτ₁_ge hτ₂_ge le_rfl hCrook_star hCard_star
      rcases hCases with ⟨hCardφ, hCross⟩ | ⟨hCardτ₁, hLeap⟩ | ⟨hCardτ₂, hDouble⟩
      · -- Case (i): `P` is a crosscap transaction of size `φ`; by (7.9), `(S2)` holds.
        right; left
        exact h79 G H η θ_star θ_k θ'' π beta μ φ k T_star T d r S₀ α₀_disc α₀_pt i (D i) P X
          hφ3 hφ_le hTransP hPathsP hX_sub hEndsP hFreeX hCardφ hCross
      · -- Case (ii): `P` is a leap transaction of size `τ₁`; impossible by (7.10).
        exfalso
        exact h710 G H η θ_star θ_k θ'' lam_k π beta μ τ₁ k T_star T d r
          S₀ α₀_disc α₀_pt i (D i) P X hFlat hμ12 hμ_even rfl hbeta_lam h2τ₁_lt
          hTransP hPathsP hX_sub hEndsP hFreeX hCardτ₁ hLeap
      · -- In case (iii), (7.11) gives `(S1)` at `θ''` for the doublecross transaction.
        exfalso
        exact hS1_θ'' (h711 G H η θ_star θ_k θ'' lam_k lam' π beta μ τ₂ k T_star T d r
          S₀ α₀_disc α₀_pt i (D i) P X hFlat hMetric (by omega) hlam'4 hθ''_ge hθ''_even rfl
          hlam_bound_beta hθ''_beta le_rfl hr_inj hr_eye hr_dist
          hTransP hPathsP hX_sub hEndsP hFreeX hCardτ₂ hDouble)


end GraphMinor.GM16
