/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralSubstitution.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralSubstitutionError
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralSubstitutionDiagonal
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralPartialCauchy

/-!
# Ginibre Brownian integral substitution

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianIntegral_bounded_substitution_meanSquare`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Stochastic substitution for actual bounded continuous original-filtration
integrands. Both integral identities use their genuine mean-square defining
limits; independence from the scalar integral's own filtration is unnecessary. -/
theorem brownianIntegral_bounded_substitution_meanSquare
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (A : ℝ≥0 → Ω → ℝ) (u : ι → ℝ≥0 → Ω → ℝ)
    (hA : ∀ r, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB r) _ (A r))
    (hu : ∀ i r, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB r) _ (u i r))
    (C U : ℝ) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hAb : ∀ r ω, ‖A r ω‖ ≤ C) (hub : ∀ i r ω, ‖u i r ω‖ ≤ U)
    (T : ℝ≥0) (hc : ∀ᵐ ω ∂P, ContinuousOn (fun r => A r ω) (Set.Icc 0 T))
    (β : ℝ≥0 → Ω → ℝ) (hβ : ∀ r, MemLp (β r) 2 P)
    (hpartial : ∀ r, r ≤ T → Tendsto (fun k => ∫ ω,
      (brownianAggregatePartialSum B u T (k + 1) r ω - β r ω) ^ 2 ∂P) atTop (𝓝 0))
    (J : Ω → ℝ) (hJ : MemLp J 2 P)
    (hproduct : Tendsto (fun k => ∫ ω,
      ((∑ i, brownianUniformLeftSum (B i) (fun r ω => A r ω * u i r ω) T (k + 1) ω) - J ω) ^ 2 ∂P)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (brownianUniformLeftSum β A T (n+1) ω-J ω)^2 ∂P)
      atTop (𝓝 0) := by
  classical
  have hAm (r : ℝ≥0) : Measurable (A r) := (hA r).mono
    ((ginibreBrownianAugmentedFiltration B P hB).le r) le_rfl
  have hum (i : ι) (r : ℝ≥0) : Measurable (u i r) := (hu i r).mono
    ((ginibreBrownianAugmentedFiltration B P hB).le r) le_rfl
  have hui (i : ι) (r : ℝ≥0) : MemLp (u i r) 2 P := MemLp.of_bound
    (hum i r).aestronglyMeasurable U (Eventually.of_forall (hub i r))
  have hpL (K : ℕ) (r : ℝ≥0) : MemLp (brownianAggregatePartialSum B u T K r) 2 P := by
    apply memLp_finsetSum
    intro i hi
    exact brownianUniformPartialSum_memLp_two B P hB hind i (u i) (hu i) (hui i) T K r
  have hβS (N : ℕ) : MemLp (brownianUniformLeftSum β A T N) 2 P := by
    apply memLp_finsetSum
    intro k hk
    exact actualBoundedMultiplier_memLp_two P (A (itoUniformNNTime T N k)) _
      (hAm _).aestronglyMeasurable ((hβ _).sub (hβ _)) C (hAb _)
  have hSL (N M : ℕ) : MemLp (brownianSubstitutionCoarseApproximation B u A T N M) 2 P := by
    apply memLp_finsetSum
    intro k hk
    exact actualBoundedMultiplier_memLp_two P (A (itoUniformNNTime T N k)) _
      (hAm _).aestronglyMeasurable ((hpL _ _).sub (hpL _ _)) C (hAb _)
  have hProdL (K : ℕ) : MemLp (fun ω => ∑ i,
      brownianUniformLeftSum (B i) (fun r ω => A r ω*u i r ω) T K ω) 2 P := by
    apply memLp_finsetSum
    intro i hi
    exact brownianActualLeftGridSum_memLp_two B P hB hind i _ (fun r => (hA r).mul (hu i r))
      (fun r => actualBoundedMultiplier_memLp_two P (A r) (u i r)
        (hAm r).aestronglyMeasurable (hui i r) C (hAb r))
      (itoUniformNNTime T K) (itoUniformNNTime_mono T K) K
  have hfixed (n : ℕ) : Tendsto (fun m => ∫ ω,
      (brownianSubstitutionCoarseApproximation B u A T (n+1) (m+1) ω-
        brownianUniformLeftSum β A T (n+1) ω)^2 ∂P) atTop (𝓝 0) := by
    have hK : Tendsto (fun m : ℕ => (n+1)*(m+1)-1) atTop atTop := by
      apply tendsto_atTop_mono _ tendsto_id
      intro m
      change m ≤ (n+1)*(m+1)-1
      have hh := Nat.mul_le_mul_right (m+1) (show 1≤n+1 by omega)
      simp only [one_mul] at hh
      omega
    have he (m : ℕ) : (n+1)*(m+1)-1+1=(n+1)*(m+1) := by
      have hp := Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos m)
      exact Nat.sub_add_cancel hp
    have hl (k : Fin (n+1+1)) : Tendsto (fun m => ∫ ω,
        (brownianAggregatePartialSum B u T ((n+1)*(m+1)) (itoUniformNNTime T (n+1) k) ω-
          β (itoUniformNNTime T (n+1) k) ω)^2 ∂P) atTop (𝓝 0) := by
      have hh := (hpartial (itoUniformNNTime T (n+1) k)
        (itoUniformNNTime_le_end T (n+1) k (Nat.succ_pos n) (by omega))).comp hK
      simpa only [Function.comp_def, he] using hh
    exact actualMeanSquareLimit_weighted_grid_increments P
      (fun m => brownianAggregatePartialSum B u T ((n+1)*(m+1))) β A
      (itoUniformNNTime T (n+1)) (n+1) (fun k m => hpL _ _) (fun k => hβ _)
      (fun k => (hAm _).aestronglyMeasurable) C hC (fun k => hAb _) hl
  obtain ⟨m, hm⟩ := actualMeanSquare_diagonal_selection P
    (fun n m => brownianSubstitutionCoarseApproximation B u A T (n+1) (m+1))
    (fun n => brownianUniformLeftSum β A T (n+1)) hfixed
  have herror := brownianSubstitutionCoarseApproximation_frozen_error_tendsto_meanSquare
    B P hB hind A u hA hu C U hC hU hAb hub T m hc
  have hK : Tendsto (fun n : ℕ => (n+1)*(m n+1)-1) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro n
    change n ≤ (n+1)*(m n+1)-1
    have hh := Nat.mul_le_mul_left (n+1) (show 1≤m n+1 by omega)
    simp only [mul_one] at hh
    omega
  have he (n : ℕ) : (n+1)*(m n+1)-1+1=(n+1)*(m n+1) := by
    have hp := Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos (m n))
    exact Nat.sub_add_cancel hp
  have hPL := hproduct.comp hK
  simp only [Function.comp_def, he] at hPL
  have hcoarse := actualMeanSquareLimit_transfer P
    (fun n ω => ∑ i, brownianUniformLeftSum (B i) (fun r ω => A r ω*u i r ω)
      T ((n+1)*(m n+1)) ω)
    (fun n => brownianSubstitutionCoarseApproximation B u A T (n+1) (m n+1)) J
    (fun n => hProdL _) (fun n => hSL _ _) hJ
    (by simpa only [sub_sq_comm] using herror) hPL
  exact actualMeanSquareLimit_transfer P
    (fun n => brownianSubstitutionCoarseApproximation B u A T (n+1) (m n+1))
    (fun n => brownianUniformLeftSum β A T (n+1)) J
    (fun n => hSL _ _) (fun n => hβS _) hJ hm hcoarse

end
end GinibrePoincare
