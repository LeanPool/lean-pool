/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralSubstitutionError.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralSubstitutionRefinement
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralSubstitutionMesh

/-!
# Ginibre Brownian integral substitution error

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianSubstitutionCoarseApproximation_frozen_error_tendsto_meanSquare`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem brownianSubstitutionCoarseApproximation_frozen_error_tendsto_meanSquare
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (A : ℝ≥0 → Ω → ℝ) (u : ι → ℝ≥0 → Ω → ℝ)
    (hA : ∀ r, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB r) _ (A r))
    (hu : ∀ i r, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB r) _ (u i r))
    (C U : ℝ) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hAb : ∀ r ω, ‖A r ω‖ ≤ C) (hub : ∀ i r ω, ‖u i r ω‖ ≤ U)
    (T : ℝ≥0) (m : ℕ → ℕ)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun r => A r ω) (Set.Icc 0 T)) :
    Tendsto (fun n => ∫ ω,
      (brownianSubstitutionCoarseApproximation B u A T (n+1) (m n+1) ω-
        ∑ i, brownianUniformLeftSum (B i) (fun r ω => A r ω*u i r ω)
          T ((n+1)*(m n+1)) ω)^2 ∂P) atTop (𝓝 0) := by
  classical
  have hAm (r : ℝ≥0) : Measurable (A r) := (hA r).mono
    ((ginibreBrownianAugmentedFiltration B P hB).le r) le_rfl
  have hum (i : ι) (r : ℝ≥0) : Measurable (u i r) := (hu i r).mono
    ((ginibreBrownianAugmentedFiltration B P hB).le r) le_rfl
  have hAi (r : ℝ≥0) : MemLp (A r) 2 P := MemLp.of_bound
    (hAm r).aestronglyMeasurable C (Eventually.of_forall (hAb r))
  let E : ι → ℕ → Ω → ℝ := fun i n ω =>
    ∑ k : Fin ((n+1)*(m n+1)),
      (A (itoUniformNNTime T (n+1) (k.val/(m n+1))) ω-
        A (itoUniformNNTime T ((n+1)*(m n+1)) k) ω)*
      u i (itoUniformNNTime T ((n+1)*(m n+1)) k) ω*
      (B i (itoUniformNNTime T ((n+1)*(m n+1)) (k.val+1)) ω-
        B i (itoUniformNNTime T ((n+1)*(m n+1)) k) ω)
  have hEi (i : ι) (n : ℕ) : MemLp (E i n) 2 P := by
    apply memLp_finsetSum
    intro k hk
    let a := itoUniformNNTime T ((n+1)*(m n+1)) k
    let b := itoUniformNNTime T ((n+1)*(m n+1)) (k.val+1)
    let c := itoUniformNNTime T (n+1) (k.val/(m n+1))
    let G := fun ω => (A c ω-A a ω)*u i a ω
    have hG : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB a) _ G :=
      (((hA c).mono ((ginibreBrownianAugmentedFiltration B P hB).mono
        (itoUniformNNTime_coarse_le_fine T (n+1) (m n+1) k (Nat.succ_pos _))) le_rfl).sub (hA
            a)).mul (hu i a)
    have hGi : MemLp G 2 P := by
      simpa only [G, mul_comm, Pi.sub_apply] using actualBoundedMultiplier_memLp_two P
        (u i a) _ (hum i a).aestronglyMeasurable ((hAi c).sub (hAi a)) U (hub i a)
    have hh := brownianFrozenStep_memLp_two B P hB hind i G a b b hG hGi
    have he : brownianFrozenStep (B i) G a b b = (fun ω => G ω*(B i b ω-B i a ω)) := by
      funext ω
      simp [brownianFrozenStep, a, b, max_eq_right (itoUniformNNTime_mono T _ (Nat.le_succ k.val))]
    rw [he] at hh
    exact hh
  have hmesh := brownianFrozenMultiplierMesh_tendsto_meanSquare P A hAm T m hc C hC hAb
  have hEl (i : ι) : Tendsto (fun n => ∫ ω, (E i n ω)^2 ∂P) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _)
      (fun n => brownianFrozenMultiplier_difference_secondMoment_le B P hB hind i A (u i)
        hA (hu i) C U hC hU hAb (hub i) T (n+1) (m n+1) (Nat.succ_pos _) (Nat.succ_pos _))
    simpa only [mul_zero] using hmesh.const_mul ((T : ℝ)*U^2)
  have hh := actualMeanSquareZero_finset_sum P Finset.univ E hEi hEl
  have he : (fun n ω => ∑ i, E i n ω) = (fun n ω =>
      brownianSubstitutionCoarseApproximation B u A T (n+1) (m n+1) ω-
        ∑ i, brownianUniformLeftSum (B i) (fun r ω => A r ω*u i r ω)
          T ((n+1)*(m n+1)) ω) := by
    funext n ω
    rw [brownianSubstitutionCoarseApproximation_refinement B u A T (n+1) (m n+1) (Nat.succ_pos _) ω]
    simp only [E, brownianUniformLeftSum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hepoint (n : ℕ) (ω : Ω) := congrFun (congrFun he n) ω
  simp_rw [hepoint] at hh
  exact hh

end
end GinibrePoincare
