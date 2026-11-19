/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralSubstitutionNatural.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralSubstitution
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticUnitFieldPartialMeanSquare

/-!
# Ginibre Brownian integral substitution natural

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianUnitIntegral_bounded_substitution_of_horizon_limits`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Aggregation step: terminal mean-square limits `m i` of the coordinate Riemann sums
identify any in-probability limit `J` of their sum, which is then square integrable and a
mean-square limit. -/
theorem brownianAggregateUniformSum_meanSquare_of_coordinate_limits
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (F : ι → ℝ≥0 → Ω → ℝ)
    (hF : ∀ i r, @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) r) _ (F i r))
    (C : ℝ) (hb : ∀ i r ω, ‖F i r ω‖ ≤ C) (T : ℝ≥0) (m : ι → Ω → ℝ)
    (hmL : ∀ i, MemLp (m i) 2 P)
    (hmS : ∀ i, Tendsto (fun k => ∫ ω,
      (brownianUniformLeftSum (B i) (F i) T (k + 1) ω - m i ω) ^ 2 ∂P) atTop (𝓝 0))
    (J : Ω → ℝ)
    (hlim : TendstoInMeasure P (fun k ω => ∑ i, brownianUniformLeftSum (B i) (F i) T (k + 1) ω)
      atTop J) :
    MemLp J 2 P ∧ Tendsto (fun k => ∫ ω,
      ((∑ i, brownianUniformLeftSum (B i) (F i) T (k + 1) ω) - J ω) ^ 2 ∂P) atTop (𝓝 0) := by
  classical
  have hFi (i : ι) (r : ℝ≥0) : MemLp (F i r) 2 P := MemLp.of_bound
    (((hF i r).mono ((ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)).le r) le_rfl).aestronglyMeasurable)
    C (Eventually.of_forall (hb i r))
  have hSL (i : ι) (k : ℕ) : MemLp (brownianUniformLeftSum (B i) (F i) T (k+1)) 2 P :=
    brownianUniformLeftSum_memLp_two B P (fun i => (hB i).toIsPreBrownianReal) hind
      i (F i) (hF i) (hFi i) T (k+1)
  have hsum := itoTendstoInMeasure_finset_sum P Finset.univ
    (fun i k => brownianUniformLeftSum (B i) (F i) T (k+1)) m
    (fun i k => (hSL i k).aestronglyMeasurable)
    (fun i => ginibre_tendstoInMeasure_of_meanSquare P _ _
      (fun k => ((hSL i k).sub (hmL i)).integrable_sq) (hmS i))
  have he := tendstoInMeasure_ae_unique hsum hlim
  have hJL : MemLp (fun ω => ∑ i, m i ω) 2 P := memLp_finsetSum _ (fun i _ => hmL i)
  refine ⟨hJL.ae_eq he, ?_⟩
  have hh := actualMeanSquareZero_finset_sum P Finset.univ
    (fun i k ω => brownianUniformLeftSum (B i) (F i) T (k+1) ω - m i ω)
    (fun i k => (hSL i k).sub (hmL i)) hmS
  have hEq (k : ℕ) : (∫ ω,
      ((∑ i, brownianUniformLeftSum (B i) (F i) T (k+1) ω)-J ω)^2 ∂P) =
      ∫ ω, (∑ i, (brownianUniformLeftSum (B i) (F i) T (k+1) ω - m i ω))^2 ∂P := by
    apply integral_congr_ae
    filter_upwards [he] with ω hω
    rw [← hω, Finset.sum_sub_distrib]
  simp_rw [hEq]
  exact hh

theorem brownianAggregateUniformSum_meanSquare_of_horizon_limit
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (F : ι → ℝ≥0 → Ω → ℝ)
    (hF : ∀ i r, @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) r) _ (F i r))
    (T : ℝ≥0) (hc : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun r => F i r ω) (Set.Icc 0 T))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ i r ω, ‖F i r ω‖ ≤ C)
    (J : Ω → ℝ)
    (hlim : TendstoInMeasure P (fun k ω => ∑ i, brownianUniformLeftSum (B i) (F i) T (k + 1) ω)
      atTop J) :
    MemLp J 2 P ∧ Tendsto (fun k => ∫ ω,
      ((∑ i, brownianUniformLeftSum (B i) (F i) T (k+1) ω)-J ω)^2 ∂P) atTop (𝓝 0) := by
  classical
  have hex (i : ι) := brownianContinuousIntegral_exists B P hB hind i (F i) (hF i)
    T (hc i) C hC (hb i)
  choose M hM hMC hML hM0 hMP hMS using hex
  exact brownianAggregateUniformSum_meanSquare_of_coordinate_limits B P hB hind F hF C hb T
    (fun i => M i T) (fun i => hML i T)
    (fun i => by simpa only [brownianUniformPartialSum_terminal] using hMS i T) J hlim

/-- Genuine stochastic substitution under natural bounded continuous
unit-field assumptions, with integral values specified only by actual horizon
limits in probability. Mean-square limits and refinement control are derived. -/
theorem brownianUnitIntegral_bounded_substitution_of_horizon_limits
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℝ≥0 → Ω → EuclideanSpace ℝ ι)
    (hu : ∀ r, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) r) _ (u r))
    (hunit : ∀ r ω, ‖u r ω‖ = 1) (huc : ∀ᵐ ω ∂P, Continuous (fun r => u r ω))
    (A : ℝ≥0 → Ω → ℝ)
    (hA : ∀ r, @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) r) _ (A r))
    (C : ℝ) (hC : 0 ≤ C) (hAb : ∀ r ω, ‖A r ω‖ ≤ C)
    (T : ℝ≥0) (hc : ∀ᵐ ω ∂P, ContinuousOn (fun r => A r ω) (Set.Icc 0 T))
    (β : ℝ≥0 → Ω → ℝ) (hβ : ∀ r, MemLp (β r) 2 P)
    (hβlim : ∀ r, TendstoInMeasure P (fun k ω => ∑ i,
      brownianUniformLeftSum (B i) (fun s ω => u s ω i) r (k + 1) ω) atTop (β r))
    (J : Ω → ℝ)
    (hJlim : TendstoInMeasure P (fun k ω => ∑ i,
      brownianUniformLeftSum (B i) (fun r ω => A r ω * u r ω i) T (k + 1) ω) atTop J) :
    Tendsto (fun k => ∫ ω, (brownianUniformLeftSum β A T (k+1) ω-J ω)^2 ∂P)
      atTop (𝓝 0) := by
  classical
  have hum (i : ι) (r : ℝ≥0) : @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) r) _
      (fun ω => u r ω i) := (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i).measurable.comp (hu r)
  have hub (i : ι) (r : ℝ≥0) (ω : Ω) : ‖u r ω i‖≤1 := by
    simpa only [hunit r ω] using PiLp.norm_apply_le (u r ω) i
  have hProd := brownianAggregateUniformSum_meanSquare_of_horizon_limit B P hB hind
    (fun i r ω => A r ω*u r ω i) (fun i r => (hA r).mul (hum i r)) T
    (fun i => by
      filter_upwards [hc, huc] with ω hω hωu
      exact hω.mul (((PiLp.continuous_apply 2 (fun _ : ι => ℝ) i).comp hωu).continuousOn))
    C hC (fun i r ω => by
      rw [norm_mul]
      calc
        ‖A r ω‖*‖u r ω i‖ ≤ C*‖u r ω i‖ :=
          mul_le_mul_of_nonneg_right (hAb r ω) (norm_nonneg _)
        _ ≤ C := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hub i r ω) hC) J hJlim
  exact brownianIntegral_bounded_substitution_meanSquare B P
    (fun i => (hB i).toIsPreBrownianReal) hind A (fun i r ω => u r ω i) hA hum
    C 1 hC (by norm_num) hAb hub T hc β hβ
    (fun r hr => ginibreUnitField_partial_meanSquare_of_horizon_limits
      B P hB hind u hu hunit huc β hβlim T r hr) J hProd.1 hProd.2

end
end GinibrePoincare
