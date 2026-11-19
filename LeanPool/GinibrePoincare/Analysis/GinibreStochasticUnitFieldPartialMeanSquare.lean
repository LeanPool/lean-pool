/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticUnitFieldPartialMeanSquare.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticUnitFieldGlobalIntegral
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralSubstitutionFinite

/-! Genuine mean-square partial-sum convergence of the global unit-field
integral, derived from its actual original horizon limits. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreUnitField_partial_meanSquare_of_horizon_limits
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℝ≥0 → Ω → EuclideanSpace ℝ ι)
    (hu : ∀ t, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) t) _ (u t))
    (hunit : ∀ t ω, ‖u t ω‖ = 1)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => u t ω))
    (I : ℝ≥0 → Ω → ℝ)
    (hI : ∀ t, TendstoInMeasure P (fun k ω =>
      ∑ i, brownianUniformLeftSum (B i) (fun s ω => u s ω i) t (k + 1) ω) atTop (I t))
    (T t : ℝ≥0) (ht : t ≤ T) :
    Tendsto (fun k => ∫ ω,
      ((∑ i, brownianUniformPartialSum (B i) (fun s ω => u s ω i) T (k+1) t ω)-I t ω)^2 ∂P)
      atTop (𝓝 0) := by
  classical
  classical
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  let A := fun i s ω => u s ω i
  have hA (i : ι) (s : ℝ≥0) : @Measurable Ω ℝ (F s) _ (A i s) :=
    (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i).measurable.comp (hu s)
  have hb (i : ι) (s : ℝ≥0) (ω : Ω) : ‖A i s ω‖ ≤ 1 := by
    simpa only [A, hunit s ω] using PiLp.norm_apply_le (u s ω) i
  have hAc (i : ι) : ∀ᵐ ω ∂P, ContinuousOn (fun s => A i s ω) (Icc 0 T) :=
    hc.mono (fun ω hω => ((PiLp.continuous_apply 2 (fun _ : ι => ℝ) i).comp hω).continuousOn)
  have hAL (i : ι) (s : ℝ≥0) : MemLp (A i s) 2 P := MemLp.of_bound
    ((hA i s).mono (F.le s) le_rfl).aestronglyMeasurable 1 (Eventually.of_forall (hb i s))
  have hex (i : ι) := brownianContinuousIntegral_exists B P hB hind i (A i) (hA i)
    T (hAc i) 1 (by norm_num) (hb i)
  choose M hM hMC hML hM0 hMP hMS using hex
  have hH (i : ι) : TendstoInMeasure P (fun k => brownianUniformLeftSum (B i) (A i) t (k+1)) atTop
      (M i t) :=
    (brownianContinuousIntegral_horizon_limit B P (fun i => (hB i).toIsPreBrownianReal) hind
      i (A i) (hA i) T t ht (hAc i) 1 (by norm_num) (hb i) (M i t) (hML i t) (hMS i t)).2
  have hSL (i : ι) (k : ℕ) : MemLp (brownianUniformLeftSum (B i) (A i) t (k+1)) 2 P :=
    brownianUniformLeftSum_memLp_two B P (fun i => (hB i).toIsPreBrownianReal) hind
      i (A i) (hA i) (hAL i) t (k+1)
  have hPL (i : ι) (k : ℕ) : MemLp (brownianUniformPartialSum (B i) (A i) T (k+1) t) 2 P :=
    brownianUniformPartialSum_memLp_two B P (fun i => (hB i).toIsPreBrownianReal) hind
      i (A i) (hA i) (hAL i) T (k+1) t
  have hsum := itoTendstoInMeasure_finset_sum P Finset.univ
    (fun i k => brownianUniformLeftSum (B i) (A i) t (k+1)) (fun i => M i t)
    (fun i k => (hSL i k).aestronglyMeasurable) hH
  have he := tendstoInMeasure_ae_unique hsum (hI t)
  have hz := actualMeanSquareZero_finset_sum P Finset.univ
    (fun i k ω => brownianUniformPartialSum (B i) (A i) T (k+1) t ω-M i t ω)
    (fun i k => (hPL i k).sub (hML i t)) (fun i => hMS i t)
  have hEq (k : ℕ) : (∫ ω,
      ((∑ i, brownianUniformPartialSum (B i) (fun s ω => u s ω i) T (k+1) t ω)-I t ω)^2 ∂P) =
      ∫ ω, (∑ i, (brownianUniformPartialSum (B i) (A i) T (k+1) t ω-M i t ω))^2 ∂P := by
    apply integral_congr_ae
    filter_upwards [he] with ω hω
    rw [← hω, Finset.sum_sub_distrib]
  simp_rw [hEq]
  exact hz
end
end GinibrePoincare
