/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralPartialCauchy.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralPartialGeometry
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! Conditional contraction makes the actual continuous partial sums L² Cauchy at every time. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem real_condExp_square_integral_le {Ω : Type*} [mAmbient : MeasurableSpace Ω]
    (P : Measure Ω) (m : MeasurableSpace Ω) (hm : m ≤ mAmbient) [SigmaFinite (P.trim hm)]
    (f : Ω → ℝ) (hf : MemLp f 2 P) :
    (∫ ω, (P[f | m] ω)^2 ∂P) ≤ ∫ ω, (f ω)^2 ∂P := by
  have hi : Integrable (fun ω => ‖f ω‖^(2 : ℝ)) P := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hf.integrable_sq
  have hle := Integrable.norm_condExp_rpow_le (f := f) (m := m) (μ := P) (p := 2) (by norm_num) hi
  have hj : (fun ω => (P[f | m] ω)^2) ≤ᵐ[P] P[(fun ω => (f ω)^2) | m] := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hle
  calc
    _ ≤ ∫ ω, P[(fun ω => (f ω)^2) | m] ω ∂P :=
      integral_mono_ae ((hf.condExp (by norm_num)).integrable_sq) integrable_condExp hj
    _ = _ := integral_condExp hm

theorem brownianUniformPartialSum_memLp_two {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (T : ℝ≥0) (N : ℕ) (t : ℝ≥0) :
    MemLp (brownianUniformPartialSum (B j) F T N t) 2 P := by
  have := Fintype.ofFinite ι
  convert! memLp_finsetSum (Finset.range N) (fun i _ =>
    brownianFrozenStep_memLp_two B P hB hind j (F (itoUniformNNTime T N i))
      (itoUniformNNTime T N i) (itoUniformNNTime T N (i+1)) t (hF _) (hFi _)) using 1

theorem brownianUniformPartialSum_difference_secondMoment_le_terminal {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (T : ℝ≥0) (N M : ℕ) (t : ℝ≥0) (ht : t ≤ T) :
    (∫ ω, (brownianUniformPartialSum (B j) F T N t ω-brownianUniformPartialSum (B j) F T M t ω)^2
        ∂P) ≤
      ∫ ω, (brownianUniformLeftSum (B j) F T N ω-brownianUniformLeftSum (B j) F T M ω)^2 ∂P := by
  have := Fintype.ofFinite ι
  have hm := (brownianUniformPartialSum_martingale B P hB hind j F hF hFi T N).sub
    (brownianUniformPartialSum_martingale B P hB hind j F hF hFi T M)
  have hc := hm.condExp_ae_eq ht
  have hf : MemLp (fun ω => brownianUniformLeftSum (B j) F T N ω-brownianUniformLeftSum (B j) F T M
      ω) 2 P :=
    (brownianUniformLeftSum_memLp_two B P hB hind j F hF hFi T N).sub
      (brownianUniformLeftSum_memLp_two B P hB hind j F hF hFi T M)
  have hterminal : (brownianUniformPartialSum (B j) F T N-brownianUniformPartialSum (B j) F T M) T =
      fun ω => brownianUniformLeftSum (B j) F T N ω-brownianUniformLeftSum (B j) F T M ω := by
    funext ω
    simp only [Pi.sub_apply, brownianUniformPartialSum_terminal]
  rw [hterminal] at hc
  calc
    _ = ∫ ω, (P[(fun ω => brownianUniformLeftSum (B j) F T N ω-brownianUniformLeftSum (B j) F T M ω)
        |
        ginibreBrownianAugmentedFiltration B P hB t] ω)^2 ∂P := by
      apply integral_congr_ae
      filter_upwards [hc] with ω hω
      simpa only [Pi.sub_apply] using congrArg (fun x : ℝ => x^2) hω.symm
    _ ≤ _ := real_condExp_square_integral_le P _ ((ginibreBrownianAugmentedFiltration B P hB).le t)
        _ hf

theorem brownianUniformPartialSum_tendsto_difference_meanSquare {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (T t : ℝ≥0) (ht : t ≤ T)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun s => F s ω) (Set.Icc 0 T))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ s ∈ Set.Icc 0 T, ∀ ω, ‖F s ω‖ ≤ C) :
    Tendsto (fun q : ℕ×ℕ => ∫ ω,
      (brownianUniformPartialSum (B j) F T (q.1+1) t ω-brownianUniformPartialSum (B j) F T (q.2+1) t
          ω)^2 ∂P)
      atTop (𝓝 0) := by
  have := Fintype.ofFinite ι
  have hle (q : ℕ×ℕ) :
      (∫ ω, (brownianUniformPartialSum (B j) F T (q.1+1) t ω-brownianUniformPartialSum (B j) F T
          (q.2+1) t ω)^2 ∂P) ≤
        ∫ ω, (brownianUniformLeftSum (B j) F T (q.1+1) ω-brownianUniformLeftSum (B j) F T (q.2+1)
            ω)^2 ∂P :=
    brownianUniformPartialSum_difference_secondMoment_le_terminal B P hB hind j F hF hFi T _ _ t ht
  exact squeeze_zero (fun q => integral_nonneg fun ω => sq_nonneg _) hle
    (brownianUniformLeftSum_tendsto_difference_meanSquare B P hB hind j F hF hFi T hc C hC hbound)

end
end GinibrePoincare
