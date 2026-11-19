/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralMeanSquareCauchy.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralRefinementBound

/-! Actual Brownian left sums are Cauchy in mean square for continuous bounded adapted coefficients.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem brownianUniformRefinementMesh_tendsto_meanSquare {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℝ≥0 → Ω → ℝ) (hF : ∀ t, Measurable (F t)) (T : ℝ≥0)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => F t ω) (Set.Icc 0 T))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t ∈ Set.Icc 0 T, ∀ ω, ‖F t ω‖ ≤ C) :
    Tendsto (fun q : ℕ×ℕ => ∫ ω, (brownianUniformRefinementMesh F T q.1 q.2 ω)^2 ∂P)
      atTop (𝓝 0) := by
  let a := fun q : ℕ×ℕ => fun k : Fin ((q.1+1)*(q.2+1)) => itoUniformNNTime T (q.1+1)
      (k.val/(q.2+1))
  let b := fun q : ℕ×ℕ => fun k : Fin ((q.1+1)*(q.2+1)) => itoUniformNNTime T (q.2+1)
      (k.val/(q.1+1))
  have ha (q : ℕ×ℕ) (k : Fin ((q.1+1)*(q.2+1))) : a q k ∈ Set.Icc 0 T :=
    (itoUniformNNTime_common_samples_mem T (q.1+1) (q.2+1) k (Nat.succ_pos _) (Nat.succ_pos _)
        k.is_lt).1
  have hb (q : ℕ×ℕ) (k : Fin ((q.1+1)*(q.2+1))) : b q k ∈ Set.Icc 0 T :=
    (itoUniformNNTime_common_samples_mem T (q.1+1) (q.2+1) k (Nat.succ_pos _) (Nat.succ_pos _)
        k.is_lt).2.1
  have hd : Tendsto (fun q : ℕ×ℕ => (T : ℝ)/((q.1 : ℝ)+1)+(T : ℝ)/((q.2 : ℝ)+1)) atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => (T : ℝ)/((n : ℝ)+1)) atTop (𝓝 0) := by
      simpa only [mul_one_div, mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (T : ℝ)
    simpa only [zero_add, Function.comp_apply] using (hh.comp (show Tendsto Prod.fst (atTop : Filter
        (ℕ×ℕ)) atTop from by simpa only [← prod_atTop_atTop_eq] using tendsto_fst)).add (hh.comp
            (show Tendsto Prod.snd (atTop : Filter (ℕ×ℕ)) atTop from by
                simpa only [← prod_atTop_atTop_eq] using tendsto_snd))
  exact brownianCoefficientSampleMesh_tendsto_meanSquare P (fun q : ℕ×ℕ => Fin ((q.1+1)*(q.2+1)))
    F hF T a b ha hb _ hd (fun q k => by
      simpa only [Nat.cast_add, Nat.cast_one] using
        itoUniformNNTime_two_coarse_dist_le T (q.1+1) (q.2+1) k (Nat.succ_pos _) (Nat.succ_pos _))
            hc C hC hbound

theorem brownianUniformLeftSum_tendsto_difference_meanSquare {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (T : ℝ≥0)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => F t ω) (Set.Icc 0 T))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t ∈ Set.Icc 0 T, ∀ ω, ‖F t ω‖ ≤ C) :
    Tendsto (fun q : ℕ×ℕ => ∫ ω,
      (brownianUniformLeftSum (B j) F T (q.1+1) ω-brownianUniformLeftSum (B j) F T (q.2+1) ω)^2 ∂P)
      atTop (𝓝 0) := by
  have := Fintype.ofFinite ι
  have hle (q : ℕ×ℕ) :
      (∫ ω, (brownianUniformLeftSum (B j) F T (q.1+1) ω-brownianUniformLeftSum (B j) F T (q.2+1)
          ω)^2 ∂P) ≤
        (T : ℝ)*(∫ ω, (brownianUniformRefinementMesh F T q.1 q.2 ω)^2 ∂P) :=
    brownianUniformLeftSum_difference_secondMoment_le_mesh B P hB hind j F hF hFi T q.1 q.2
  apply squeeze_zero (fun q => integral_nonneg fun ω => sq_nonneg _) hle
  simpa only [mul_zero] using
    (brownianUniformRefinementMesh_tendsto_meanSquare P F (fun t => (hF t).mono
      ((ginibreBrownianAugmentedFiltration B P hB).le t) le_rfl) T hc C hC hbound).const_mul (T : ℝ)

end
end GinibrePoincare
