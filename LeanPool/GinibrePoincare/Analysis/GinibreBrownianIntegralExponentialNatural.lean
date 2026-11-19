/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralExponentialNatural.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralExponentialDensity

/-!
# Ginibre Brownian integral exponential natural

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianBoundedVector_exponential_integral_exists_normalized`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Actual bounded continuous adapted vector integrands have genuine continuous
 stochastic integrals whose literal exponential density is normalized.
 No integral, uniform-integrability or exponential-martingale certificate is assumed. -/
theorem brownianBoundedVector_exponential_integral_exists_normalized {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (F : ι → ℝ≥0 → Ω → ℝ)
    (hF : ∀ i t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal) t) _ (F i t))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t ω, (∑ i, (F i t ω) ^ 2) ≤ C ^ 2)
    (T : ℝ≥0)
    (hc : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun s => F i s ω) (Set.Icc 0 T)) :
    ∃ M : ι → ℝ≥0 → Ω → ℝ,
      (∀ i, Martingale (M i) (ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal)) P ∧
        (∀ ω, Continuous (fun t => M i t ω)) ∧ (∀ t, MemLp (M i t) 2 P) ∧
        M i 0 =ᵐ[P] (fun _ => 0) ∧
        ∀ t ≤ T, TendstoInMeasure P
          (fun n => brownianUniformLeftSum (B i) (F i) t (n+1)) atTop (M i t)) ∧
      Integrable (brownianVectorExponentialIntegralDensity F T (fun i => M i T)) P ∧
      (∫ ω, brownianVectorExponentialIntegralDensity F T (fun i => M i T) ω ∂P)=1 ∧
      Tendsto (fun n => eLpNorm (brownianVectorExponentialUniformSum B F T n-
        brownianVectorExponentialIntegralDensity F T (fun i => M i T)) 1 P) atTop (𝓝 0) := by
  classical
  have hiB (i : ι) (t : ℝ≥0) (ω : Ω) : ‖F i t ω‖≤C := by
    rw [Real.norm_eq_abs]
    apply abs_le_of_sq_le_sq _ hC
    exact (Finset.single_le_sum (fun j _ => sq_nonneg (F j t ω)) (Finset.mem_univ i)).trans (hb t ω)
  have hex (i : ι) := brownianContinuousIntegral_exists_all_horizons B P hB hind i (F i)
    (hF i) T (hc i) C hC (hiB i)
  choose M hM using hex
  have hFi (i : ι) (t : ℝ≥0) : MemLp (F i t) 2 P := MemLp.of_bound
    ((hF i t).mono ((ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)).le t) le_rfl).aestronglyMeasurable C
    (Eventually.of_forall (hiB i t))
  have hs (i : ι) (n : ℕ) :=
    (brownianUniformLeftSum_memLp_two B P (fun i => (hB i).toIsPreBrownianReal) hind
      i (F i) (hF i) (hFi i) T (n+1)).aestronglyMeasurable
  have hI (i : ι) := hM i |>.2.2.2.2.2 T le_rfl
  have hd := brownianVectorExponentialIntegralDensity_normalized B P
    (fun i => (hB i).toIsPreBrownianReal) hind F hF C hC hb T hc hs
    (fun i => M i T) hI
  refine ⟨M,?_, hd.1, hd.2.2.1, hd.2.2.2⟩
  intro i
  exact ⟨(hM i).1, (hM i).2.1, (hM i).2.2.1, (hM i).2.2.2.1, (hM i).2.2.2.2.2⟩

end
end GinibrePoincare
