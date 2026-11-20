/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryBrownianDyadicGaussianMoments.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianDyadicGaussianFinite
public import Mathlib.Probability.Moments.Variance
/-!
# Alternative Bakry Emery Brownian dyadic Gaussian moments

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryBrownianFiniteDyadicLinear_law`, `bakryBrownianFiniteDyadicLinear_covariance`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The linear form `∑ i, c i * sample i` of a dyadic sample, over the coordinates of the
levels below `N`. -/
def bakryBrownianFiniteDyadicLinear (N : ℕ) (c : BakryBrownianFiniteDyadicIndex N → ℝ)
    (sample : BakryBrownianDyadicSample) : ℝ :=
  ∑ i, c i * sample (bakryBrownianFiniteDyadicEmbed N i)

theorem bakryBrownianFiniteDyadicLinear_gaussian (N : ℕ)
    (c : BakryBrownianFiniteDyadicIndex N → ℝ) :
    HasGaussianLaw (bakryBrownianFiniteDyadicLinear N c) bakryBrownianDyadicMeasure := by
  let L : (BakryBrownianFiniteDyadicIndex N → ℝ) →L[ℝ] ℝ :=
    ∑ i, c i • ContinuousLinearMap.proj i
  convert (bakryBrownianFiniteDyadic_coordinates_gaussian N).map_fun L using 1
  funext sample
  simp only [L, bakryBrownianFiniteDyadicLinear, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

theorem bakryBrownianFiniteDyadicLinear_mean (N : ℕ)
    (c : BakryBrownianFiniteDyadicIndex N → ℝ) :
    (∫ sample, bakryBrownianFiniteDyadicLinear N c sample ∂bakryBrownianDyadicMeasure) = 0 := by
  have hc (i : BakryBrownianFiniteDyadicIndex N) : Integrable
      (fun sample : BakryBrownianDyadicSample => c i * sample (bakryBrownianFiniteDyadicEmbed N i))
      bakryBrownianDyadicMeasure :=
    ((bakryBrownianDyadic_coordinate_law _).hasGaussianLaw.integrable).const_mul _
  unfold bakryBrownianFiniteDyadicLinear
  rw [integral_finsetSum _ (fun i _ => hc i)]
  apply Finset.sum_eq_zero
  intro i hi
  rw [integral_const_mul, (bakryBrownianDyadic_coordinate_law _).integral_eq,
      integral_id_gaussianReal, mul_zero]

theorem bakryBrownianFiniteDyadicLinear_variance (N : ℕ)
    (c : BakryBrownianFiniteDyadicIndex N → ℝ) :
    Var[bakryBrownianFiniteDyadicLinear N c; bakryBrownianDyadicMeasure] = ∑ i, (c i)^2 := by
  let X := fun i (sample : BakryBrownianDyadicSample) => c i * sample
      (bakryBrownianFiniteDyadicEmbed N i)
  have hMem (i : BakryBrownianFiniteDyadicIndex N) : MemLp (X i) 2 bakryBrownianDyadicMeasure :=
    ((bakryBrownianDyadic_coordinate_law _).hasGaussianLaw.memLp_two).const_mul _
  have hInd := (bakryBrownianDyadic_coordinates_independent.precomp
    (bakryBrownianFiniteDyadicEmbed_injective N)).comp (fun i x => c i*x) (fun i => by fun_prop)
  have he : bakryBrownianFiniteDyadicLinear N c = ∑ i, X i := by
    funext sample
    simp only [bakryBrownianFiniteDyadicLinear, Finset.sum_apply, X]
  rw [he, IndepFun.variance_sum (fun i _ => hMem i) (fun i _ j _ hij => hInd.indepFun hij)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [variance_const_mul, (bakryBrownianDyadic_coordinate_law _).variance_eq,
    variance_id_gaussianReal]
  simp

theorem bakryBrownianFiniteDyadicLinear_law (N : ℕ)
    (c : BakryBrownianFiniteDyadicIndex N → ℝ) :
    HasLaw (bakryBrownianFiniteDyadicLinear N c)
      (gaussianReal 0 (∑ i, (c i)^2).toNNReal) bakryBrownianDyadicMeasure := by
  have hg := bakryBrownianFiniteDyadicLinear_gaussian N c
  refine ⟨hg.aemeasurable,?_⟩
  rw [hg.map_eq_gaussianReal, bakryBrownianFiniteDyadicLinear_mean,
      bakryBrownianFiniteDyadicLinear_variance]

theorem bakryBrownianFiniteDyadicLinear_covariance (N : ℕ)
    (c d : BakryBrownianFiniteDyadicIndex N → ℝ) :
    cov[bakryBrownianFiniteDyadicLinear N c, bakryBrownianFiniteDyadicLinear N d;
      bakryBrownianDyadicMeasure] = ∑ i, c i*d i := by
  have he := variance_add (bakryBrownianFiniteDyadicLinear_gaussian N c).memLp_two
    (bakryBrownianFiniteDyadicLinear_gaussian N d).memLp_two
  have hAdd : bakryBrownianFiniteDyadicLinear N (c+d) =
      bakryBrownianFiniteDyadicLinear N c + bakryBrownianFiniteDyadicLinear N d := by
    funext sample
    simp only [bakryBrownianFiniteDyadicLinear, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [← hAdd, bakryBrownianFiniteDyadicLinear_variance,
    bakryBrownianFiniteDyadicLinear_variance, bakryBrownianFiniteDyadicLinear_variance] at he
  have hp : (∑ i, (c i+d i)^2) = (∑ i, (c i)^2)+2*(∑ i, c i*d i)+(∑ i, (d i)^2) := by
    simp only [add_sq, Finset.sum_add_distrib, mul_assoc,← Finset.mul_sum]
  change (∑ i, (c i+d i)^2) = _ at he
  linarith

end
end GinibrePoincare
