/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGaussianTiltVectorLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianTiltVector
public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianTiltLaw
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Basic.ENNReal.BigOperators

/-!
# Brownian integral Gaussian tilt vector law

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `gaussianReal_pi_exponential_tilt_centered`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- Exact simultaneous tilt of every independent Gaussian coordinate. -/
theorem gaussianReal_pi_exponential_tilt {ι : Type*} [Fintype ι]
    (h : ι → ℝ) (v : ℝ≥0) :
    (Measure.pi (fun _ : ι => gaussianReal 0 v)).withDensity
      (fun x => ENNReal.ofReal (gaussianVectorExponentialTilt h v x)) =
      Measure.pi (fun i => gaussianReal (h i*(v : ℝ)) v) := by
  classical
  apply (Measure.pi_eq (μ:=fun i => gaussianReal (h i*(v : ℝ)) v) ?_).symm
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  have hInt (i : ι) : Integrable (gaussianExponentialTilt (h i) v) ((gaussianReal 0 v).restrict (s
      i)) :=
    (gaussianExponentialTilt_integrable (h i) v).mono_measure Measure.restrict_le_self
  have hprod : Integrable (gaussianVectorExponentialTilt h v)
      (Measure.pi (fun i => (gaussianReal 0 v).restrict (s i))) := Integrable.fintype_prod_dep hInt
  rw [← ofReal_integral_eq_lintegral_ofReal hprod
    (Eventually.of_forall (gaussianVectorExponentialTilt_nonneg h v))]
  unfold gaussianVectorExponentialTilt
  rw [integral_fintype_prod_eq_prod]
  have hp : ∀ i ∈ (Finset.univ : Finset ι),
      0≤∫ x in s i, gaussianExponentialTilt (h i) v x ∂gaussianReal 0 v := by
    intro i hi
    exact integral_nonneg (fun x => (show 0≤gaussianExponentialTilt (h i) v x from (Real.exp_pos
        _).le))
  rw [ENNReal.ofReal_prod_of_nonneg hp]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← gaussianReal_exponential_tilt (h i) v, withDensity_apply _ (hs i),
    ← ofReal_integral_eq_lintegral_ofReal (hInt i)
      (Eventually.of_forall fun x => (Real.exp_pos _).le)]

/-- Under the true Gaussian RN tilt, subtracting the predictable drift restores
all centered independent coordinate laws. -/
theorem gaussianReal_pi_exponential_tilt_centered {ι : Type*} [Fintype ι]
    (h : ι → ℝ) (v : ℝ≥0) :
    ((Measure.pi (fun _ : ι => gaussianReal 0 v)).withDensity
      (fun x => ENNReal.ofReal (gaussianVectorExponentialTilt h v x))).map
      (fun x i => x i-h i*(v : ℝ)) = Measure.pi (fun _ : ι => gaussianReal 0 v) := by
  rw [gaussianReal_pi_exponential_tilt]
  have hmap (i : ι) : (gaussianReal (h i*(v : ℝ)) v).map
      (fun x : ℝ => x-h i*(v : ℝ)) = gaussianReal 0 v := by
    simpa only [sub_eq_add_neg, neg_mul, add_neg_cancel] using
      (gaussianReal_map_add_const (μ:=h i*(v : ℝ)) (v:=v) (-h i*(v : ℝ)))
  let : ∀ i, IsProbabilityMeasure ((gaussianReal (h i*(v : ℝ)) v).map
      (fun x : ℝ => x-h i*(v : ℝ))) := fun i => by rw [hmap]; infer_instance
  rw [Measure.pi_map_pi (fun i => (show Measurable (fun x : ℝ => x-h i*(v : ℝ)) by
      fun_prop).aemeasurable)]
  simp_rw [hmap]

end
end GinibrePoincare
