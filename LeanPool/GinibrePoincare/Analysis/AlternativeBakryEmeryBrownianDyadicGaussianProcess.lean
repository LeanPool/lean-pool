/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryBrownianDyadicGaussianProcess.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianDyadicGaussianPartial
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianDyadicGaussianLimit
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianDyadicCovariance
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
/-!
# Alternative Bakry Emery Brownian dyadic Gaussian process

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryBrownianMinQuadratic_nonneg`, `bakryBrownianDyadicPath_isGaussianProcess`,
`bakryBrownianDyadicPath_mean`, `bakryBrownianDyadicPath_covariance`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous paths `C(Icc 0 1, ℝ)`, used locally in this file. -/
local instance bakryDyadicGaussianProcessPathMeasurable :
    MeasurableSpace C(Icc (0 : ℝ) 1, ℝ) := borel _
local instance bakryDyadicGaussianProcess_pathBorel :
    BorelSpace C(Icc (0 : ℝ) 1, ℝ) := ⟨rfl⟩

/-- The min-covariance quadratic form obtained from the actual dyadic
coefficient construction. -/
def bakryBrownianMinQuadratic {ι : Type*} [Fintype ι]
    (t : ι → Icc (0 : ℝ) 1) (c : ι → ℝ) : ℝ :=
  ∑ a, ∑ b, c a*c b*min (t a : ℝ) (t b : ℝ)

theorem bakryBrownianDyadicQuadraticKernel_tendsto {ι : Type*} [Fintype ι]
    (t : ι → Icc (0 : ℝ) 1) (c : ι → ℝ) :
    Tendsto (fun N => bakryBrownianDyadicQuadraticKernel N t c) atTop
      (𝓝 (bakryBrownianMinQuadratic t c)) := by
  change Tendsto (fun N => ∑ a, ∑ b, c a*c b*bakryBrownianDyadicKernel N (t a) (t b))
    atTop (𝓝 (∑ a, ∑ b, c a*c b*min (t a : ℝ) (t b : ℝ)))
  apply tendsto_finsetSum
  intro a ha
  apply tendsto_finsetSum
  intro b hb
  exact tendsto_const_nhds.mul (bakryBrownianDyadicKernel_tendsto (t a) (t b))

theorem bakryBrownianMinQuadratic_nonneg {ι : Type*} [Fintype ι]
    (t : ι → Icc (0 : ℝ) 1) (c : ι → ℝ) : 0 ≤ bakryBrownianMinQuadratic t c := by
  apply ge_of_tendsto (bakryBrownianDyadicQuadraticKernel_tendsto t c)
  apply Eventually.of_forall
  intro N
  have he := bakryBrownianDyadicLinearWeights_normSq N t c
  simp_rw [bakryBrownianDyadicWeights_inner] at he
  change (∑ i, (bakryBrownianDyadicLinearWeights N t c i)^2) =
    bakryBrownianDyadicQuadraticKernel N t c at he
  rw [← he]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Genuine complete unit-interval finite linear-combination law, derived
from actual uniform convergence and the internally proved tent covariance. -/
theorem bakryBrownianDyadicPath_linear_law {ι : Type*} [Fintype ι]
    (t : ι → Icc (0 : ℝ) 1) (c : ι → ℝ) :
    HasLaw (fun sample : BakryBrownianDyadicSample =>
      ∑ a, c a*bakryBrownianDyadicPath sample (t a))
      (gaussianReal 0 (bakryBrownianMinQuadratic t c).toNNReal) bakryBrownianDyadicMeasure := by
  have hMeas : AEMeasurable (fun sample : BakryBrownianDyadicSample =>
      ∑ a, c a*bakryBrownianDyadicPath sample (t a)) bakryBrownianDyadicMeasure := by
    convert (Finset.aemeasurable_sum Finset.univ
      (fun a ha => ((continuous_eval_const (t a)).measurable.comp_aemeasurable
        bakryBrownianDyadicPath_aemeasurable).const_mul (c a))) using 1
    ext sample
    simp only [Finset.sum_apply, Function.comp_def]
  apply bakryBrownian_centered_gaussian_limit bakryBrownianDyadicMeasure
    (fun N sample => ∑ a, c a*bakryBrownianDyadicPartialPath N sample (t a))
    _ (fun N => (bakryBrownianDyadicQuadraticKernel N t c).toNNReal)
    _ (fun N => bakryBrownianDyadicPartialPath_linear_law N t c) hMeas
  · filter_upwards [bakryBrownianDyadicPartialPath_tendsto] with sample hs
    apply tendsto_finsetSum
    intro a ha
    exact tendsto_const_nhds.mul ((continuous_eval_const (t a)).continuousAt.tendsto.comp hs)
  · exact continuous_real_toNNReal.continuousAt.tendsto.comp
      (bakryBrownianDyadicQuadraticKernel_tendsto t c)

/-- Every actual finite collection of unit-interval evaluations is jointly
Gaussian. No Gaussian-process certificate is supplied. -/
theorem bakryBrownianDyadicPath_evaluations_gaussian {ι : Type*} [Finite ι]
    (t : ι → Icc (0 : ℝ) 1) :
    HasGaussianLaw (fun sample : BakryBrownianDyadicSample => fun a : ι =>
      bakryBrownianDyadicPath sample (t a)) bakryBrownianDyadicMeasure := by
  have := Fintype.ofFinite ι
  classical
  have hMeas : AEMeasurable (fun sample : BakryBrownianDyadicSample => fun a : ι =>
      bakryBrownianDyadicPath sample (t a)) bakryBrownianDyadicMeasure :=
    AEMeasurable.of_eval (fun a => (continuous_eval_const (t a)).measurable.comp_aemeasurable
      bakryBrownianDyadicPath_aemeasurable)
  refine ⟨hMeas,?_⟩
  apply isGaussian_of_map_eq_gaussianReal
  intro L
  let c := fun a => L (Pi.single a 1)
  have hRep (x : ι → ℝ) : L x = ∑ a, c a*x a := by
    have he : (∑ a, Pi.single a (x a)) = x := by
      funext b
      simp only [Finset.sum_apply]
      exact Fintype.sum_pi_single b x
    calc
      L x = L (∑ a, Pi.single a (x a)) := congrArg L he.symm
      _ = ∑ a, L (Pi.single a (x a)) := by rw [map_sum]
      _ = ∑ a, c a*x a := by
        apply Finset.sum_congr rfl
        intro a ha
        have hb : Pi.single a (x a) = (x a) • Pi.single a 1 := by
          funext b
          by_cases h : b = a <;> simp [h]
        rw [hb, map_smul]
        change x a * c a = c a * x a
        ring
  refine ⟨0, (bakryBrownianMinQuadratic t c).toNNReal,?_⟩
  rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hMeas]
  have h := bakryBrownianDyadicPath_linear_law t c
  rw [← h.map_eq]
  apply Measure.map_congr
  exact Eventually.of_forall (fun sample => hRep _)

theorem bakryBrownianDyadicPath_isGaussianProcess :
    IsGaussianProcess (fun t : Icc (0 : ℝ) 1 => fun sample : BakryBrownianDyadicSample =>
      bakryBrownianDyadicPath sample t) bakryBrownianDyadicMeasure := by
  refine ⟨fun I => ?_⟩
  exact bakryBrownianDyadicPath_evaluations_gaussian (fun t : I => t.val)

theorem bakryBrownianDyadicPath_law (t : Icc (0 : ℝ) 1) :
    HasLaw (fun sample : BakryBrownianDyadicSample => bakryBrownianDyadicPath sample t)
      (gaussianReal 0 t.val.toNNReal) bakryBrownianDyadicMeasure := by
  have h := bakryBrownianDyadicPath_linear_law (fun _ : Unit => t) (fun _ => 1)
  simpa only [bakryBrownianMinQuadratic, Fintype.sum_unique, mul_one, one_mul, min_self] using h

theorem bakryBrownianDyadicPath_mean (t : Icc (0 : ℝ) 1) :
    (∫ sample, bakryBrownianDyadicPath sample t ∂bakryBrownianDyadicMeasure) = 0 := by
  rw [(bakryBrownianDyadicPath_law t).integral_eq, integral_id_gaussianReal]

theorem bakryBrownianDyadicPath_memLp_two (t : Icc (0 : ℝ) 1) :
    MemLp (fun sample : BakryBrownianDyadicSample => bakryBrownianDyadicPath sample t) 2
      bakryBrownianDyadicMeasure := (bakryBrownianDyadicPath_law t).hasGaussianLaw.memLp_two

theorem bakryBrownianDyadicPath_variance (t : Icc (0 : ℝ) 1) :
    Var[(fun sample => bakryBrownianDyadicPath sample t);bakryBrownianDyadicMeasure] = (t : ℝ) := by
  rw [(bakryBrownianDyadicPath_law t).variance_eq, variance_id_gaussianReal]
  exact Real.coe_toNNReal _ t.property.1

theorem bakryBrownianDyadicPath_covariance (s t : Icc (0 : ℝ) 1) :
    cov[(fun sample => bakryBrownianDyadicPath sample s),
      (fun sample => bakryBrownianDyadicPath sample t);bakryBrownianDyadicMeasure] =
      min (s : ℝ) (t : ℝ) := by
  have h := bakryBrownianDyadicPath_linear_law (fun a : Fin 2 => if a=0 then s else t) (fun _ => 1)
  have hV := h.variance_eq
  simp only [Fin.isValue, one_mul, Fin.sum_univ_two, ↓reduceIte, one_ne_zero,
    bakryBrownianMinQuadratic, mul_one, min_self, variance_id_gaussianReal,
    Real.coe_toNNReal'] at hV
  have hp : 0 ≤ (s : ℝ)+(min (s : ℝ) (t : ℝ))+(min (t : ℝ) (s : ℝ)+(t : ℝ)) := by
    have hm : 0 ≤ min (s : ℝ) (t : ℝ) := le_min s.property.1 t.property.1
    rw [min_comm (t : ℝ)]
    linarith [s.property.1, t.property.1]
  rw [max_eq_left hp] at hV
  have hAdd := variance_fun_add (bakryBrownianDyadicPath_memLp_two s)
    (bakryBrownianDyadicPath_memLp_two t)
  rw [bakryBrownianDyadicPath_variance, bakryBrownianDyadicPath_variance] at hAdd
  rw [min_comm (t : ℝ)] at hV
  linarith

end
end GinibrePoincare
