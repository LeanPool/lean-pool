/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreOUTransition.lean.
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

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Kernel.Defs

/-! # Actual Gaussian Ornstein–Uhlenbeck transition kernels -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The Ornstein–Uhlenbeck decay factor `exp (-rate * t)`. -/
def ginibreOUDecay (rate t : ℝ≥0) : ℝ := Real.exp (-(rate : ℝ) * (t : ℝ))
/-- The Ornstein–Uhlenbeck transition variance `(1 - ginibreOUDecay rate t ^ 2) / 2` at time
`t`. -/
def ginibreOUVariance (rate t : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal ((1 - ginibreOUDecay rate t ^ 2) / 2)

theorem ginibreOUDecay_nonneg (rate t : ℝ≥0) : 0 ≤ ginibreOUDecay rate t :=
  (Real.exp_pos _).le

theorem ginibreOUDecay_le_one (rate t : ℝ≥0) : ginibreOUDecay rate t ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr rate.coe_nonneg) t.coe_nonneg

theorem ginibreOUVariance_coe (rate t : ℝ≥0) :
    (ginibreOUVariance rate t : ℝ) = (1 - ginibreOUDecay rate t ^ 2) / 2 := by
  apply Real.coe_toNNReal
  have h0 := ginibreOUDecay_nonneg rate t
  have h1 := ginibreOUDecay_le_one rate t
  nlinarith

theorem ginibreOUDecay_add (rate s t : ℝ≥0) :
    ginibreOUDecay rate (s + t) = ginibreOUDecay rate t * ginibreOUDecay rate s := by
  simp only [ginibreOUDecay, NNReal.coe_add]
  rw [← Real.exp_add]
  congr 1
  ring

theorem ginibreOUVariance_add (rate s t : ℝ≥0) :
    (ginibreOUVariance rate (s + t) : ℝ) =
      ginibreOUDecay rate t ^ 2 * (ginibreOUVariance rate s : ℝ) +
        (ginibreOUVariance rate t : ℝ) := by
  simp only [ginibreOUVariance_coe, ginibreOUDecay_add]
  ring

/-- The genuine probability kernel with stationary real variance 1/2. -/
def ginibreOUTransition (rate t : ℝ≥0) : Kernel ℝ ℝ where
  toFun x := gaussianReal (ginibreOUDecay rate t * x) (ginibreOUVariance rate t)
  measurable' := measurable_gaussianReal.comp
    ((measurable_const.mul measurable_id).prodMk measurable_const)

instance ginibreOUTransition_isMarkov (rate t : ℝ≥0) :
    IsMarkovKernel (ginibreOUTransition rate t) where
  isProbabilityMeasure x := by
    change IsProbabilityMeasure
      (gaussianReal (ginibreOUDecay rate t * x) (ginibreOUVariance rate t))
    infer_instance

@[simp] theorem ginibreOUTransition_zero (rate : ℝ≥0) (x : ℝ) :
    ginibreOUTransition rate 0 x = Measure.dirac x := by
  simp [ginibreOUTransition, ginibreOUVariance, ginibreOUDecay, gaussianReal_zero_var]

theorem ginibreOUTransition_mean (rate t : ℝ≥0) (x : ℝ) :
    (∫ y, y ∂ginibreOUTransition rate t x) = ginibreOUDecay rate t * x := by
  change (∫ y, y ∂gaussianReal (ginibreOUDecay rate t * x) (ginibreOUVariance rate t)) = _
  exact integral_id_gaussianReal

theorem ginibreOUTransition_variance (rate t : ℝ≥0) (x : ℝ) :
    ProbabilityTheory.variance id (ginibreOUTransition rate t x) = ginibreOUVariance rate t := by
  change ProbabilityTheory.variance id (gaussianReal (ginibreOUDecay rate t * x)
    (ginibreOUVariance rate t)) = _
  exact variance_id_gaussianReal

/-- The actual law of an affine combination of two independent Gaussian
coordinates, including zero variances. -/
theorem ginibreGaussian_affine_product_map (a b : ℝ) (v w : ℝ≥0) :
    ((gaussianReal 0 v).prod (gaussianReal 0 w)).map
      (fun p : ℝ × ℝ => a * p.1 + b + p.2) =
        gaussianReal b (NNReal.mk (a ^ 2) (sq_nonneg a) * v + w) := by
  let μ := (gaussianReal 0 v).prod (gaussianReal 0 w)
  have hXY : IndepFun (fun p : ℝ × ℝ => a * p.1 + b) Prod.snd μ :=
    indepFun_prod (X := fun y : ℝ => a * y + b) (Y := id) (by fun_prop) measurable_id
  have hX : μ.map (fun p : ℝ × ℝ => a * p.1 + b) =
      gaussianReal b (NNReal.mk (a ^ 2) (sq_nonneg a) * v) := by
    change μ.map ((fun y : ℝ => a * y + b) ∘ Prod.fst) = _
    rw [← Measure.map_map (by fun_prop) measurable_fst,
      measurePreserving_fst.map_eq]
    have he : (fun y : ℝ => a * y + b) = (fun y : ℝ => y + b) ∘ (fun y : ℝ => a * y) := rfl
    rw [he, ← Measure.map_map (by fun_prop) (by fun_prop),
      gaussianReal_map_const_mul, gaussianReal_map_add_const]
    simp
  have hY : μ.map Prod.snd = gaussianReal 0 w := measurePreserving_snd.map_eq
  have h := gaussianReal_add_gaussianReal_of_indepFun hXY
    ⟨by fun_prop, hX⟩ ⟨measurable_snd.aemeasurable, hY⟩
  change μ.map (fun p : ℝ × ℝ => a * p.1 + b + p.2) = _ at h
  simpa only [μ, add_zero] using h

/-- Two actual independent Gaussian noise increments yield the exact
Ornstein–Uhlenbeck transition at the sum of times. -/
theorem ginibreOUTransition_two_steps (rate s t : ℝ≥0) (x : ℝ) :
    ((gaussianReal 0 (ginibreOUVariance rate s)).prod
      (gaussianReal 0 (ginibreOUVariance rate t))).map
        (fun p : ℝ × ℝ => ginibreOUDecay rate t * (ginibreOUDecay rate s * x + p.1) + p.2) =
      ginibreOUTransition rate (s + t) x := by
  have hf : (fun p : ℝ × ℝ => ginibreOUDecay rate t * (ginibreOUDecay rate s * x + p.1) + p.2) =
      (fun p : ℝ × ℝ => ginibreOUDecay rate t * p.1 +
        (ginibreOUDecay rate t * ginibreOUDecay rate s * x) + p.2) := by
    funext p; ring
  rw [hf, ginibreGaussian_affine_product_map]
  have hv : (NNReal.mk (ginibreOUDecay rate t ^ 2) (sq_nonneg _) : ℝ≥0) * ginibreOUVariance rate s +
      ginibreOUVariance rate t = ginibreOUVariance rate (s + t) := by
    apply Subtype.ext
    exact (ginibreOUVariance_add rate s t).symm
  rw [hv]
  change gaussianReal _ _ = gaussianReal _ _
  rw [ginibreOUDecay_add]

end
end GinibrePoincare
