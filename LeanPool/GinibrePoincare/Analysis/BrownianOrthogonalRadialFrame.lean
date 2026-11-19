/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalRadialFrame.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalHouseholder
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Brownian orthogonal radial frame

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianRadialFrame_radial_coordinate`, `brownianRadialFrame_measurable`.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The unit vector `‖x‖⁻¹ • x` in the direction of `x`, with fallback `e` when `x = 0`. -/
def brownianRadialUnitVector (x e : E) : E := by
  classical
  exact if x = 0 then e else ‖x‖⁻¹ • x

omit [CompleteSpace E] in
theorem brownianRadialUnitVector_norm (x e : E) (he : ‖e‖ = 1) :
    ‖brownianRadialUnitVector x e‖ = 1 := by
  classical
  unfold brownianRadialUnitVector
  split_ifs with hx
  · exact he
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- The Householder reflection along `brownianRadialUnitVector x e - e`, which exchanges the unit
vector `e` with the radial direction of `x`. -/
def brownianRadialFrame (x e : E) : E ≃ₗᵢ[ℝ] E :=
  brownianHouseholder (brownianRadialUnitVector x e - e)

omit [CompleteSpace E] in
theorem brownianRadialFrame_radial_coordinate (x e v : E) (he : ‖e‖ = 1) :
    inner ℝ e (brownianRadialFrame x e v) = inner ℝ (brownianRadialUnitVector x e) v :=
  brownianHouseholder_radial_coordinate _ e v (by rw [brownianRadialUnitVector_norm x e he, he])

omit [CompleteSpace E] in
theorem brownianRadialUnitVector_measurable [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (e : E) : Measurable (fun x => brownianRadialUnitVector x e) := by
  classical
  unfold brownianRadialUnitVector
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

omit [CompleteSpace E] in
theorem brownianRadialFrame_measurable [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (e : E) :
    Measurable (fun p : E × E => brownianRadialFrame p.1 e p.2) := by
  simp_rw [brownianRadialFrame, brownianHouseholder_apply]
  have hw : Measurable (fun p : E × E => brownianRadialUnitVector p.1 e - e) :=
    ((brownianRadialUnitVector_measurable e).comp measurable_fst).sub measurable_const
  exact measurable_snd.sub ((measurable_const.mul
    ((hw.inner measurable_snd).div (hw.norm.pow_const 2))).smul hw)

end
end GinibrePoincare
