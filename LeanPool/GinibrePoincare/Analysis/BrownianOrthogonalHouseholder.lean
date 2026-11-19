/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalHouseholder.lean.
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

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Brownian orthogonal householder

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianHouseholder_radial_coordinate`, `brownianHouseholder_measurable`.
-/

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace
namespace GinibrePoincare
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Householder reflection across the hyperplane orthogonal to `u`, written as minus the
reflection in the line `span ℝ {u}`. -/
def brownianHouseholder (u : E) : E ≃ₗᵢ[ℝ] E :=
  (Submodule.span ℝ {u}).reflection.trans (LinearIsometryEquiv.neg ℝ)

omit [CompleteSpace E] in
theorem brownianHouseholder_apply (u v : E) :
    brownianHouseholder u v = v - (2 * (inner ℝ u v / ‖u‖ ^ 2)) • u := by
  change -((Submodule.span ℝ {u}).reflection v) = _
  rw [Submodule.reflection_singleton_apply]
  change -(2 • (inner ℝ u v / ‖u‖ ^ 2) • u - v) = _
  simp only [two_smul, two_mul, add_smul]
  abel

omit [CompleteSpace E] in
theorem brownianHouseholder_same_norm (x e : E) (he : ‖x‖ = ‖e‖) :
    brownianHouseholder (x-e) x = e := by
  rw [brownianHouseholder_apply]
  by_cases hzero : x-e = 0
  · have hx : x = e := sub_eq_zero.mp hzero
    simp [hx]
  have hnorm : ‖x-e‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hzero)
  have hid : 2 * inner ℝ (x-e) x = ‖x-e‖ ^ 2 := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq, norm_sub_sq_real, ← he, real_inner_comm e x]
    ring
  have hc : 2 * (inner ℝ (x-e) x / ‖x-e‖ ^ 2) = 1 := by
    rw [← mul_div_assoc, hid, div_self hnorm]
  rw [hc, one_smul]
  abel

omit [CompleteSpace E] in
theorem brownianHouseholder_radial_coordinate (x e v : E) (he : ‖x‖ = ‖e‖) :
    inner ℝ e (brownianHouseholder (x-e) v) = inner ℝ x v := by
  have hh := (brownianHouseholder (x-e)).inner_map_map x v
  rw [brownianHouseholder_same_norm x e he] at hh
  exact hh

omit [CompleteSpace E] in
theorem brownianHouseholder_measurable [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] :
    Measurable (fun p : E × E => brownianHouseholder p.1 p.2) := by
  simp_rw [brownianHouseholder_apply]
  fun_prop

end
end GinibrePoincare
