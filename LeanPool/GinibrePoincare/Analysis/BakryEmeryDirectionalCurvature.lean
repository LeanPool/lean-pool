/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BakryEmeryDirectionalCurvature.lean.
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

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Strong convexity gives the actual directional curvature and gradient
monotonicity needed by the Langevin construction. These are differential facts,
not an assumed entropy inequality or an assumed diffusion. -/

@[expose] public section
namespace GinibrePoincare
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem convex_line {F : E → ℝ} (hF : ConvexOn ℝ univ F) (x v : E) :
    ConvexOn ℝ univ (fun t : ℝ => F (x + t • v)) := by
  simpa [Function.comp_def, AffineMap.lineMap_apply_module', add_comm] using
    hF.comp_affineMap (AffineMap.lineMap x (x + v))

/-- The supporting-plane bound uses the literal Fréchet derivative. -/
theorem bakryEmery_convex_support {F : E → ℝ} (hF : ConvexOn ℝ univ F)
    (x y : E) (hd : DifferentiableAt ℝ F x) :
    (fderiv ℝ F x) (y-x) ≤ F y - F x := by
  have hl : HasDerivAt (fun t : ℝ => x + t • (y-x)) (y-x) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (y-x) |>.const_add x
  have h := (convex_line hF x (y-x)).le_slope_of_hasDerivAt
    (mem_univ 0) (mem_univ 1) (by norm_num)
    (by
      have hd' : HasFDerivAt F (fderiv ℝ F x) (x + (0 : ℝ) • (y-x)) := by simpa using hd.hasFDerivAt
      exact hd'.comp_hasDerivAt 0 hl)
  simpa [slope, div_eq_mul_inv] using h

/-- Strong convexity of the actual potential remainder implies strong
monotonicity of its literal derivative, with no Hessian upper bound. -/
theorem bakryEmery_gradient_strong_monotonicity (W : E → ℝ) (κ : ℝ)
    (hconv : ConvexOn ℝ univ (fun x => W x - (κ / 2) * ‖x‖ ^ 2))
    (x y : E) (hx : DifferentiableAt ℝ W x) (hy : DifferentiableAt ℝ W y) :
    κ*‖y-x‖^2 ≤ (fderiv ℝ W y) (y-x) - (fderiv ℝ W x) (y-x) := by
  let R : E → ℝ := fun z => W z - (κ/2)*‖z‖^2
  have hR (z : E) (hz : DifferentiableAt ℝ W z) :
      HasFDerivAt R (fderiv ℝ W z - (κ/2) • (2 • innerSL ℝ z)) z :=
    hz.hasFDerivAt.sub ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul (κ/2))
  have ha := bakryEmery_convex_support hconv x y (hR x hx).differentiableAt
  have hb := bakryEmery_convex_support hconv y x (hR y hy).differentiableAt
  rw [(hR x hx).fderiv] at ha
  rw [(hR y hy).fderiv] at hb
  simp only [sub_apply, add_apply, smul_apply,
    smul_eq_mul, innerSL_apply_apply, two_smul] at ha hb
  have hlin : (fderiv ℝ W y) (x-y) = -(fderiv ℝ W y) (y-x) := by
    rw [show x-y = -(y-x) by abel, map_neg]
  have hi : ⟪y, x-y⟫_ℝ = -⟪y, y-x⟫_ℝ := by
    rw [show x-y = -(y-x) by abel, inner_neg_right]
  have hn : ⟪y, y-x⟫_ℝ - ⟪x, y-x⟫_ℝ = ‖y-x‖^2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  rw [hlin, hi] at hb
  change _ ≤ R y - R x at ha
  change _ ≤ R x - R y at hb
  rw [← hn]
  nlinarith

end GinibrePoincare
