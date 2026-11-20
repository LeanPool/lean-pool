/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryRegularizedLift.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryConvexLift
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Smooth strongly convex regularizations of the radial Euclidean lift

The positive extra coordinate removes the nonsmoothness of the radius at the
origin. The strong-convexity parameter remains exactly `nρ`.
-/

@[expose] public section
open Set Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- The regularised potential `x ↦ n * V (√(‖x‖² + ε²))` on a normed group, the potential `V`
being evaluated at a real point. -/
def bakryEmeryRegularizedLiftPotential {E : Type*} [NormedAddCommGroup E]
    (n : ℕ) (V : Potential) (ε : ℝ) (x : E) : ℝ :=
  (n : ℝ) * V (Real.sqrt (‖x‖ ^ 2 + ε ^ 2) : ℂ)

theorem bakryEmeryRegularizedLift_contDiff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (n : ℕ) (V : Potential) (ε : ℝ)
    (hV : ContDiff ℝ 2 V) (hε : 0 < ε) :
    ContDiff ℝ 2 (bakryEmeryRegularizedLiftPotential (E := E) n V ε) := by
  have hq : ContDiff ℝ 2 (fun x : E => ‖x‖ ^ 2 + ε ^ 2) :=
    (contDiff_norm_sq ℝ).add contDiff_const
  have hpos (x : E) : ‖x‖ ^ 2 + ε ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg ‖x‖, sq_pos_of_pos hε]
  exact contDiff_const.mul (hV.comp (Complex.ofRealCLM.contDiff.comp (hq.sqrt hpos)))

/-- The affine embedding `x ↦ (x, ε)` of `E` into the `L²` product `WithLp 2 (E × ℝ)`. -/
def bakryEmeryExtraCoordinate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ε : ℝ) : E →ᵃ[ℝ] WithLp 2 (E × ℝ) :=
  ((WithLp.linearEquiv 2 ℝ (E × ℝ)).symm.toLinearMap.toAffineMap).comp
    ((AffineMap.id ℝ E).prod (AffineMap.const ℝ E ε))

theorem bakryEmeryExtraCoordinate_norm_sq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ε : ℝ) (x : E) :
    ‖bakryEmeryExtraCoordinate ε x‖ ^ 2 = ‖x‖ ^ 2 + ε ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp [bakryEmeryExtraCoordinate, Real.norm_eq_abs, sq_abs]

theorem bakryEmeryExtraCoordinate_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ε : ℝ) (x : E) :
    ‖bakryEmeryExtraCoordinate ε x‖ = Real.sqrt (‖x‖ ^ 2 + ε ^ 2) := by
  rw [← bakryEmeryExtraCoordinate_norm_sq ε x, Real.sqrt_sq (norm_nonneg _)]

/-- Global strong convexity is preserved with no loss of the exact `nρ`
constant when the confinement is regularized by an extra coordinate. -/
theorem bakryEmeryRegularizedLift_strongConvex {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (n : ℕ) (ρ ε : ℝ) {V : Potential}
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) :
    ConvexOn ℝ (univ : Set E) (fun x =>
      bakryEmeryRegularizedLiftPotential n V ε x - ((n : ℝ) * ρ) / 2 * ‖x‖ ^ 2) := by
  have h := (bakryEmeryEuclideanLift_strongConvex
    (E := WithLp 2 (E × ℝ)) n ρ hrot hc).comp_affineMap
      (bakryEmeryExtraCoordinate (E := E) ε)
  have h' := h.add_const (((n : ℝ) * ρ) / 2 * ε ^ 2)
  convert h' using 1
  · simp
  · funext x
    change (n : ℝ) * V (Real.sqrt (‖x‖ ^ 2 + ε ^ 2) : ℂ) - ((n : ℝ) * ρ) / 2 * ‖x‖ ^ 2 =
      ((n : ℝ) * V (‖bakryEmeryExtraCoordinate ε x‖ : ℂ) -
        ((n : ℝ) * ρ) / 2 * ‖bakryEmeryExtraCoordinate ε x‖ ^ 2) +
        ((n : ℝ) * ρ) / 2 * ε ^ 2
    rw [bakryEmeryExtraCoordinate_norm_sq, bakryEmeryExtraCoordinate_norm]
    ring

/-- The regularized potentials converge pointwise to the original radial lift. -/
theorem bakryEmeryRegularizedLift_tendsto {E : Type*} [NormedAddCommGroup E]
    (n : ℕ) (V : Potential) (hV : Continuous V) (x : E) :
    Tendsto (fun ε : ℝ => bakryEmeryRegularizedLiftPotential n V ε x) (𝓝 0)
      (𝓝 (bakryEmeryEuclideanLiftPotential n V x)) := by
  have hq : Tendsto (fun ε : ℝ => ‖x‖ ^ 2 + ε ^ 2) (𝓝 0) (𝓝 (‖x‖ ^ 2)) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => ‖x‖ ^ 2) (𝓝 0) (𝓝 (‖x‖ ^ 2))).add
      ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).pow 2))
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hq
  have hC := Complex.continuous_ofReal.continuousAt.tendsto.comp hs
  have hh := hV.continuousAt.tendsto.comp hC
  simpa [bakryEmeryRegularizedLiftPotential, bakryEmeryEuclideanLiftPotential,
    Real.sqrt_sq (norm_nonneg x)] using hh.const_mul (n : ℝ)

/-- Uniform quadratic confinement, including the positive extra coordinate. -/
theorem bakryEmeryRegularizedLift_quadratic_lower_bound {E : Type*} [NormedAddCommGroup E]
    (n : ℕ) (ρ ε : ℝ) {V : Potential} (hrot : IsRotationalPotential V)
    (hc : IsRhoConvexPotential ρ V) (x : E) :
    ((n : ℝ) * ρ) / 2 * (‖x‖ ^ 2 + ε ^ 2) + (n : ℝ) * V 0 ≤
      bakryEmeryRegularizedLiftPotential n V ε x := by
  have h := rhoConvexPotential_quadratic_lower_bound ρ hrot hc
    (Real.sqrt (‖x‖ ^ 2 + ε ^ 2) : ℂ)
  rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by positivity)] at h
  have hh := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  dsimp [bakryEmeryRegularizedLiftPotential]
  convert hh using 1; ring

/-- A single Gaussian majorant dominates every positive regularization. -/
theorem bakryEmeryRegularizedLift_density_domination {E : Type*} [NormedAddCommGroup E]
    (n : ℕ) (ρ ε : ℝ) {V : Potential} (hρ : 0 ≤ ρ)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) (x : E) :
    Real.exp (-bakryEmeryRegularizedLiftPotential n V ε x) ≤
      Real.exp (-(n : ℝ) * V 0) * Real.exp (-((n : ℝ) * ρ) / 2 * ‖x‖ ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := bakryEmeryRegularizedLift_quadratic_lower_bound n ρ ε hrot hc x
  have hpos : 0 ≤ ((n : ℝ) * ρ) / 2 * ε ^ 2 := by positivity
  nlinarith

end
end GinibrePoincare

