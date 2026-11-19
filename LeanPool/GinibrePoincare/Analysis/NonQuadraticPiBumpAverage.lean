/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticPiBumpAverage.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiBump

/-!
# Non quadratic pi bump average

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `piL2BumpAverage_tendsto`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace GinibrePoincare
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
/-- The mollification of `u ∈ L²(ℂ^d)` by the product bump: the Bochner integral of the
translates `lebesgueL2Translate d y u` against the weight `piPlanarBump d φ y`. -/
def piL2BumpAverage (d : ℕ) (φ : ContDiffBump (0 : ℂ))
    (u : Lp W 2 (volume : Measure (Configuration d))) : Lp W 2 (volume : Measure (Configuration d))
        :=
  ∫ y, piPlanarBump d φ y • lebesgueL2Translate d y u

theorem piPlanarBump_integrable (d : ℕ) (φ : ContDiffBump (0 : ℂ)) :
    Integrable (piPlanarBump d φ) (volume : Measure (Configuration d)) :=
  (piPlanarBump_continuous d φ).integrable_of_hasCompactSupport
    (piPlanarBump_compact d φ)

omit [CompleteSpace W] in
theorem integrable_piL2BumpIntegrand (d : ℕ) (φ : ContDiffBump (0 : ℂ))
    (u : Lp W 2 (volume : Measure (Configuration d))) :
    Integrable (fun y => piPlanarBump d φ y • lebesgueL2Translate d y u) :=
  ((piPlanarBump_continuous d φ).smul (continuous_lebesgueL2Translate d
      u)).integrable_of_hasCompactSupport (piPlanarBump_compact d φ).smul_right

theorem piL2BumpAverage_error_le (d : ℕ) (φ : ContDiffBump (0 : ℂ))
    (u : Lp W 2 (volume : Measure (Configuration d))) (ε : ℝ)
    (he : ∀ y ∈ Function.support (piPlanarBump d φ),
      ‖lebesgueL2Translate d y u - u‖ ≤ ε) :
    ‖piL2BumpAverage d φ u - u‖ ≤ ε := by
  have hconst : Integrable (fun y => piPlanarBump d φ y • u) :=
    (piPlanarBump_integrable d φ).smul_const u
  have hint := integrable_piL2BumpIntegrand d φ u
  have hmass : (∫ y, piPlanarBump d φ y • u) = u := by
    rw [integral_smul_const]
    change (∫ y : Configuration d, piPlanarBump d φ y) • u = u
    rw [piPlanarBump_integral, one_smul]
  have heq : piL2BumpAverage d φ u - u =
      ∫ y, piPlanarBump d φ y • (lebesgueL2Translate d y u - u) := by
    unfold piL2BumpAverage
    calc
      _ = (∫ y, piPlanarBump d φ y • lebesgueL2Translate d y u) -
          ∫ y, piPlanarBump d φ y • u := by rw [hmass]
      _ = ∫ y, (piPlanarBump d φ y • lebesgueL2Translate d y u -
          piPlanarBump d φ y • u) := (integral_sub hint hconst).symm
      _ = _ := integral_congr_ae (Eventually.of_forall (fun y => (smul_sub _ _ _).symm))
  rw [heq]
  have hnorm : ‖∫ y, piPlanarBump d φ y • (lebesgueL2Translate d y u - u)‖ ≤
      ∫ y, piPlanarBump d φ y * ε := by
    apply norm_integral_le_of_norm_le ((piPlanarBump_integrable d φ).mul_const ε)
    exact Eventually.of_forall (fun y => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (piPlanarBump_nonneg d φ y)]
      by_cases hy : piPlanarBump d φ y = 0
      · simp [hy]
      · exact mul_le_mul_of_nonneg_left (he y hy) (piPlanarBump_nonneg d φ y))
  have hi : (∫ y, piPlanarBump d φ y ∂(volume : Measure (Configuration d))) = 1 :=
    piPlanarBump_integral d φ
  simpa only [integral_mul_const, hi, one_mul] using hnorm

theorem piL2BumpAverage_tendsto (d : ℕ) (φ : ℕ → ContDiffBump (0 : ℂ))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (u : Lp W 2 (volume : Measure (Configuration d))) :
    Tendsto (fun m => piL2BumpAverage d (φ m) u) atTop (𝓝 u) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, ht⟩ := Metric.continuousAt_iff.mp
    (continuous_lebesgueL2Translate d u).continuousAt (ε / 2) (half_pos hε)
  obtain ⟨M, hM⟩ := eventually_atTop.mp ((tendsto_order.mp hφ).2 δ hδ)
  refine ⟨M, fun m hm => ?_⟩
  rw [dist_eq_norm]
  apply (piL2BumpAverage_error_le d (φ m) u (ε / 2) ?_).trans_lt (half_lt_self hε)
  intro y hy
  have hd : dist y 0 < δ := (piPlanarBump_support_ball d (φ m) y hy).trans (hM m hm)
  have he := ht hd
  simpa only [lebesgueL2Translate_zero, dist_eq_norm] using he.le
end
end GinibrePoincare
