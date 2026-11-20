/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryRadialLSI.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryLiftBoundedLSI
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryRadiusLaw
/-!
# Alternative Bakry Emery radial LSI

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmery_kostlan_radius_bounded_lsi`.
-/

@[expose] public section
open MeasureTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The paper's actual single-radius law inherits LSI from its strongly convex
Euclidean lift. No quantile transport or supplied diffusion is used. -/
theorem bakryEmery_kostlan_radius_bounded_lsi
    (n k : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)
    (V : Potential) (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) {K : ℝ≥0} (hLip : LipschitzWith K f)
    (C : ℝ) (hb : ∀ r, ‖f r‖ ≤ C) :
    squareEntropy ((potentialSquaredRadiusLaw n k V).map Real.sqrt) f ≤
      (2/((n : ℝ)*ρ)) * ∫ r, (deriv f r)^2 ∂(potentialSquaredRadiusLaw n k V).map Real.sqrt := by
  let E := EuclideanSpace ℝ (Fin (k+1) × Fin 2)
  let μ := bakryEmeryNormalizedGibbs (volume : Measure E) (bakryEmeryEuclideanLiftPotential n V)
  have hmap : μ.map norm = (potentialSquaredRadiusLaw n k V).map Real.sqrt :=
    bakryEmeryEuclideanGibbs_radius_law n k hn ρ hρ V hV.continuous hrot hc
  have he : squareEntropy (μ.map norm) f = squareEntropy μ (fun x : E => f ‖x‖) :=
    squareEntropy_map μ norm continuous_norm.measurable.aemeasurable f
      (hf.continuous.pow 2).aestronglyMeasurable
      (continuous_square_mul_log hf.continuous).aestronglyMeasurable
  have hg : (∫ x : E, ‖gradient (fun y : E => f ‖y‖) x‖^2 ∂μ) =
      ∫ r, (deriv f r)^2 ∂μ.map norm := by
    rw [integral_congr_ae (bakryEmeryEuclideanGibbs_radius_gradient_energy_ae n k V f hf)]
    exact (integral_map continuous_norm.measurable.aemeasurable
      ((hf.continuous_deriv (by norm_num)).pow 2).aestronglyMeasurable).symm
  have h := bakryEmeryEuclideanLift_boundedLipschitz_square_lsi n (k+1) hn (by omega)
    ρ hρ V hV hrot hc (fun x : E => f ‖x‖) (LipschitzWith.of_dist_le_mul (fun x y =>
        (hLip.dist_le_mul ‖x‖ ‖y‖).trans
      (mul_le_mul_of_nonneg_left (dist_norm_norm_le x y) K.coe_nonneg))) C
    (fun x => hb ‖x‖)
  change squareEntropy μ (fun x : E => f ‖x‖) ≤ _ at h
  rw [←he, hg, hmap] at h
  exact h

end
end GinibrePoincare
