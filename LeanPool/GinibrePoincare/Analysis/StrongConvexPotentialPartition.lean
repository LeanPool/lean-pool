/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/StrongConvexPotentialPartition.lean.
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

public import LeanPool.GinibrePoincare.Analysis.StrongConvexRadialLaw

/-!
# Strong convex potential partition

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `rhoConvex_potentialPartition_lt_top`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal ContDiff
namespace GinibrePoincare
noncomputable section

theorem rawPotentialKostlanCoordinateLaw_squaredRadius (n k : ℕ) (hn : 0 < n)
    {V : Potential} (hVc : Continuous V) (hVr : IsRotationalPotential V) :
    (rawPotentialKostlanCoordinateLaw n k V).map Complex.normSq =
      (ENNReal.ofReal ((n : ℝ) / Real.pi) *
        (((k + 1 : ℕ) : ℝ≥0∞) * potentialPolynomialVolume k (Complex.normSq ⁻¹' Iic 1))) •
        rawPotentialSquaredRadiusLaw n k V := by
  let b := ENNReal.ofReal ((n : ℝ) / Real.pi) *
    (((k + 1 : ℕ) : ℝ≥0∞) *
      potentialPolynomialVolume k (Complex.normSq ⁻¹' Iic 1))
  have ht : (rawPotentialKostlanCoordinateLaw n k V).map Complex.normSq =
      b • rawPotentialSquaredRadiusLaw n k V := by
    rw [rawPotentialKostlanCoordinateLaw_eq_volume n k hn hVc, Measure.map_smul _
        Complex.continuous_normSq.measurable.aemeasurable]
    have hprofile : (fun z : ℂ => ENNReal.ofReal (Real.exp (-(n : ℝ) * V z))) =
        (fun s => ENNReal.ofReal (Real.exp (-(n : ℝ) * potentialSquaredRadiusProfile V s))) ∘
          Complex.normSq := by
      funext z
      rw [Function.comp_apply, potential_eq_squaredRadiusProfile hVr]
    rw [hprofile, map_withDensity_comp_measurable _ _ Complex.continuous_normSq.measurable _
      (by unfold potentialSquaredRadiusProfile;
          exact (Real.continuous_exp.comp (continuous_const.mul
            (hVc.comp (Complex.continuous_ofReal.comp
                Real.continuous_sqrt)))).measurable.ennreal_ofReal),
      potentialPolynomialVolume_squaredRadius, withDensity_smul_measure, smul_smul]
    rfl
  exact ht

theorem potentialPolynomialVolume_unit_disk_lt_top (k : ℕ) :
    potentialPolynomialVolume k (Complex.normSq ⁻¹' Iic 1) < ⊤ := by
  have hq := Complex.continuous_normSq
  have hcompact : IsCompact (Complex.normSq ⁻¹' Iic 1) := by
    apply (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset
      (isClosed_le hq continuous_const)
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    change Complex.normSq z ≤ 1 at hz
    rw [Complex.normSq_eq_norm_sq] at hz
    nlinarith [norm_nonneg z]
  unfold potentialPolynomialVolume
  rw [withDensity_apply _ (hq.measurable measurableSet_Iic)]
  exact (Complex.continuous_normSq.pow k).continuousOn.integrableOn_compact hcompact
      |>.lintegral_lt_top

theorem rhoConvex_raw_squaredRadius_mass_lt_top (n k : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) :
    rawPotentialSquaredRadiusLaw n k V univ < ⊤ := by
  have hi := rhoConvexPotential_radial_density_integrable n k hn ρ hρ hV hrot hc
  rw [rawPotentialSquaredRadiusLaw_eq_square_map n k V hV.continuous,
    Measure.smul_apply, Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp only [preimage_univ, smul_eq_mul]
  rw [rawRadialConfinementLaw_mass n k (fun r : ℝ => V (r : ℂ))
    (hV.continuous.comp Complex.continuous_ofReal) hi]
  exact ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top

theorem rhoConvex_raw_Kostlan_mass_lt_top (n k : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) :
    rawPotentialKostlanCoordinateLaw n k V univ < ⊤ := by
  have he := rawPotentialKostlanCoordinateLaw_squaredRadius n k hn hV.continuous hrot
  have hm := congrArg (fun μ : Measure ℝ => μ univ) he
  rw [Measure.map_apply Complex.continuous_normSq.measurable MeasurableSet.univ,
    Measure.smul_apply] at hm
  simp only [preimage_univ, smul_eq_mul] at hm
  rw [hm]
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top (by simp)
      (potentialPolynomialVolume_unit_disk_lt_top k)))
    (rhoConvex_raw_squaredRadius_mass_lt_top n k hn ρ hρ hV hrot hc)

theorem rhoConvex_potentialPartition_lt_top (n : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) :
    potentialPartition n V < ⊤ := by
  have he := potentialPartition_eq_coordinate_product n hn hV.continuous hrot
  have hm : ENNReal.ofReal (((n : ℝ) / Real.pi) ^ n) * potentialPartition n V < ⊤ := by
    rw [he]
    apply ENNReal.mul_lt_top (by simp)
    exact ENNReal.prod_lt_top (fun i _ =>
      rhoConvex_raw_Kostlan_mass_lt_top n i.val hn ρ hρ hV hrot hc)
  exact ENNReal.lt_top_of_mul_ne_top_right hm.ne
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))

end
end GinibrePoincare
