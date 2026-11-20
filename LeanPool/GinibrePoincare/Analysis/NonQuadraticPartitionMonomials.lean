/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticPartitionMonomials.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticRadiusLaw
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticWeightedMonomialRepresentatives

/-!
# Non quadratic partition monomials

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialPartition_weightedMonomial_memLp`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal ContDiff
namespace GinibrePoincare
noncomputable section

theorem planarWeightedMonomial_norm_sq (n k : ℕ) (V : ℂ → ℝ) (z : ℂ) :
    ‖z ^ k * planarPotentialHalfWeight n V z‖ ^ 2 =
      Complex.normSq z ^ k * Real.exp (-(n : ℝ) * V z) := by
  rw [norm_mul, norm_pow]
  unfold planarPotentialHalfWeight
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  rw [show (‖z‖ ^ k) ^ 2 = (‖z‖ ^ 2) ^ k by rw [← pow_mul, ← pow_mul, Nat.mul_comm],
    ← Complex.normSq_eq_norm_sq]
  rw [pow_two, ← Real.exp_add]
  congr 2
  ring

theorem potentialPartition_weightedMonomial_memLp (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hr : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤) (i : Fin
        n) :
    MemLp (fun z : ℂ => z ^ i.val * planarPotentialHalfWeight n V z) 2 volume := by
  have hmass := (rawPotentialKostlanCoordinateLaw_mass_valid n hn hV hr hfin i).2
  rw [rawPotentialKostlanCoordinateLaw_eq_volume n i.val hn hV,
    smul_apply, smul_eq_mul] at hmass
  have hc : ENNReal.ofReal ((n : ℝ) / Real.pi) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hpoly : ((potentialPolynomialVolume i.val).withDensity
      (fun z => ENNReal.ofReal (Real.exp (-(n : ℝ) * V z)))) Set.univ < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right hmass.ne hc
  have hexp : Continuous (fun z : ℂ => Real.exp (-(n : ℝ) * V z)) :=
    Real.continuous_exp.comp (continuous_const.mul hV)
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, potentialPolynomialVolume,
    lintegral_withDensity_eq_lintegral_mul (volume : Measure ℂ)
      (f := fun z => ENNReal.ofReal (Complex.normSq z ^ i.val)) (by fun_prop)
      hexp.measurable.ennreal_ofReal] at hpoly
  have hcont : Continuous (fun z : ℂ => z ^ i.val * planarPotentialHalfWeight n V z) := by
    unfold planarPotentialHalfWeight
    exact (continuous_id.pow i.val).mul (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp ((continuous_const.mul hV).div_const 2)))
  apply (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr
  refine ⟨(hcont.norm.pow 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun z => sq_nonneg _))]
  simp_rw [planarWeightedMonomial_norm_sq, ENNReal.ofReal_mul (pow_nonneg (Complex.normSq_nonneg _)
      _)]
  exact hpoly
end
end GinibrePoincare
