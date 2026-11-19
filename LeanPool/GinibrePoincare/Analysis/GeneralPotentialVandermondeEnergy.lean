/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialVandermondeEnergy.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialVandermondeCentered

/-!
# General potential Vandermonde energy

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialVandermonde_weighted_real_energy`.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem integral_potentialMeasure (n : ℕ) {V : Potential} (hV : Continuous V)
    (g : Configuration n → ℝ) :
    (∫ z, g z ∂potentialMeasure n V) =
      (potentialPartition n V).toReal⁻¹ *
        ∫ z, potentialWeight n V z * g z ∂configurationVolume n := by
  unfold potentialMeasure rawPotentialMeasure
  rw [integral_smul_measure, ENNReal.toReal_inv]
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_potentialDensity n hV)
    (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (potentialWeight_nonneg n V _), smul_eq_mul]

theorem potentialVandermonde_weighted_dbarNormSq (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (g : Configuration n → ℂ) (hg : Differentiable ℝ g) (z : Configuration n) :
    (∑ i, Complex.normSq (piComplexDbar i (potentialVandermondeCoefficient n V g) z *
      piPotentialHalfWeight n n V z)) =
      (potentialPartition n V).toReal⁻¹ * potentialWeight n V z * dbarNormSq g z := by
  have he (i : Fin n) : piComplexDbar i (potentialVandermondeCoefficient n V g) z *
      piPotentialHalfWeight n n V z = potentialVandermondeMultiplier n V z * piComplexDbar i g z :=
          by
    rw [piComplexDbar_potentialVandermondeCoefficient V g hg i z]
    change potentialVandermondeCoefficient n V (piComplexDbar i g) z *
      (∏ j, planarPotentialHalfWeight n V (z j)) = _
    exact potentialVandermondeCoefficient_weighted n V _ z
  simp_rw [he, Complex.normSq_mul, piComplexDbar_eq_dbarComponent]
  rw [← Finset.mul_sum, potentialVandermondeMultiplier_normSq n hn hV hfin]
  rfl

theorem potentialVandermonde_weighted_real_gradient (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : Differentiable ℝ f) (z : Configuration n) :
    (∑ i, Complex.normSq (piComplexDbar i (potentialVandermondeCoefficient n V (fun x => (f x : ℂ)))
        z *
      piPotentialHalfWeight n n V z)) =
      (1 / 4 : ℝ) * ((potentialPartition n V).toReal⁻¹ *
        potentialWeight n V z * realGradientNormSq f z) := by
  have hfc : Differentiable ℝ (fun x => (f x : ℂ)) :=
    Complex.ofRealCLM.differentiable.comp hf
  rw [potentialVandermonde_weighted_dbarNormSq n hn hV hfin _ hfc,
    dbarNormSq_ofReal_eq_realGradientNormSq hf]
  ring

theorem potentialVandermonde_weighted_real_energy (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : Differentiable ℝ f) :
    (∫ z, ∑ i, Complex.normSq (piComplexDbar i
      (potentialVandermondeCoefficient n V (fun x => (f x : ℂ))) z *
        piPotentialHalfWeight n n V z) ∂configurationVolume n) =
      (1 / 4 : ℝ) * potentialGradientEnergy n V f := by
  simp_rw [potentialVandermonde_weighted_real_gradient n hn hV hfin f hf]
  rw [integral_const_mul]
  unfold potentialGradientEnergy
  rw [integral_potentialMeasure n hV]
  simp_rw [mul_assoc]
  rw [integral_const_mul]

end
end GinibrePoincare
