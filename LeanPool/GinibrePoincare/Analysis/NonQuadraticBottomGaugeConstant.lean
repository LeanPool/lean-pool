/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticBottomGaugeConstant.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialQuotientCentering
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticAlternatingPhasePolynomial

/-!
# Non quadratic bottom gauge constant

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialInverseGauge_bottom_polynomial_constant`.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- A literal bottom alternating polynomial becomes a genuine constant under
 the normalized nonquadratic Vandermonde unitary. -/
theorem potentialInverseGauge_bottom_polynomial_constant {n : ℕ} (hn : 0 < n)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) (P : ConfigurationPolynomial n)
    (hp : P.IsHomogeneous (vandermondeDegree n))
    (hAlt : IsAlternatingConfigurationPolynomial P) (F : PlanarPiLebesgueL2 n)
    (hF : (F : Configuration n → ℂ) =ᵐ[volume]
      fun z => MvPolynomial.eval z P * piPotentialHalfWeight n n V z) :
    ∃ c : ℂ, (potentialPiVandermondeL2Equiv n hn hV.continuous hfin).symm F =
      potentialConstantL2 n hn hV.continuous hfin c := by
  have hex : ∃ t : ℂ, ∀ z, MvPolynomial.eval z P = t * vandermonde z := by
    by_cases hz : P = 0
    · exact ⟨0, fun z => by simp [hz]⟩
    obtain ⟨Q, hQ, hf⟩ := alternating_polynomial_vandermonde_division hAlt
    have hc := quotient_eq_C_of_bottom_homogeneous_degree hp hz hf
    refine ⟨Q.coeff 0, fun z => ?_⟩
    rw [hf, hc, map_mul, MvPolynomial.eval_C, eval_polynomialVandermonde]
    simpa using mul_comm (vandermonde z) (Q.coeff 0)
  obtain ⟨t, ht⟩ := hex
  let s : ℂ := Real.sqrt (potentialPartition n V).toReal
  have hs : s ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (Real.sqrt_pos.mpr (ENNReal.toReal_pos
      (potentialPartition_pos n hn hV.continuous).ne' hfin.ne)).ne'
  refine ⟨s * t, ?_⟩
  apply (potentialPiVandermondeL2Equiv n hn hV.continuous hfin).injective
  rw [LinearIsometryEquiv.apply_symm_apply,
    potentialPiVandermondeL2Equiv_constant n hn hV.continuous hrot hfin]
  have hc : s⁻¹ * (s * t) = t := by rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  change F = (s⁻¹ * (s * t)) • partitionWeightedVandermondeL2 n hn hV.continuous hrot hfin
  rw [hc]
  apply Lp.ext
  filter_upwards [hF, partitionWeightedVandermondeL2_coeFn n hn hV.continuous hrot hfin,
    Lp.coeFn_smul t (partitionWeightedVandermondeL2 n hn hV.continuous hrot hfin)] with z hf hw hs
  rw [hf, hs]
  change MvPolynomial.eval z P * piPotentialHalfWeight n n V z = t * _
  rw [ht, hw]
  ring

end
end GinibrePoincare
