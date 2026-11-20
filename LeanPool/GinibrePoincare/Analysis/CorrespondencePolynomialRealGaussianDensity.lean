/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondencePolynomialRealGaussianDensity.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondencePolynomialRealGaussian
public import LeanPool.GinibrePoincare.Analysis.FinitePiDensity
/-!
# Correspondence polynomial real Gaussian density

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondencePolynomial_realGaussian_density_integrable`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace GinibrePoincare
noncomputable section

/-- Gaussian polynomial moments written against literal real-coordinate
Lebesgue density, with arbitrary positive variance. -/
theorem correspondencePolynomial_realGaussian_density_integrable {ι : Type*}
    [Fintype ι] (v : ℝ≥0) (hv : v ≠ 0) (P : MvPolynomial ι ℝ) :
    Integrable (fun x : ι → ℝ => Real.exp (-(∑ i, (x i)^2)/(2*(v : ℝ))) * MvPolynomial.eval x P)
        volume := by
  classical
  let μ : Measure (ι → ℝ) := Measure.pi (fun _ : ι => gaussianReal 0 v)
  have hi : Integrable (fun x => MvPolynomial.eval x P) μ := by
    have he : (fun x => MvPolynomial.eval x P) = fun x =>
        ∑ d ∈ P.support, MvPolynomial.eval x (MvPolynomial.monomial d (P.coeff d)) := by
      funext x
      conv_lhs => rw [P.as_sum]
      simp only [map_sum]
    rw [he]
    apply integrable_finsetSum
    intro d hd
    have hnorm : Integrable (fun x : ι→ℝ => ∏ i, ‖x i‖^(d i)) μ := by
      unfold μ
      apply Integrable.fintype_prod (f := fun i (y : ℝ) => ‖y‖^(d i))
      intro i
      exact (IsGaussian.memLp_id (gaussianReal 0 v) ((d i : ℕ) : ℝ≥0∞) (by
          finiteness)).integrable_norm_pow'
    apply (integrable_norm_iff (MvPolynomial.continuous_eval _).aestronglyMeasurable).mp
    convert hnorm.const_mul (‖P.coeff d‖) using 1
    funext x
    simp only [MvPolynomial.eval_monomial, norm_mul]
    rw [Finsupp.prod_fintype _ _ (by intro i; simp)]
    simp only [norm_prod, norm_pow]
  let : SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF 0 v)) := by
    rw [← gaussianReal_of_var_ne_zero 0 hv]
    infer_instance
  have hμ : μ = (volume : Measure (ι→ℝ)).withDensity
      (fun x => ∏ i, gaussianPDF 0 v (x i)) := by
    unfold μ
    rw [show (fun _ : ι => gaussianReal 0 v) =
      (fun _ : ι => (volume : Measure ℝ).withDensity (gaussianPDF 0 v)) by
      funext i; exact gaussianReal_of_var_ne_zero 0 hv]
    rw [Measure.pi_withDensity _ _ (fun _ => measurable_gaussianPDF 0 v), ← volume_pi]
  rw [hμ] at hi
  have hprod (x : ι→ℝ) : (∏ i, gaussianPDF 0 v (x i)).toReal =
      ((Real.sqrt (2*Real.pi*(v : ℝ)))⁻¹)^(Fintype.card ι) *
        Real.exp (-(∑ i, (x i)^2)/(2*(v : ℝ))) := by
    simp only [ENNReal.toReal_prod, gaussianPDF]
    simp only [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
    simp only [gaussianPDFReal, sub_zero]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,← Real.exp_sum]
    congr 2
    rw [← Finset.sum_div,← Finset.sum_neg_distrib]
  have he := (integrable_withDensity_iff
    (by fun_prop : Measurable (fun x : ι→ℝ => ∏ i, gaussianPDF 0 v (x i)))
    (ae_of_all _ fun x => ENNReal.prod_lt_top (fun i _ => gaussianPDF_lt_top))).mp hi
  simp only [hprod] at he
  have hc : ((Real.sqrt (2*Real.pi*(v : ℝ)))⁻¹)^(Fintype.card ι) ≠ 0 := by
    apply pow_ne_zero
    apply inv_ne_zero
    apply Real.sqrt_ne_zero'.mpr
    have hvR : 0<(v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
    positivity
  have hmul : Integrable (fun x : ι→ℝ => ((Real.sqrt (2*Real.pi*(v : ℝ)))⁻¹)^(Fintype.card ι) *
      (Real.exp (-(∑ i, (x i)^2)/(2*(v : ℝ))) * MvPolynomial.eval x P)) volume := by
    convert he using 1
    funext x
    ring
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) _).mp hmul

end
end GinibrePoincare
