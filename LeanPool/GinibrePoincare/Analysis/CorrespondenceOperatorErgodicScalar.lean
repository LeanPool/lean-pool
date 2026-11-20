/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorErgodicScalar.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorEvolution
/-!
# Correspondence operator ergodic scalar

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperator_ergodic_range_norm_bound`.
-/

@[expose] public section
open Set Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
/-- Uniform decay after multiplication by the resolvent complement, with no
spectral gap assumption. -/
theorem correspondenceOperator_ergodic_multiplier_bound {t r : ℝ} (ht : 0 ≤ t)
    (hr : r ∈ Icc (0 : ℝ) 1) :
    ‖resolventEvolutionMultiplier t r*(1-r)‖≤1/(1+t) := by
  by_cases ht0 : t=0
  · subst t
    simp only [resolventEvolutionMultiplier_zero, one_mul, add_zero, div_one, Real.norm_eq_abs]
    rw [abs_of_nonneg (sub_nonneg.mpr hr.2)]
    linarith [hr.1]
  have htpos : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
  by_cases hr0 : r=0
  · subst r
    rw [resolventEvolutionMultiplier_nonpositive htpos le_rfl, zero_mul, norm_zero]
    positivity
  have hrpos : 0<r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
  rw [resolventEvolutionMultiplier_positive_formula htpos hrpos]
  have hu : 0≤1-r := sub_nonneg.mpr hr.2
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le hu)]
  have hinv : 1-r≤r⁻¹-1 := by
    have hri := mul_inv_cancel₀ hr0
    nlinarith [sq_nonneg (r-1)]
  have hexp : Real.exp (-t*(r⁻¹-1))≤Real.exp (-t*(1-r)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hinv (neg_nonpos.mpr ht))
  have he : (1+t*(1-r))*Real.exp (-t*(1-r))≤1 := by
    have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (t*(1-r)))
      (Real.exp_pos (-t*(1-r))).le
    rw [← Real.exp_add] at hh
    have hz : t*(1-r)+ -t*(1-r)=0 := by ring
    rw [hz, Real.exp_zero] at hh
    simpa only [add_comm] using hh
  have hp : 0<1+t := by linarith
  apply (le_div_iff₀ hp).mpr
  have hcomp : (1+t)*(1-r)≤1+t*(1-r) := by nlinarith [hr.1]
  have hb := mul_le_mul_of_nonneg_right hcomp (Real.exp_pos (-t*(1-r))).le
  have hmul := mul_le_mul_of_nonneg_right hexp hu
  nlinarith

/-- The CFC complement range decays uniformly for any positive contraction
resolvent, including spectral accumulation at both zero and one. -/
theorem correspondenceOperator_ergodic_range_norm_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Icc (0 : ℝ) 1) (t : ℝ≥0) :
    ‖resolventCfcEvolution R t*(1-R)‖≤1/(1+(t : ℝ)) := by
  let f := resolventEvolutionMultiplier (t : ℝ)
  have hf : ContinuousOn f (spectrum ℝ R) := (resolventEvolutionMultiplier_continuous
      _).continuousOn
  have he : cfc (fun r : ℝ => f r*(1-r)) R=resolventCfcEvolution R t*(1-R) := by
    rw [cfc_mul f (fun r : ℝ => 1-r) R hf (continuousOn_const.sub continuousOn_id),
      cfc_sub (fun _ : ℝ => 1) (fun r : ℝ => r) R continuousOn_const continuousOn_id,
      cfc_const_one (R := ℝ) (a := R), cfc_id' ℝ R hR]
    rfl
  rw [← he]
  apply norm_cfc_le (by positivity)
  intro r hr
  exact correspondenceOperator_ergodic_multiplier_bound t.property (hSpec r hr)
end
end GinibrePoincare
