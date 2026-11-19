/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullSemigroupEigenvectors.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupGenerator
public import Mathlib.Analysis.Calculus.DSlope
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupCFC

/-! # Exact continuous-functional-calculus action on resolvent eigenvectors -/

@[expose] public section
open scoped NNReal ContDiff
namespace GinibrePoincare
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Continuous calculus preserves genuine eigenvectors; differentiability at
 the eigenvalue permits an elementary divided-difference proof. -/
theorem cfc_apply_of_resolvent_eigenvector (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (f : ℝ → ℝ) (hf : Continuous f) (r : ℝ) (hd : DifferentiableAt ℝ f r)
    (x : H) (hx : R x = r • x) : cfc f R x = f r • x := by
  have hg : Continuous (dslope f r) := by
    rw [← continuousOn_univ]
    exact (continuousOn_dslope (s := Set.univ) (by simp)).mpr ⟨hf.continuousOn, hd⟩
  have he : cfc (fun s : ℝ => f s - f r) R =
      (R - (r : ℝ) • 1) * cfc (dslope f r) R := by
    have hfun : (fun s : ℝ => f s - f r) = fun s => (s - r) * dslope f r s := by
      funext s
      exact (sub_smul_dslope f r s).symm
    rw [hfun, cfc_mul (fun s : ℝ => s - r) (dslope f r) R
      (continuousOn_id.sub continuousOn_const) hg.continuousOn,
      cfc_sub (fun s : ℝ => s) (fun _ : ℝ => r) R continuousOn_id continuousOn_const,
      cfc_id' ℝ R hR, cfc_const r R hR, Algebra.algebraMap_eq_smul_one]
  have hc : Commute (R - (r : ℝ) • 1) (cfc (dslope f r) R) := by
    have h := cfc_commute_cfc (fun s : ℝ => s - r) (dslope f r) R
    rw [cfc_sub (fun s : ℝ => s) (fun _ : ℝ => r) R continuousOn_id continuousOn_const,
      cfc_id' ℝ R hR, cfc_const r R hR, Algebra.algebraMap_eq_smul_one] at h
    exact h
  have hzero : (R - (r : ℝ) • 1) x = 0 := by
    simp only [sub_apply, smul_apply, one_apply_eq_self, hx, sub_self]
  have hv := congrArg (fun L : H →L[ℂ] H => L x) he
  rw [hc.eq] at hv
  rw [cfc_sub f (fun _ : ℝ => f r) R hf.continuousOn continuousOn_const,
    cfc_const (f r) R hR, Algebra.algebraMap_eq_smul_one] at hv
  simpa only [sub_apply, smul_apply, one_apply_eq_self, mul_apply_eq_comp,
    hzero, map_zero, sub_eq_zero] using hv

/-- All scalar resolvent multipliers are smooth in the spectral variable. -/
theorem resolventEvolutionMultiplier_contDiff (t : ℝ) : ContDiff ℝ ∞ (resolventEvolutionMultiplier
    t) := by
  unfold resolventEvolutionMultiplier
  split_ifs
  · exact contDiff_const
  · exact contDiff_const.mul ((expNegInvGlue.contDiff : ContDiff ℝ ∞ expNegInvGlue).comp
      (contDiff_id.div_const t))

/-- Exact full-space evolution on every genuine resolvent eigenvector. -/
theorem resolventCfcEvolution_eigenvector (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (t : ℝ≥0) (r : ℝ) (x : H) (hx : R x = r • x) :
    resolventCfcEvolution R t x = resolventEvolutionMultiplier (t : ℝ) r • x :=
  cfc_apply_of_resolvent_eigenvector R hR _ (resolventEvolutionMultiplier_continuous _)
    r ((resolventEvolutionMultiplier_contDiff _).differentiable (by simp)).differentiableAt x hx

/-- Exact evolution on every genuine nonpositive generator eigenvector. -/
theorem resolventCfcEvolution_generator_eigenvector (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hInj : Function.Injective R) (t : ℝ≥0) (rate : ℝ) (hRate : 0 ≤ rate)
    (x : H) (hx : (x, -(rate : ℂ) • x) ∈ (resolventGenerator R hInj).graph) :
    resolventCfcEvolution R t x = Real.exp (-rate * (t : ℝ)) • x := by
  rw [resolventGenerator_graph R hInj] at hx
  change R (x - -(rate : ℂ) • x) = x at hx
  have hsc : x - -(rate : ℂ) • x = (1 + rate) • x := by
    rw [neg_smul, sub_neg_eq_add, add_smul, one_smul]
    rfl
  have hmap : R ((1 + rate) • x) = (1 + rate) • R x :=
    (R.restrictScalars ℝ).map_smul (1 + rate) x
  rw [hsc, hmap] at hx
  have hp : 0 < 1 + rate := by linarith
  have hv : R x = (1 + rate)⁻¹ • x := by
    calc
      R x = (1 + rate)⁻¹ • ((1 + rate) • R x) := (inv_smul_smul₀ hp.ne' _).symm
      _ = _ := congrArg (fun y : H => (1 + rate)⁻¹ • y) hx
  rw [resolventCfcEvolution_eigenvector R hR t _ x hv]
  by_cases ht : t = 0
  · subst t; simp
  · have htpos : 0 < (t : ℝ) := by exact_mod_cast lt_of_le_of_ne t.coe_nonneg (Ne.symm (by
                                     exact_mod_cast ht))
    rw [resolventEvolutionMultiplier_positive_formula htpos (inv_pos.mpr hp), inv_inv]
    rw [show -(t : ℝ) * ((1 + rate) - 1) = -rate * (t : ℝ) by ring]

/-- Every actual zero-mode is fixed at all nonnegative times. -/
theorem resolventCfcEvolution_fixes_kernel (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hInj : Function.Injective R) (t : ℝ≥0) (x : H)
    (hx : (x, 0) ∈ (resolventGenerator R hInj).graph) : resolventCfcEvolution R t x = x := by
  have he := resolventCfcEvolution_generator_eigenvector R hR hInj t 0 le_rfl x
    (by simpa only [Complex.ofReal_zero, neg_zero, zero_smul] using hx)
  simpa only [neg_zero, zero_mul, Real.exp_zero, one_smul] using he

end
end GinibrePoincare
