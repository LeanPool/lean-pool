/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoScalarChain.lean.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoConfiguration
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianGenerator
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Finite dimensional Ito scalar chain

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `ginibreRealPaperSpeedGenerator_scalar_comp`.
-/

@[expose] public section

open Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

theorem secondDirectionalDerivative_scalar_comp {n : ℕ}
    (f : Configuration n → ℝ) (φ : ℝ → ℝ) (x v : Configuration n)
    (hf : ContDiffAt ℝ 2 f x) (hφ : ContDiffAt ℝ 2 φ (f x)) :
    secondDirectionalDerivative (fun y => φ (f y)) v x =
      deriv (deriv φ) (f x)*(fderiv ℝ f x v)^2 +
        deriv φ (f x)*secondDirectionalDerivative f v x := by
  have hfd := hf.differentiableAt (by norm_num)
  have hφd := hφ.differentiableAt (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hφ'd : DifferentiableAt ℝ (deriv φ) (f x) :=
    (hφ.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hEq : (fun y => fderiv ℝ (fun z => φ (f z)) y v) =ᶠ[𝓝 x]
      (fun y => deriv φ (f y)*fderiv ℝ f y v) := by
    have hfn := hf.eventually (by norm_num)
    have hφn := hf.continuousAt.eventually (hφ.eventually (by norm_num))
    filter_upwards [hfn, hφn] with y hy hφy
    have he := ((hφy.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt y
      (hy.differentiableAt (by norm_num)).hasFDerivAt).fderiv
    exact congrArg (fun L => L v) he
  unfold secondDirectionalDerivative
  rw [hEq.fderiv_eq]
  have hg : DifferentiableAt ℝ (fun y => deriv φ (f y)) x := by
    simpa only [Function.comp_def] using hφ'd.comp x hfd
  rw [fderiv_fun_mul hg
    (hd.clm_apply (differentiableAt_const v))]
  have hfirst := (hφ'd.hasDerivAt.comp_hasFDerivAt x hfd.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => deriv φ (f y)) x = deriv (deriv φ) (f x) • fderiv ℝ f x at hfirst
  rw [hfirst]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem configurationLaplacian_scalar_comp {n : ℕ}
    (f : Configuration n → ℝ) (φ : ℝ → ℝ) (x : Configuration n)
    (hf : ContDiffAt ℝ 2 f x) (hφ : ContDiffAt ℝ 2 φ (f x)) :
    configurationLaplacian (fun y => φ (f y)) x =
      deriv (deriv φ) (f x)*
        realGradientNormSq f x+
      deriv φ (f x)*configurationLaplacian f x := by
  unfold configurationLaplacian realGradientNormSq
  simp_rw [secondDirectionalDerivative_scalar_comp f φ x _ hf hφ]
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem fderiv_scalar_comp_apply {n : ℕ}
    (f : Configuration n → ℝ) (φ : ℝ → ℝ) (x v : Configuration n)
    (hf : DifferentiableAt ℝ f x) (hφ : DifferentiableAt ℝ φ (f x)) :
    fderiv ℝ (fun y => φ (f y)) x v = deriv φ (f x)*fderiv ℝ f x v := by
  exact congrArg (fun L => L v) (hφ.hasDerivAt.comp_hasFDerivAt x hf.hasFDerivAt).fderiv

theorem ginibrePregenerator_scalar_comp {n : ℕ}
    (f : Configuration n → ℝ) (φ : ℝ → ℝ) (x : Configuration n)
    (hf : ContDiffAt ℝ 2 f x) (hφ : ContDiffAt ℝ 2 φ (f x)) :
    ginibrePregenerator n (fun y => φ (f y)) x =
      deriv φ (f x)*ginibrePregenerator n f x +
        (1/(n : ℝ))*deriv (deriv φ) (f x)*realGradientNormSq f x := by
  unfold ginibrePregenerator
  rw [configurationLaplacian_scalar_comp f φ x hf hφ]
  simp_rw [fderiv_scalar_comp_apply f φ x _
    (hf.differentiableAt (by norm_num)) (hφ.differentiableAt (by norm_num))]
  simp_rw [← Finset.mul_sum]
  ring

theorem ginibreRealPaperSpeedGenerator_scalar_comp {n : ℕ}
    (α : ℝ) (f : Configuration n → ℝ) (φ : ℝ → ℝ) (x : Configuration n)
    (hf : ContDiffAt ℝ 2 f x) (hφ : ContDiffAt ℝ 2 φ (f x)) :
    ginibreRealPaperSpeedGenerator n α (fun y => φ (f y)) x =
      deriv φ (f x)*ginibreRealPaperSpeedGenerator n α f x +
        (α/(n : ℝ)^2)*deriv (deriv φ) (f x)*realGradientNormSq f x := by
  unfold ginibreRealPaperSpeedGenerator
  rw [ginibrePregenerator_scalar_comp f φ x hf hφ]
  simp only [div_eq_mul_inv]
  ring

end
end GinibrePoincare
