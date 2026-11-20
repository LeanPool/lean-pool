/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryJointRadialKernel.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryJointMollification
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticWeyl
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Correspondence auxiliary joint radial kernel

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `configurationRadialSmoothing_mean_value`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

/-- The product kernel `∏ i, planarRadialSmoothingKernel (z i)` on configurations. -/
def configurationRadialSmoothingKernel (n : ℕ) (z : Configuration n) : ℝ :=
  ∏ i, planarRadialSmoothingKernel (z i)

theorem configurationRadialSmoothingKernel_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (configurationRadialSmoothingKernel n) := by
  exact contDiff_prod (fun i _ => planarRadialSmoothingKernel_contDiff.comp (contDiff_apply ℝ (fun _
      => ℂ) i))

/-- The product radial smoothing kernel is supported in the closed sup-norm ball of radius `2`. -/
theorem configurationRadialSmoothingKernel_tsupport_subset (n : ℕ) :
    tsupport (configurationRadialSmoothingKernel n) ⊆
      Metric.closedBall (0 : Configuration n) 2 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  apply pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr
  intro i
  have hzi : planarRadialSmoothingKernel (z i) ≠ 0 := by
    intro hi
    exact hz (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  have hbase : planarRadialSmoothingBase (z i) ≠ 0 := by
    intro h
    exact hzi (by simp [planarRadialSmoothingKernel, h])
  have hpos : 0 < 2-Complex.normSq (z i) := by
    by_contra h
    exact hbase (Real.smoothTransition.zero_of_nonpos (le_of_not_gt h))
  rw [Complex.normSq_eq_norm_sq] at hpos
  nlinarith [norm_nonneg (z i)]

theorem configurationRadialSmoothingKernel_compact (n : ℕ) :
    HasCompactSupport (configurationRadialSmoothingKernel n) :=
  (isCompact_closedBall (0 : Configuration n) 2).of_isClosed_subset (isClosed_tsupport _)
    (configurationRadialSmoothingKernel_tsupport_subset n)

theorem configurationRadialSmoothingKernel_integral (n : ℕ) :
    (∫ z : Configuration n, configurationRadialSmoothingKernel n z) = 1 := by
  unfold configurationRadialSmoothingKernel
  rw [integral_fin_nat_prod_volume_eq_prod]
  simp only [planarRadialSmoothingKernel_integral, Finset.prod_const_one]

/-- Tensor radial smoothing reproduces every genuine jointly entire
function, without an integrability assumption at infinity. -/
theorem configurationRadialSmoothing_mean_value (n : ℕ)
    (F : Configuration n → ℂ) (hF : Differentiable ℂ F) (x : Configuration n) :
    (∫ y : Configuration n, configurationRadialSmoothingKernel n y • F (x-y)) = F x := by
  induction n with
  | zero =>
    have hc : ∀ y : Configuration 0, F (x-y) = F x :=
      fun y => congrArg F (Subsingleton.elim _ _)
    simp_rw [hc]
    rw [integral_smul_const, configurationRadialSmoothingKernel_integral, one_smul]
  | succ n ih =>
    let H : Configuration (n+1) → ℂ := fun y =>
      configurationRadialSmoothingKernel (n+1) y • F (x-y)
    have hH : Integrable H volume :=
      ((configurationRadialSmoothingKernel_contDiff (n+1)).continuous.smul
        (hF.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
          ((configurationRadialSmoothingKernel_compact (n+1)).smul_right)
    have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).symm
    have hcons (a : ℂ × Configuration n) :
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).symm a =
        Fin.cons a.1 a.2 := by
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    have hc : Continuous (fun a : ℂ × Configuration n => (Fin.cons a.1 a.2 : Configuration (n+1)))
        := by
      fun_prop
    have hcomp : Integrable (fun a : ℂ × Configuration n => H (Fin.cons a.1 a.2)) volume := by
      have hh := (he.integrable_comp hH.aestronglyMeasurable).mpr hH
      simpa only [Function.comp_def, hcons] using hh
    rw [← he.integral_comp' H]
    simp only [hcons]
    change (∫ a : ℂ × Configuration n, H (Fin.cons a.1 a.2) ∂
      (volume : Measure ℂ).prod (volume : Measure (Configuration n))) = F x
    have hcomp' : Integrable (fun a : ℂ × Configuration n => H (Fin.cons a.1 a.2))
      ((volume : Measure ℂ).prod (volume : Measure (Configuration n))) := hcomp
    rw [integral_prod_symm _ hcomp']
    have hinner (y : Configuration n) :
        (∫ a : ℂ, H (Fin.cons a y)) =
          configurationRadialSmoothingKernel n y • F (Fin.cons (x 0) (Fin.tail x-y)) := by
      have hd : Differentiable ℂ (fun a : ℂ => F (Fin.cons a (Fin.tail x-y))) := by
        apply hF.comp
        fun_prop
      have hmv := radial_integral_holomorphic_mean_value planarRadialSmoothingKernel
        planarRadialSmoothingKernel_contDiff.continuous planarRadialSmoothingKernel_compact
        planarRadialSmoothingKernel_radial (fun a => F (Fin.cons a (Fin.tail x-y))) hd (x 0)
      rw [planarRadialSmoothingKernel_integral, one_smul] at hmv
      have hfunc : (fun a : ℂ => H (Fin.cons a y)) =
          (fun a : ℂ => configurationRadialSmoothingKernel n y •
            (planarRadialSmoothingKernel a • F (Fin.cons (x 0-a) (Fin.tail x-y)))) := by
        funext a
        unfold H configurationRadialSmoothingKernel
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        have hsub : x-Fin.cons a y = Fin.cons (x 0-a) (Fin.tail x-y) := by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]
        rw [hsub]
        simp only [smul_smul]
        congr 1
        ring
      rw [hfunc, integral_smul, hmv]
    simp_rw [hinner]
    have hd : Differentiable ℂ (fun y : Configuration n => F (Fin.cons (x 0) y)) := by
      apply hF.comp
      fun_prop
    have hh := ih (fun y => F (Fin.cons (x 0) y)) hd (Fin.tail x)
    simpa only [Fin.cons_self_tail] using hh

end
end GinibrePoincare
