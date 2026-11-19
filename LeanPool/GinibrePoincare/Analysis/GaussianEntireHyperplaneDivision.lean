/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianEntireHyperplaneDivision.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianEntireDirectionalDerivative
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Entire division by a linear functional

Choose `v` with `ℓ v = 1` and project `z` onto `ker ℓ` by
`P z = z - ℓ z • v`. The path `A t z = P z + t • (ℓ z • v)` joins the
hyperplane to `z`. Integrating the directional derivative of `f` along this path
defines the quotient everywhere, including where `ℓ z = 0`.

Entire differentiability of the directional derivative and differentiation of a
parameter integral prove that the quotient is entire. The fundamental theorem
of calculus recovers `f z = ℓ z * g z`, since `f (P z) = 0`. This construction
avoids defining a quotient by pointwise division at the hyperplane.
-/

@[expose] public section

open MeasureTheory
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- Global entire division by a nonzero linear functional whose hyperplane
annihilates the numerator. The quotient is an explicit Hadamard integral. -/
theorem gaussian_entire_hyperplane_division {n : ℕ}
    (ℓ : Configuration n →L[ℂ] ℂ) (v : Configuration n) (hv : ℓ v = 1)
    (f : Configuration n → ℂ) (hf : Differentiable ℂ f)
    (hzero : ∀ z, ℓ z = 0 → f z = 0) :
    ∃ g : Configuration n → ℂ, Differentiable ℂ g ∧
      ∀ z, f z = ℓ z * g z := by
  let P : Configuration n →L[ℂ] Configuration n :=
    ContinuousLinearMap.id ℂ (Configuration n) - ℓ.smulRight v
  let A : ℝ → Configuration n →L[ℂ] Configuration n :=
    fun t => P + (t : ℂ) • ℓ.smulRight v
  let d : Configuration n → ℂ := fun z => fderiv ℂ f z v
  have hd : Differentiable ℂ d := gaussian_entire_directional_fderiv_differentiable hf v
  have hA : Continuous A := by
    exact continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  have hAz : Continuous (fun p : Configuration n × ℝ => A p.2 p.1) :=
    (hA.comp continuous_snd).clm_apply continuous_fst
  let F : Configuration n → ℝ → ℂ := fun z t => d (A t z)
  let F' : Configuration n → ℝ → Configuration n →L[ℂ] ℂ :=
    fun z t => (fderiv ℂ d (A t z)).comp (A t)
  have hF : Continuous ↿F := hd.continuous.comp hAz
  have hF' : Continuous ↿F' :=
    (((gaussian_entire_contDiff_complex_one hd).continuous_fderiv (by norm_num)).comp hAz).clm_comp
      (hA.comp continuous_snd)
  have hdiff : ∀ z t, HasFDerivAt (fun w => F w t) (F' z t) z := by
    intro z t
    exact (hd (A t z)).hasFDerivAt.comp z (A t).hasFDerivAt
  let g : Configuration n → ℂ := fun z => ∫ t in (0 : ℝ)..1, F z t
  have hg : Differentiable ℂ g :=
    gaussian_entire_parameter_intervalIntegral F F' hF hF' hdiff 0 1
  refine ⟨g, hg, ?_⟩
  intro z
  have hAz_eq : ∀ t : ℝ, A t z = P z + t • (ℓ z • v) := by
    intro t
    simp only [A, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
    congr 1
  have hcurve : ∀ t : ℝ, HasDerivAt (fun s : ℝ => A s z) (ℓ z • v) t := by
    intro t
    simp_rw [hAz_eq]
    simpa using ((hasDerivAt_id t).smul_const (ℓ z • v)).const_add (P z)
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (A s z)) (ℓ z * F z t) t := by
    intro t
    have h := ((hf (A t z)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hcurve t)
    change HasDerivAt (fun s : ℝ => f (A s z)) ((fderiv ℂ f (A t z)) (ℓ z • v)) t at h
    simpa only [F, d,
      map_smul, smul_eq_mul] using h
  have hcont : Continuous (fun t : ℝ => ℓ z * F z t) :=
    continuous_const.mul (hd.continuous.comp ((hA.clm_apply continuous_const)))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := (1 : ℝ)) (fun t _ => hderiv t) (hcont.intervalIntegrable 0 1)
  have hP : ℓ (P z) = 0 := by
    simp [P, hv]
  have h0 : A 0 z = P z := by simp [A]
  have h1 : A 1 z = z := by simp [A, P]
  rw [h0, h1, hzero (P z) hP, sub_zero, intervalIntegral.integral_const_mul] at hFTC
  exact hFTC.symm

end
end GinibrePoincare
