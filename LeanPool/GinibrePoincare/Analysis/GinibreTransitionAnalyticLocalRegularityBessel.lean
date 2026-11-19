/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityBessel.lean.
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

public import Mathlib.Analysis.Distribution.Sobolev

/-! Actual distributional elliptic equations gain one Sobolev derivative from
L² divergence data. This follows from the concrete Fourier/Bessel operators;
no derivative or regularity certificate is assumed. -/

@[expose] public section
open TemperedDistribution FourierTransform MeasureTheory
open scoped SchwartzMap LineDeriv Laplacian
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem ginibreLocalRegularity_fourierMultiplier_add
    (g h : E → ℂ) (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth)
    (u : 𝓢'(E, ℂ)) :
    fourierMultiplierCLM ℂ (g+h) u = fourierMultiplierCLM ℂ g u+fourierMultiplierCLM ℂ h u := by
  simp only [fourierMultiplierCLM_apply, smulLeftCLM_add hg hh, add_apply]
  exact map_add _ _ _

theorem ginibreLocalRegularity_bessel_two_eq
    (u : 𝓢'(E, ℂ)) :
    besselPotential E ℂ 2 u = u+(-(2*Real.pi)^2 : ℂ)⁻¹ • (Δ u) := by
  have hg : (fun x : E => Complex.ofReal (‖x‖^2)).HasTemperateGrowth := by fun_prop
  have he : (fun x : E => ((1+‖x‖^2)^(2/(2 : ℝ)) : ℝ)) = fun x => 1+‖x‖^2 := by
    funext x
    norm_num
  simp only [besselPotential, show (2 : ℝ)/2=1 by norm_num, Real.rpow_one]
  have hs : (fun x : E => Complex.ofReal (1+‖x‖^2)) =
      (fun _ : E => (1 : ℂ))+(fun x : E => Complex.ofReal (‖x‖^2)) := by
    funext x
    simp
  rw [hs, ginibreLocalRegularity_fourierMultiplier_add _ _ (by fun_prop) hg,
    fourierMultiplierCLM_const]
  simp only [ContinuousLinearMap.id_apply, one_smul]
  rw [laplacian_eq_fourierMultiplierCLM]
  rw [← algebraMap_smul ℂ (-(2*Real.pi)^2)
    ((fourierMultiplierCLM ℂ (fun x : E => Complex.ofReal (‖x‖^2))) u)]
  rw [show (algebraMap ℝ ℂ) (-(2*Real.pi)^2) = (-(2*Real.pi)^2 : ℂ) by
    change Complex.ofReal (-(2*Real.pi)^2) = _
    simp]
  rw [smul_smul]
  have hc : (-(2*Real.pi)^2 : ℂ) ≠ 0 := by
    exact neg_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr
        Real.pi_ne_zero)))
  rw [inv_mul_cancel₀ hc, one_smul]

theorem ginibreLocalRegularity_elliptic_divergence_memSobolev
    {ι : Type*} [Fintype ι] (u h : 𝓢'(E, ℂ)) (F : ι → 𝓢'(E, ℂ)) (v : ι → E)
    (hu : MemSobolev 0 2 u) (hh : MemSobolev 0 2 h)
    (hF : ∀ i, MemSobolev 0 2 (F i))
    (heq : Δ u = h + ∑ i, ∂_{v i} (F i)) :
    MemSobolev 1 2 u := by
  have hder (i : ι) : MemSobolev (-1) 2 (∂_{v i} (F i)) := by
    simpa using (hF i).lineDerivOp (m := v i)
  have hsum (s : Finset ι) : MemSobolev (-1) 2 (∑ i ∈ s, ∂_{v i} (F i)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simpa only [Finset.sum_insert hi] using (hder i).add ih
  have hr : MemSobolev (-1) 2 (besselPotential E ℂ 2 u) := by
    rw [ginibreLocalRegularity_bessel_two_eq, heq]
    exact (hu.mono (by norm_num)).add
      (((hh.mono (by norm_num)).add (by simpa using hsum Finset.univ)).smul _)
  have h := (memSobolev_besselPotential_iff (s := (-1 : ℝ)) (r := (2 : ℝ))).mp hr
  norm_num at h
  exact h

end
end GinibrePoincare
