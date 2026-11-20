/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryLocalDolbeaultCoordinate.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultDifferential
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenParametric

/-!
# Correspondence auxiliary local Dolbeault coordinate

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `localizedCauchyGreenPotential_solves`,
`localizedCauchyGreenPotential_transverse_CR`, `localDolbeault_smooth_residual_CR_local`.
-/

@[expose] public section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem finiteComplexDbar_last_slice (F : P × ℂ → ℂ)
    (hF : ContDiff ℝ ∞ F) (p : P) (z : ℂ) :
    finiteComplexDbar (0, 1) (0, Complex.I) F (p, z) =
      planarDbar (fun w => F (p, w)) z := by
  have h := (hF.differentiable (by simp) (p, z)).hasFDerivAt.comp z
    ((hasFDerivAt_const p z).prodMk (hasFDerivAt_id z))
  have h' : HasFDerivAt (fun w => F (p, w))
      ((fderiv ℝ F (p, z)).comp
        ((0 : ℂ →L[ℝ] P).prod (ContinuousLinearMap.id ℝ ℂ))) z := by
    simpa only [Function.comp_def] using! h
  simp only [finiteComplexDbar, planarDbar, h'.fderiv]
  simp

/-- The actual coordinate solver, with an ordinary smooth compactly
supported cutoff in the solved plane. -/
def localizedCauchyGreenPotential (χ : ℂ → ℂ) (a : P → ℂ → ℂ) : P × ℂ → ℂ :=
  parametricCauchyGreenPotential (fun p z => χ z * a p z)

theorem localizedCauchyGreenPotential_contDiff (χ : ℂ → ℂ) (a : P → ℂ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) :
    ContDiff ℝ ∞ (localizedCauchyGreenPotential χ a) := by
  apply parametricCauchyGreenPotential_contDiff _
    ((hχ.comp contDiff_snd).mul ha) (tsupport χ) hc
  intro p z hz
  rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]

theorem localizedCauchyGreenPotential_solves (χ : ℂ → ℂ) (a : P → ℂ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (p : P) (z : ℂ) :
    finiteComplexDbar (0, 1) (0, Complex.I) (localizedCauchyGreenPotential χ a) (p, z) =
      χ z * a p z := by
  rw [finiteComplexDbar_last_slice _
    (localizedCauchyGreenPotential_contDiff χ a hχ hc ha)]
  exact parametricCauchyGreenPotential_last_dbar _
    ((hχ.comp contDiff_snd).mul ha) (tsupport χ) hc
    (fun p z hz => by rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]) p z

theorem localizedCauchyGreenPotential_transverse_CR_on_support (χ : ℂ → ℂ)
    (a : P → ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (v w : P) (q : P × ℂ)
    (hCR : ∀ z ∈ tsupport χ,
      finiteComplexDbar (v, 0) (w, 0) (Function.uncurry a) (q.1, z) = 0) :
    finiteComplexDbar (v, 0) (w, 0) (localizedCauchyGreenPotential χ a) q = 0 := by
  have hd (z : ℂ) (b : P) :
      fderiv ℝ (fun x : P × ℂ => χ x.2 * a x.1 x.2) (q.1, z) (b, 0) =
        χ z * fderiv ℝ (Function.uncurry a) (q.1, z) (b, 0) := by
    have hx := (hχ.differentiable (by simp) z).hasFDerivAt.comp (q.1, z)
      (ContinuousLinearMap.snd ℝ P ℂ).hasFDerivAt
    have hm := hx.mul (ha.differentiable (by simp) (q.1, z)).hasFDerivAt
    have hm' : HasFDerivAt (fun x : P × ℂ => χ x.2 * a x.1 x.2)
        (χ z • fderiv ℝ (Function.uncurry a) (q.1, z) +
          a q.1 z • ((fderiv ℝ χ z).comp (ContinuousLinearMap.snd ℝ P ℂ))) (q.1, z) := by
      simpa only [Function.comp_def, Pi.mul_apply, Function.uncurry,
        ContinuousLinearMap.coe_snd] using! hm
    rw [hm'.fderiv]
    simp
  have h := parametricCauchyGreenPotential_transverse_CR_at
    (fun p z => χ z * a p z) ((hχ.comp contDiff_snd).mul ha)
    (tsupport χ) hc (fun p z hz => by rw [image_eq_zero_of_notMem_tsupport hz, zero_mul])
    v w q (fun z => by
      change fderiv ℝ (fun x : P × ℂ => χ x.2 * a x.1 x.2) (q.1, z) (v, 0) +
        Complex.I * fderiv ℝ (fun x : P × ℂ => χ x.2 * a x.1 x.2) (q.1, z) (w, 0) = 0
      rw [hd z v, hd z w]
      by_cases hzs : z ∈ tsupport χ
      · have hz := hCR z hzs
        simp only [finiteComplexDbar] at hz
        have hz' : fderiv ℝ (Function.uncurry a) (q.1, z) (v, 0) +
            Complex.I * fderiv ℝ (Function.uncurry a) (q.1, z) (w, 0) = 0 := by
          exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
        linear_combination χ z * hz'
      · simp only [image_eq_zero_of_notMem_tsupport hzs, zero_mul, mul_zero, add_zero])
  simpa only [finiteComplexDbar, localizedCauchyGreenPotential, mul_zero] using!
    congrArg (fun b : ℂ => (1/2 : ℂ)*b) h

theorem localizedCauchyGreenPotential_transverse_CR (χ : ℂ → ℂ)
    (a : P → ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (v w : P) (q : P × ℂ)
    (hCR : ∀ z, finiteComplexDbar (v, 0) (w, 0) (Function.uncurry a) (q.1, z) = 0) :
    finiteComplexDbar (v, 0) (w, 0) (localizedCauchyGreenPotential χ a) q = 0 :=
  localizedCauchyGreenPotential_transverse_CR_on_support χ a hχ hc ha v w q (fun z _ => hCR z)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finiteComplexDbar_congr_of_eventuallyEq {f g : E → ℂ}
    {x v w : E} (h : f =ᶠ[𝓝 x] g) :
    finiteComplexDbar v w f x = finiteComplexDbar v w g x := by
  simp only [finiteComplexDbar, h.fderiv_eq (𝕜 := ℝ)]

/-- The residual is holomorphic in the solved direction using only a
local solution identity. No globally closed extension is required. -/
theorem localDolbeault_smooth_residual_CR_local (f g u : E → ℂ)
    (_ : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hu : ContDiff ℝ ∞ u)
    (v w a b x : E)
    (hsolve : finiteComplexDbar v w u =ᶠ[𝓝 x] f)
    (hclosed : finiteComplexDbar a b f x = finiteComplexDbar v w g x) :
    finiteComplexDbar v w (g-finiteComplexDbar a b u) x = 0 := by
  rw [finiteComplexDbar_sub g _ (hg.differentiable (by simp))
    ((finiteComplexDbar_contDiff u hu a b).differentiable (by simp)),
    finiteComplexDbar_commute u hu v w a b x,
    finiteComplexDbar_congr_of_eventuallyEq hsolve,← hclosed, sub_self]

end
end GinibrePoincare
