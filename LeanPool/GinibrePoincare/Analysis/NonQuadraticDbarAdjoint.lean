/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticDbarAdjoint.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticDbarBochner

/-! # Weighted planar integration by parts
The concrete ∂bar adjoint is paired with the derivative in the actual
weighted real Hilbert pairing. -/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- Weighted integration by parts for either Cartesian direction. -/
theorem planar_weighted_derivative_ibp (W f g : ℂ → ℝ) (v : ℂ)
    (hv : v = 1 ∨ v = Complex.I) (hW : ContDiff ℝ 1 W)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport f) :
    (∫ z, f z * planarDerivative v g z * Real.exp (-W z)) =
      ∫ z, (planarDerivative v W z * f z - planarDerivative v f z) * g z *
        Real.exp (-W z) := by
  let w := fun z => Real.exp (-W z)
  let H := fun z => f z * g z * w z
  have hw : ContDiff ℝ 1 w := Real.contDiff_exp.comp hW.neg
  have hH : ContDiff ℝ 1 H := (hf.mul hg).mul hw
  have hHc : HasCompactSupport H := hc.mul_right.mul_right
  have hz : (∫ z, planarDerivative v H z) = 0 := by
    rcases hv with rfl | rfl
    · exact integral_fderiv_complex_real_eq_zero H hH hHc
    · exact integral_fderiv_complex_imag_eq_zero H hH hHc
  have hpoint (z : ℂ) : planarDerivative v H z =
      planarDerivative v f z * g z * w z + f z * planarDerivative v g z * w z -
        planarDerivative v W z * f z * g z * w z := by
    have h := ((hf.differentiable (by norm_num) z).hasFDerivAt.mul
      (hg.differentiable (by norm_num) z).hasFDerivAt).mul
      (hW.differentiable (by norm_num) z).hasFDerivAt.neg.exp
    have he := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) h.fderiv
    change fderiv ℝ H z v = _ at he
    unfold planarDerivative
    rw [he]
    simp only [add_apply, smul_apply,
      neg_apply, smul_eq_mul]
    dsimp [w]
    ring
  have hDf : Continuous (planarDerivative v f) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDg : Continuous (planarDerivative v g) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDW : Continuous (planarDerivative v W) :=
    (hW.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hi1 : Integrable (fun z => planarDerivative v f z * g z * w z) :=
    ((hDf.mul hg.continuous).mul hw.continuous).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v |>.mul_right |>.mul_right)
  have hi2 : Integrable (fun z => f z * planarDerivative v g z * w z) :=
    ((hf.continuous.mul hDg).mul hw.continuous).integrable_of_hasCompactSupport
      (hc.mul_right.mul_right)
  have hi3 : Integrable (fun z => planarDerivative v W z * f z * g z * w z) :=
    (((hDW.mul hf.continuous).mul hg.continuous).mul hw.continuous).integrable_of_hasCompactSupport
      (hc.mul_left.mul_right.mul_right)
  simp_rw [hpoint] at hz
  rw [integral_sub
    (f := fun z => planarDerivative v f z * g z * w z + f z * planarDerivative v g z * w z)
    (g := fun z => planarDerivative v W z * f z * g z * w z)
    (hi1.add hi2) hi3,
    integral_add (f := fun z => planarDerivative v f z * g z * w z)
      (g := fun z => f z * planarDerivative v g z * w z) hi1 hi2] at hz
  have ht : (fun z => (planarDerivative v W z * f z - planarDerivative v f z) * g z * w z) =
      fun z => planarDerivative v W z * f z * g z * w z - planarDerivative v f z * g z * w z := by
    funext z
    ring
  change (∫ z, f z * planarDerivative v g z * w z) = _
  rw [show (fun z => (planarDerivative v W z * f z - planarDerivative v f z) * g z * Real.exp (-W
      z)) =
      (fun z => (planarDerivative v W z * f z - planarDerivative v f z) * g z * w z) from rfl,
    ht, integral_sub hi3 hi1]
  linarith

/-- The actual weighted real Hilbert adjoint pairing, in components.
Only the adjoint test needs compact support. -/
theorem planarDbar_adjoint_pairing_of_parts (W a b c d : ℂ → ℝ)
    (hW : ContDiff ℝ 1 W) (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (hc : ContDiff ℝ 1 c) (hd : ContDiff ℝ 1 d)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b) :
    (∫ z, ((planarDbarAdjointOfParts W a b z).re * c z +
      (planarDbarAdjointOfParts W a b z).im * d z) * Real.exp (-W z)) =
    ∫ z, (a z * (planarDbarOfParts c d z).re +
      b z * (planarDbarOfParts c d z).im) * Real.exp (-W z) := by
  let w := fun z => Real.exp (-W z)
  let Hx := fun z => (-1 / 2 : ℝ) * (a z * c z + b z * d z) * w z
  let Hy := fun z => (-1 / 2 : ℝ) * (b z * c z - a z * d z) * w z
  let R := fun z => (a z * (planarDbarOfParts c d z).re +
    b z * (planarDbarOfParts c d z).im) * w z
  have hw : ContDiff ℝ 1 w := Real.contDiff_exp.comp hW.neg
  have hHx : ContDiff ℝ 1 Hx :=
    (contDiff_const.mul ((ha.mul hc).add (hb.mul hd))).mul hw
  have hHy : ContDiff ℝ 1 Hy :=
    (contDiff_const.mul ((hb.mul hc).sub (ha.mul hd))).mul hw
  have hHxc : HasCompactSupport Hx :=
    (hca.mul_right.add hcb.mul_right).mul_left.mul_right
  have hHyc : HasCompactSupport Hy :=
    (hcb.mul_right.sub hca.mul_right).mul_left.mul_right
  have hDx (z : ℂ) : planarDerivative 1 Hx z = (-1 / 2 : ℝ) *
      ((planarDerivative 1 a z * c z + a z * planarDerivative 1 c z +
        planarDerivative 1 b z * d z + b z * planarDerivative 1 d z) * w z -
        (a z * c z + b z * d z) * planarDerivative 1 W z * w z) := by
    have h := (((ha.differentiable (by norm_num) z).hasFDerivAt.mul
      (hc.differentiable (by norm_num) z).hasFDerivAt).add
      ((hb.differentiable (by norm_num) z).hasFDerivAt.mul
      (hd.differentiable (by norm_num) z).hasFDerivAt)).const_mul (-1 / 2 : ℝ) |>.mul
      (hW.differentiable (by norm_num) z).hasFDerivAt.neg.exp
    have he := congrArg (fun L : ℂ →L[ℝ] ℝ => L 1) h.fderiv
    change fderiv ℝ Hx z 1 = _ at he
    unfold planarDerivative
    rw [he]
    simp only [add_apply, smul_apply, neg_apply, smul_eq_mul]
    dsimp [w]
    ring
  have hDy (z : ℂ) : planarDerivative Complex.I Hy z = (-1 / 2 : ℝ) *
      ((planarDerivative Complex.I b z * c z + b z * planarDerivative Complex.I c z -
        (planarDerivative Complex.I a z * d z + a z * planarDerivative Complex.I d z)) * w z -
        (b z * c z - a z * d z) * planarDerivative Complex.I W z * w z) := by
    have h := (((hb.differentiable (by norm_num) z).hasFDerivAt.mul
      (hc.differentiable (by norm_num) z).hasFDerivAt).sub
      ((ha.differentiable (by norm_num) z).hasFDerivAt.mul
      (hd.differentiable (by norm_num) z).hasFDerivAt)).const_mul (-1 / 2 : ℝ) |>.mul
      (hW.differentiable (by norm_num) z).hasFDerivAt.neg.exp
    have he := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) h.fderiv
    change fderiv ℝ Hy z Complex.I = _ at he
    unfold planarDerivative
    rw [he]
    simp only [add_apply, sub_apply, 
      smul_apply, neg_apply, smul_eq_mul]
    dsimp [w]
    ring
  have hpoint (z : ℂ) :
      ((planarDbarAdjointOfParts W a b z).re * c z +
      (planarDbarAdjointOfParts W a b z).im * d z) * w z =
      R z + planarDerivative 1 Hx z + planarDerivative Complex.I Hy z := by
    rw [hDx, hDy]
    simp only [planarDbarAdjointOfParts, planarDbarOfParts, R]
    ring
  have hD (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) (v : ℂ) : Continuous (planarDerivative v f) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hRc : Continuous R :=
    ((ha.continuous.mul (((hD c hc 1).sub (hD d hd Complex.I)).div_const 2)).add
      (hb.continuous.mul (((hD d hd 1).add (hD c hc Complex.I)).div_const 2))).mul hw.continuous
  have hRcompact : HasCompactSupport R := (hca.mul_right.add hcb.mul_right).mul_right
  have hRI : Integrable R := hRc.integrable_of_hasCompactSupport hRcompact
  have hDxI : Integrable (planarDerivative 1 Hx) :=
    (hD Hx hHx 1).integrable_of_hasCompactSupport (hHxc.fderiv_apply ℝ 1)
  have hDyI : Integrable (planarDerivative Complex.I Hy) :=
    (hD Hy hHy Complex.I).integrable_of_hasCompactSupport (hHyc.fderiv_apply ℝ Complex.I)
  change (∫ z, ((planarDbarAdjointOfParts W a b z).re * c z +
    (planarDbarAdjointOfParts W a b z).im * d z) * w z) = ∫ z, R z
  simp_rw [hpoint]
  rw [integral_add (f := fun z => R z + planarDerivative 1 Hx z)
      (g := fun z => planarDerivative Complex.I Hy z) (hRI.add hDxI) hDyI,
    integral_add (f := R) (g := fun z => planarDerivative 1 Hx z) hRI hDxI]
  have hx := integral_fderiv_complex_real_eq_zero Hx hHx hHxc
  have hy := integral_fderiv_complex_imag_eq_zero Hy hHy hHyc
  change _ + (∫ z, fderiv ℝ Hx z 1) + (∫ z, fderiv ℝ Hy z Complex.I) = _
  rw [hx, hy]
  simp

/-- Concrete complex operators satisfy the weighted real Hilbert adjoint identity. -/
theorem planarDbar_real_adjoint_pairing (W : ℂ → ℝ) (f g : ℂ → ℂ)
    (hW : ContDiff ℝ 1 W) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfc : HasCompactSupport f) :
    (∫ z, (star (planarDbarAdjoint W f z) * g z).re * Real.exp (-W z)) =
      ∫ z, (star (f z) * planarDbar g z).re * Real.exp (-W z) := by
  have h := planarDbar_adjoint_pairing_of_parts W
    (fun z => (f z).re) (fun z => (f z).im) (fun z => (g z).re) (fun z => (g z).im)
    hW (Complex.reCLM.contDiff.comp hf) (Complex.imCLM.contDiff.comp hf)
    (Complex.reCLM.contDiff.comp hg) (Complex.imCLM.contDiff.comp hg)
    (hfc.comp_left (g := Complex.re) rfl) (hfc.comp_left (g := Complex.im) rfl)
  simp_rw [planarDbarAdjointOfParts_eq W f (hf.differentiable (by norm_num)),
    planarDbarOfParts_eq g (hg.differentiable (by norm_num))] at h
  simpa [Complex.mul_re] using h

/-- Wirtinger ∂bar commutes with multiplication by a fixed complex scalar. -/
theorem planarDbar_const_mul (f : ℂ → ℂ) (hf : Differentiable ℝ f) (c z : ℂ) :
    planarDbar (fun w => c * f w) z = c * planarDbar f z := by
  unfold planarDbar
  rw [fderiv_const_mul (hf z) c]
  simp only [smul_apply, smul_eq_mul]
  ring

end
end GinibrePoincare
