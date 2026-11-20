/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUECenterIntegrals.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUECenterSplit
/-!
# Correspondence GUE center integrals

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueFullMeasure_center_integral`.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem gueCenterCoordinate_split_symm (n : ℕ) (hn : 0<n) (t : ℝ)
    (y : (gueCenterLine n)ᗮ) :
    gueCenterCoordinate n ((gueCenterSplitEquiv n hn).symm (t, y))=t := by
  rw [gueCenterSplitEquiv_symm_apply]
  unfold gueCenterCoordinate
  rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    gueCenterUnit_norm hn, gueCenter_orthogonal]
  simp

theorem gueRawDensity_center_integral_split {n : ℕ} (hn : 0 < n) (f : ℝ → ℝ) :
    (∫x, gueRawDensity n x*f (gueCenterCoordinate n x))=
      (∫t, Real.exp (-(n : ℝ)/2*t^2)*f t)*
        (∫y : (gueCenterLine n)ᗮ, gueRawDensity n y) := by
  have hs := ((gueCenterSplit_volume_preserving n hn).symm (gueCenterSplitEquiv n hn)).integral_comp
    (gueCenterSplitEquiv n hn).symm.measurableEmbedding
    (fun x => gueRawDensity n x*f (gueCenterCoordinate n x))
  rw [← hs]
  have he (p : ℝ×(gueCenterLine n)ᗮ) :
      gueRawDensity n ((gueCenterSplitEquiv n hn).symm p)*
        f (gueCenterCoordinate n ((gueCenterSplitEquiv n hn).symm p))=
      (Real.exp (-(n : ℝ)/2*p.1^2)*f p.1)*gueRawDensity n p.2 := by
    rw [gueCenterCoordinate_split_symm, gueCenterSplitEquiv_symm_apply,
      gueRawDensity_center_factorization hn _ _ (gueCenter_orthogonal n p.2)]
    ring
  simp_rw [he]
  exact integral_prod_mul (fun t : ℝ => Real.exp (-(n : ℝ)/2*t^2)*f t)
    (fun y : (gueCenterLine n)ᗮ => gueRawDensity n y)

theorem gueCenteredDensity_partition_ne_zero {n : ℕ} (hn : 0 < n) :
    (∫y : (gueCenterLine n)ᗮ, gueRawDensity n y)≠0 := by
  have hp := gueRawDensity_center_integral_split hn (fun _ => 1)
  simp only [mul_one] at hp
  intro hz
  rw [hz, mul_zero] at hp
  exact (ne_of_gt (gueRawDensity_partition_pos hn)) hp

theorem gueFullMeasure_center_integral {n : ℕ} (hn : 0 < n) (f : ℝ → ℝ) :
    (∫x, f (gueCenterCoordinate n x) ∂gueFullMeasure n)=
      (∫t, Real.exp (-(n : ℝ)/2*t^2)*f t)/(∫t : ℝ, Real.exp (-(n : ℝ)/2*t^2)) := by
  rw [gueFullMeasure_integral, gueRawDensity_center_integral_split hn]
  have hp := gueRawDensity_center_integral_split hn (fun _ => 1)
  simp only [mul_one] at hp
  rw [hp]
  field_simp [gueCenteredDensity_partition_ne_zero hn]

end
end GinibrePoincare
