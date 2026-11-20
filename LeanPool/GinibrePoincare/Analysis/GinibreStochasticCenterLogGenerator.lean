/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterLogGenerator.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianRadialGenerator
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoScalarChain
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLampertiGenerator
public import LeanPool.GinibrePoincare.Analysis.SumRadiusCoordinates

/-! Actual center-radius gradient and logarithmic generator. The logarithm is
used only away from zero; no regularity at a zero center is asserted. -/

@[expose] public section
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibre_fderiv_centerSquared (n : ℕ) (z v : Configuration n) :
    fderiv ℝ (ginibreCenterSquared n) z v =
      2*(coordinateSum z).re*(coordinateSum v).re+
        2*(coordinateSum z).im*(coordinateSum v).im := by
  let R : Configuration n →L[ℝ] ℝ := Complex.reCLM.comp (coordinateSumCLM n)
  let I : Configuration n →L[ℝ] ℝ := Complex.imCLM.comp (coordinateSumCLM n)
  have he : ginibreCenterSquared n = fun x => R x*R x+I x*I x := by
    funext x
    simp [ginibreCenterSquared, Complex.normSq_apply, R, I]
  rw [he]
  have hd := (((R.hasFDerivAt (x := z)).mul (R.hasFDerivAt (x := z))).add ((I.hasFDerivAt (x :=
      z)).mul (I.hasFDerivAt (x := z)))).fderiv
  change (fderiv ℝ (⇑R*⇑R+⇑I*⇑I) z) v = _
  rw [hd]
  simp [R, I, add_apply, smul_apply]; ring

theorem ginibre_centerSquared_gradient_normSq (n : ℕ) (z : Configuration n) :
    realGradientNormSq (ginibreCenterSquared n) z = 4*(n : ℝ)*ginibreCenterSquared n z := by
  unfold realGradientNormSq
  simp_rw [ginibre_fderiv_centerSquared]
  have hr (j : Fin n) : coordinateSum (realCoordinateDirection j : Configuration n)=1 := by
    simp [realCoordinateDirection, coordinateDirection, coordinateSum]
  have hi (j : Fin n) : coordinateSum (imaginaryCoordinateDirection j : Configuration n)=Complex.I
      := by
    simp [imaginaryCoordinateDirection, coordinateDirection, coordinateSum]
  simp_rw [hr, hi]
  simp [ginibreCenterSquared, Complex.normSq_apply]; ring

theorem ginibre_deriv_deriv_log {r : ℝ} (hr : 0 < r) :
    deriv (deriv Real.log) r = -(r^2)⁻¹ := by
  have he : deriv Real.log =ᶠ[nhds r] (fun x => x⁻¹) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hr.ne'] with x hx
    exact (Real.hasDerivAt_log hx).deriv
  simp []

theorem ginibreRealPaperSpeedGenerator_log_centerSquared {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z)
    (hpos : 0 < ginibreCenterSquared n z) :
    ginibreRealPaperSpeedGenerator n α (fun x => Real.log (ginibreCenterSquared n x)) z =
      -(4*α/(n : ℝ)) := by
  have hf : ContDiffAt ℝ 2 (ginibreCenterSquared n) z :=
    ((contDiff_ginibreCenterSquared n).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top))).contDiffAt
  rw [ginibreRealPaperSpeedGenerator_scalar_comp α (ginibreCenterSquared n) Real.log z hf
      (Real.contDiffAt_log.mpr hpos.ne'), (Real.hasDerivAt_log hpos.ne').deriv,
    ginibre_deriv_deriv_log hpos, ginibreRealPaperSpeedGenerator_centerSquared hn α z hz,
    ginibre_centerSquared_gradient_normSq]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp; ring
end
end GinibrePoincare
