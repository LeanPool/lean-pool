/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterLampertiGenerator.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterLogGenerator
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoScalarChain

/-! Exact actual square-root center generator, away from a zero center. -/

@[expose] public section
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- The square root of `ginibreCenterSquared n z`, i.e. the modulus of the coordinate sum. -/
def ginibreSquareRootCenter (n : ℕ) (z : Configuration n) : ℝ :=
  Real.sqrt (ginibreCenterSquared n z)

/-- The Lamperti drift `(α / n) / √r - (2α / n) * √r` of the center modulus, evaluated at the
squared modulus `r`. -/
def ginibreLampertiCenterDrift (n : ℕ) (α r : ℝ) : ℝ :=
  (α/(n : ℝ))*(1)/(Real.sqrt r)-
    (2*α/(n : ℝ))*Real.sqrt r

theorem ginibreLampertiCenterDrift_measurable (n : ℕ) (α : ℝ) :
    Measurable (ginibreLampertiCenterDrift n α) := by
  unfold ginibreLampertiCenterDrift
  fun_prop

theorem ginibreLampertiCenterDrift_continuousOn (n : ℕ) (α : ℝ) :
    ContinuousOn (ginibreLampertiCenterDrift n α) (Set.Ioi 0) := by
  intro r hr
  exact (continuous_const.continuousAt.div (Real.continuous_sqrt.continuousAt)
    (Real.sqrt_pos.mpr hr).ne').sub (continuous_const.mul Real.continuous_sqrt).continuousAt
        |>.continuousWithinAt

theorem ginibreRealPaperSpeedGenerator_squareRootCenter {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z)
    (hcenter : 0 < ginibreCenterSquared n z) :
    ginibreRealPaperSpeedGenerator n α (ginibreSquareRootCenter n) z =
      ginibreLampertiCenterDrift n α (ginibreCenterSquared n z) := by
  have hρ := hcenter
  have hs : Real.sqrt (ginibreCenterSquared n z) ≠ 0 := (Real.sqrt_pos.mpr hρ).ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hf : ContDiffAt ℝ 2 (ginibreCenterSquared n : Configuration n → ℝ) z :=
    ((contDiff_ginibreCenterSquared n).of_le
      (by exact WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top))).contDiffAt
  have hφ : ContDiffAt ℝ 2 Real.sqrt (ginibreCenterSquared n z) := Real.contDiffAt_sqrt hρ.ne'
  change ginibreRealPaperSpeedGenerator n α (fun w => Real.sqrt (ginibreCenterSquared n w)) z = _
  rw [ginibreRealPaperSpeedGenerator_scalar_comp α (ginibreCenterSquared n) Real.sqrt z hf hφ,
    (Real.hasDerivAt_sqrt hρ.ne').deriv, ginibre_deriv_deriv_sqrt hρ,
    ginibreRealPaperSpeedGenerator_centerSquared hn α z hz]
  have hg : realGradientNormSq (ginibreCenterSquared n) z=4*(n : ℝ)*ginibreCenterSquared n z :=
    ginibre_centerSquared_gradient_normSq n z
  rw [hg]
  unfold ginibreLampertiCenterDrift
  have hsq := Real.sq_sqrt hρ.le
  generalize he : Real.sqrt (ginibreCenterSquared n z)=r at hs hsq ⊢
  rw [← hsq]
  field_simp; ring
end
end GinibrePoincare
