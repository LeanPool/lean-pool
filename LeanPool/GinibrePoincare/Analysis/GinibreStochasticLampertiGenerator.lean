/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticLampertiGenerator.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticSquareRootRadius
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoScalarChain

/-! Exact actual Lamperti generator, expressed solely in the relative radius. -/

@[expose] public section
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibre_deriv_deriv_sqrt {r : ℝ} (hr : 0 < r) :
    deriv (deriv Real.sqrt) r = -1/(4*(Real.sqrt r)^3) := by
  have hn : r ≠ 0 := hr.ne'
  have hs : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  have he : deriv Real.sqrt =ᶠ[nhds r] (fun x => 1/(2*Real.sqrt x)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hn] with x hx
    exact (Real.hasDerivAt_sqrt hx).deriv
  have hg : HasDerivAt (fun x : ℝ => 1/(2*Real.sqrt x)) (-1/(4*(Real.sqrt r)^3)) r := by
    have h := ((Real.hasDerivAt_sqrt hn).const_mul 2).inv (mul_ne_zero (by norm_num) hs)
    convert! h using 1
    · funext x
      simp only [one_div, Pi.inv_apply]
    · field_simp
     ; ring
  exact (hg.congr_of_eventuallyEq he).deriv

/-- The drift `(α / n) * (2γ - 1) / √r - (2α / n) * √r` of the square-root radius, at radius
`r`, where `γ = recenteredGammaShape n`. -/
def ginibreLampertiRadialDrift (n : ℕ) (α r : ℝ) : ℝ :=
  (α/(n : ℝ))*(2*(recenteredGammaShape n : ℝ)-1)/(Real.sqrt r)-
    (2*α/(n : ℝ))*Real.sqrt r

theorem ginibreLampertiRadialDrift_measurable (n : ℕ) (α : ℝ) :
    Measurable (ginibreLampertiRadialDrift n α) := by
  unfold ginibreLampertiRadialDrift
  fun_prop

theorem ginibreLampertiRadialDrift_continuousOn (n : ℕ) (α : ℝ) :
    ContinuousOn (ginibreLampertiRadialDrift n α) (Set.Ioi 0) := by
  intro r hr
  exact (continuous_const.continuousAt.div (Real.continuous_sqrt.continuousAt)
    (Real.sqrt_pos.mpr hr).ne').sub (continuous_const.mul Real.continuous_sqrt).continuousAt
        |>.continuousWithinAt

theorem ginibreRealPaperSpeedGenerator_squareRootRadius {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z) :
    ginibreRealPaperSpeedGenerator n α ginibreSquareRootRadius z =
      ginibreLampertiRadialDrift n α (pairwiseRadius z) := by
  have hρ := pairwiseRadius_pos_of_collisionFree hn z hz
  have hs : Real.sqrt (pairwiseRadius z) ≠ 0 := (Real.sqrt_pos.mpr hρ).ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hf : ContDiffAt ℝ 2 (pairwiseRadius : Configuration n → ℝ) z :=
    ((ginibre_contDiff_pairwiseRadius n).of_le
      (by exact WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top))).contDiffAt
  have hφ : ContDiffAt ℝ 2 Real.sqrt (pairwiseRadius z) := Real.contDiffAt_sqrt hρ.ne'
  change ginibreRealPaperSpeedGenerator n α (fun w => Real.sqrt (pairwiseRadius w)) z = _
  rw [ginibreRealPaperSpeedGenerator_scalar_comp α pairwiseRadius Real.sqrt z hf hφ,
    (Real.hasDerivAt_sqrt hρ.ne').deriv, ginibre_deriv_deriv_sqrt hρ,
    ginibreRealPaperSpeedGenerator_pairwiseRadius hn α z hz]
  have hg : realGradientNormSq pairwiseRadius z=4*(n : ℝ)*pairwiseRadius z :=
    ginibre_pairwiseRadius_gradient_normSq n z
  rw [hg]
  unfold ginibreLampertiRadialDrift
  have hsq := Real.sq_sqrt hρ.le
  generalize he : Real.sqrt (pairwiseRadius z)=r at hs hsq ⊢
  rw [← hsq]
  field_simp
 ; ring
end
end GinibrePoincare
