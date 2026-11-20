/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/StrongConvexQuantileTransport.lean.
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

public import LeanPool.GinibrePoincare.Analysis.StrongConvexQuantileCalculus
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Strong convex quantile transport

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `increasingCDFQuantileOn_congr`, `cdfQuantileTransport_hasDerivAt`,
`cdfQuantileTransport_derivative_bound`, `scalar_hasDerivAt_lipschitz`.
-/

@[expose] public section

open Set Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

theorem increasingCDFQuantileOn_congr (F G : ℝ → ℝ) (s : Set ℝ)
    (hF : StrictMonoOn F s) (hrF : F '' s = Ioo 0 1)
    (hG : StrictMonoOn G s) (hrG : G '' s = Ioo 0 1) (he : F = G) :
    increasingCDFQuantileOn F s hF hrF = increasingCDFQuantileOn G s hG hrG := by
  subst G
  rfl

/-- The monotone transport between two genuine cumulative distributions. -/
def cdfQuantileTransport (F G : ℝ → ℝ)
    (hm : StrictMonoOn G (Ioi 0)) (hr : G '' Ioi 0 = Ioo 0 1) : ℝ → ℝ :=
  increasingCDFQuantileOn G (Ioi 0) hm hr ∘ F

theorem cdfQuantileTransport_hasDerivAt (F p G q : ℝ → ℝ)
    (hF : ∀ x, HasDerivAt F (p x) x) (hFr : F '' univ = Ioo 0 1)
    (hm : StrictMonoOn G (Ioi 0)) (hr : G '' Ioi 0 = Ioo 0 1)
    (hG : ∀ x ∈ Ioi 0, HasDerivAt G (q x) x)
    (hq : ∀ x ∈ Ioi 0, q x ≠ 0) (x : ℝ) :
    HasDerivAt (cdfQuantileTransport F G hm hr)
      ((q (cdfQuantileTransport F G hm hr x))⁻¹ * p x) x := by
  have hx : F x ∈ Ioo (0 : ℝ) 1 := hFr ▸ mem_image_of_mem F (mem_univ x)
  exact (increasingCDFQuantileOn_hasDerivAt G q (Ioi 0) hm hr hG hq (F x) hx).comp x (hF x)

/-- A density-profile lower bound gives the sharp contraction bound for
monotone quantile transport. This is a calculus consequence of the profile
comparison, not an assumed transport theorem. -/
theorem cdfQuantileTransport_derivative_bound (F p G q : ℝ → ℝ)
    (hFm : StrictMono F) (hFr : F '' univ = Ioo 0 1)
    (hm : StrictMonoOn G (Ioi 0)) (hr : G '' Ioi 0 = Ioo 0 1)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x ∈ Ioi 0, 0 < q x)
    (c : ℝ) (hc : 0 < c)
    (hcomp : ∀ u ∈ Ioo (0 : ℝ) 1,
      c * densityQuantileProfile F p univ (hFm.strictMonoOn univ) hFr u ≤
        densityQuantileProfile G q (Ioi 0) hm hr u) (x : ℝ) :
    0 ≤ (q (cdfQuantileTransport F G hm hr x))⁻¹ * p x ∧
      (q (cdfQuantileTransport F G hm hr x))⁻¹ * p x ≤ c⁻¹ := by
  have hx : F x ∈ Ioo (0 : ℝ) 1 := hFr ▸ mem_image_of_mem F (mem_univ x)
  have hsrc : increasingCDFQuantileOn F univ (hFm.strictMonoOn univ) hFr (F x) = x := by
    apply hFm.injective
    exact increasingCDFQuantileOn_right_inverse F univ (hFm.strictMonoOn univ) hFr (F x) hx
  have htgt := increasingCDFQuantileOn_mem G (Ioi 0) hm hr (F x) hx
  have hpos : 0 < q (cdfQuantileTransport F G hm hr x) := hq _ htgt
  have h := hcomp (F x) hx
  simp only [densityQuantileProfile, ite_eq_left hx, hsrc] at h
  change c * p x ≤ q (cdfQuantileTransport F G hm hr x) at h
  refine ⟨mul_nonneg (inv_nonneg.mpr hpos.le) (hp x), ?_⟩
  rw [mul_comm, ← div_eq_mul_inv, inv_eq_one_div]
  exact (div_le_div_iff₀ hpos hc).mpr (by simpa only [one_mul, mul_one, mul_comm] using h)

/-- A scalar derivative bound gives a genuine global Lipschitz estimate. -/
theorem scalar_hasDerivAt_lipschitz (T D : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hD : ∀ x, HasDerivAt T (D x) x)
    (hb : ∀ x, 0 ≤ D x ∧ D x ≤ c) :
    LipschitzWith (Real.toNNReal c) T := by
  apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (hD x).differentiableAt)
  intro x
  apply NNReal.coe_le_coe.mp
  change ‖fderiv ℝ T x‖ ≤ (Real.toNNReal c : ℝ)
  rw [← norm_deriv_eq_norm_fderiv, (hD x).deriv,
    Real.norm_eq_abs, abs_of_nonneg (hb x).1, Real.coe_toNNReal c hc]
  exact (hb x).2

end
end GinibrePoincare
