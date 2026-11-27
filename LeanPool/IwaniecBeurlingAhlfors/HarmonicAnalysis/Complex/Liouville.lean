/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Defs
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Liouville

/-!
# A Liouville lemma for `∂_zbar u = 0`

For a real-differentiable `u : ℂ → ℂ`, `∂_zbar u (z) = ½ (∂_x u (z) + i ∂_y u (z)) = 0` is the
Cauchy–Riemann equation `∂_y u (z) = i ∂_x u (z)`: the real derivative `Du (z)` is then
multiplication by `∂_x u (z)`, a complex-linear map, and `u` is complex-differentiable at `z`.

## Main results

* `HarmonicAnalysis.differentiable_complex_of_dzbar_eq_zero`: a real-differentiable `u` with
  `∂_zbar u = 0` everywhere is entire.
* `HarmonicAnalysis.eq_zero_of_dzbar_eq_zero`: if moreover `u (z) → 0` as `z → ∞`, then `u = 0`,
  by Liouville's theorem (Mathlib's `Differentiable.apply_eq_of_tendsto_cocompact`).
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace HarmonicAnalysis

/-- A real-differentiable `u : ℂ → ℂ` with `∂_zbar u = 0` everywhere is complex-differentiable: at
each
`z`, `Du (z) (i) = i Du (z) (1)`, so `Du (z) (w) = w Du (z) (1)` is complex-linear. -/
theorem differentiable_complex_of_dzbar_eq_zero {u : ℂ → ℂ} (hu : Differentiable ℝ u)
    (h : ∀ z, dzbar u z = 0) : Differentiable ℂ u := by
  intro z
  set L := fderiv ℝ u z
  -- the Cauchy–Riemann equation `L i = i L 1`
  have hI : L Complex.I = Complex.I * L 1 := by
    have h0 := h z
    simp only [dzbar, smul_eq_mul, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero,
      false_or] at h0
    linear_combination (-Complex.I) * h0 + (L Complex.I) * Complex.I_sq
  refine (differentiableAt_iff_restrictScalars ℝ (hu z)).2
    ⟨ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (L 1), ?_⟩
  ext w
  -- `L w = L (Re w • 1 + Im w • i) = Re w L 1 + Im w L i = w L 1`
  have hw : L w = (w.re : ℂ) * L 1 + (w.im : ℂ) * L Complex.I := by
    have hw' : w = w.re • (1 : ℂ) + w.im • Complex.I := by simp [Complex.re_add_im]
    conv_lhs => rw [hw']
    rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  change w * L 1 = L w
  rw [hw, hI]
  conv_lhs => rw [← Complex.re_add_im w]
  ring

/-- A Liouville lemma: a real-differentiable `u : ℂ → ℂ` with `∂_zbar u = 0` everywhere and
`u (z) → 0` as `z → ∞` vanishes identically. -/
theorem eq_zero_of_dzbar_eq_zero {u : ℂ → ℂ} (hu : Differentiable ℝ u) (h : ∀ z, dzbar u z = 0)
    (hlim : Tendsto u (cocompact ℂ) (𝓝 0)) (z : ℂ) : u z = 0 :=
  (differentiable_complex_of_dzbar_eq_zero hu h).apply_eq_of_tendsto_cocompact z hlim

end HarmonicAnalysis
