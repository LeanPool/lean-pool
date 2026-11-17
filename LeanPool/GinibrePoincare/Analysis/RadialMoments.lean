/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/RadialMoments.lean.
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

public import Mathlib.MeasureTheory.Integral.Gamma

/-! # Radial Gaussian moments -/


@[expose] public section


open MeasureTheory Set Real

namespace GinibrePoincare

noncomputable section

/-- The exact radial moment appearing in polar integration of a complex
Gaussian monomial. -/
theorem integral_pow_mul_exp_neg_mul_sq_Ioi (n a : ℕ) (hn : 0 < n) :
    ∫ r : ℝ in Ioi 0, r ^ (2 * a + 1) * Real.exp (-(n : ℝ) * r ^ 2) =
      (a.factorial : ℝ) / (2 * (n : ℝ) ^ (a + 1)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (2 * a + 1 : ℝ)) (b := (n : ℝ))
    (by norm_num) (by
      have ha : (0 : ℝ) ≤ a := by positivity
      linarith) hnR
  have hintegrand :
      (fun r : ℝ ↦ r ^ (2 * a + 1) * Real.exp (-(n : ℝ) * r ^ 2)) =ᵐ[volume.restrict (Ioi 0)]
        (fun r : ℝ ↦ r ^ (2 * a + 1 : ℝ) *
          Real.exp (-(n : ℝ) * r ^ (2 : ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hp : r ^ (2 * a + 1) = r ^ (2 * (a : ℝ) + 1) := by
      rw [← Real.rpow_natCast r (2 * a + 1)]
      congr 1
      push_cast
      rfl
    have htwo : r ^ (2 : ℕ) = r ^ (2 : ℝ) :=
      (Real.rpow_natCast r 2).symm
    rw [hp, htwo]
  rw [integral_congr_ae hintegrand, h]
  have hquot : ((2 * a + 1 : ℝ) + 1) / 2 = (a + 1 : ℕ) := by
    push_cast
    ring
  rw [hquot]
  rw [show ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial]
  have hneg : -((2 * a + 1 : ℝ) + 1) / 2 = -((a + 1 : ℕ) : ℝ) := by
    linarith [hquot]
  rw [hneg]
  rw [Real.rpow_neg hnR.le, Real.rpow_natCast]
  field_simp [hnR.ne']

/-- Complex-valued version of the radial Gaussian moment. -/
theorem integral_pow_mul_exp_neg_mul_sq_Ioi_complex (n a : ℕ) (hn : 0 < n) :
    ∫ r : ℝ in Ioi 0,
        ((r ^ (2 * a + 1) * Real.exp (-(n : ℝ) * r ^ 2) : ℝ) : ℂ) =
      (a.factorial : ℂ) / (2 * (n : ℂ) ^ (a + 1)) := by
  rw [integral_complex_ofReal]
  rw [integral_pow_mul_exp_neg_mul_sq_Ioi n a hn]
  push_cast
  rfl

end

end GinibrePoincare
