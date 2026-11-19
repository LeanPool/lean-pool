/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/LaguerreGammaNondegeneracy.lean.
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

public import LeanPool.GinibrePoincare.Analysis.LaguerreGammaOrthogonality
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Laguerre gamma nondegeneracy

Part of the polynomial, radial and equilibrium sectors development of the
Ginibre Poincaré formalization.

Main results: `integral_polynomial_sq_pos`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
namespace GinibrePoincare.Laguerre
noncomputable section

/-- A classical Laguerre polynomial has a strictly positive squared Gamma norm. -/
theorem integral_polynomial_sq_pos (k m : ℕ) (hk : 0 < k) :
    0 < ∫ r : ℝ, (polynomial k m).eval r * (polynomial k m).eval r
      ∂gammaMeasure (k : ℝ) 1 := by
  have hi := integrable_polynomial_mul k m m hk
  have hnonneg : ∀ r : ℝ, 0 ≤ (polynomial k m).eval r * (polynomial k m).eval r :=
    fun r => mul_self_nonneg _
  have hge := integral_nonneg_of_ae (μ := gammaMeasure (k : ℝ) 1) (Filter.Eventually.of_forall
      hnonneg)
  apply lt_of_le_of_ne hge
  intro he
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg hi).mp he.symm
  change (∀ᵐ r ∂volume.withDensity (gammaPDF (k : ℝ) 1),
    (polynomial k m).eval r * (polynomial k m).eval r = 0) at hae
  rw [ae_withDensity_iff (f := gammaPDF (k : ℝ) 1)
    (measurable_gammaPDFReal (k : ℝ) 1).ennreal_ofReal] at hae
  have hv : (fun r : ℝ => (polynomial k m).eval r * (polynomial k m).eval r) =ᵐ[
      volume.restrict (Ioi 0)] (fun _ => 0) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hae] with r hr hpos
    apply hr
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (gammaPDFReal_pos (by exact_mod_cast hk)
      (by norm_num) hpos))
  have hc : Continuous (fun r : ℝ => (polynomial k m).eval r * (polynomial k m).eval r) := by
    fun_prop
  have hon := Measure.eqOn_open_of_ae_eq hv isOpen_Ioi hc.continuousOn continuous_const.continuousOn
  have hcl := hon.of_subset_closure hc.continuousOn continuous_const.continuousOn
    (show Ioi (0 : ℝ) ⊆ Ici 0 from Ioi_subset_Ici_self)
    (show Ici (0 : ℝ) ⊆ closure (Ioi 0) by rw [closure_Ioi])
  have hzero := hcl (show (0 : ℝ) ∈ Ici 0 by simp)
  simp only [eval_zero] at hzero
  have hp : (0 : ℝ) < Nat.choose (m+k-1) m := by
    exact_mod_cast (Nat.choose_pos (show m ≤ m+k-1 by omega))
  exact (mul_pos hp hp).ne' hzero

end
end GinibrePoincare.Laguerre
