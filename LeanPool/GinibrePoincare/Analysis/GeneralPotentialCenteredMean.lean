/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialCenteredMean.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialProjectionGeometry

/-!
# General potential centered mean

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialCenteredL2_orthogonal_constant`.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem potentialCenteredL2_integral_zero (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V)) :
    (∫ z, potentialCenteredL2 n hn hV hfin f hf z ∂potentialMeasure n V) = 0 := by
  let := potentialMeasure_isProbabilityMeasure n hn hV hfin
  rw [integral_congr_ae (potentialCenteredL2_coeFn n hn hV hfin f hf),
    integral_complex_ofReal]
  have hfi : Integrable f (potentialMeasure n V) := hf.integrable (by norm_num)
  rw [integral_sub hfi (integrable_const _), integral_const]
  simp

/-- The constant function `c` as an element of `L²` of the probability measure
`potentialMeasure n V`. -/
def potentialConstantL2 (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤) (c : ℂ) :
    Lp ℂ 2 (potentialMeasure n V) := by
  letI := potentialMeasure_isProbabilityMeasure n hn hV hfin
  exact (memLp_const c).toLp (fun _ => c)

theorem potentialConstantL2_coeFn (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤) (c : ℂ) :
    (potentialConstantL2 n hn hV hfin c : Configuration n → ℂ) =ᵐ[potentialMeasure n V]
      fun _ => c := by
  let := potentialMeasure_isProbabilityMeasure n hn hV hfin
  exact (memLp_const c).coeFn_toLp

theorem potentialCenteredL2_orthogonal_constant (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V)) (c : ℂ) :
    inner ℂ (potentialConstantL2 n hn hV hfin c) (potentialCenteredL2 n hn hV hfin f hf) = 0 := by
  rw [L2.inner_def]
  rw [integral_congr_ae (by
    filter_upwards [potentialConstantL2_coeFn n hn hV hfin c] with z hz
    rw [hz])]
  simp only [RCLike.inner_apply]
  rw [integral_mul_const, potentialCenteredL2_integral_zero n hn hV hfin f hf, zero_mul]

end
end GinibrePoincare
