/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialVandermondeCentered.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialVandermondeGauge

/-!
# General potential Vandermonde centered

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialVandermondeCentered_norm_sq`, `potentialSmoothCompact_memLp`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
namespace GinibrePoincare
noncomputable section

theorem potentialCentered_memLp (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V)) :
    MemLp (fun z => ((f z - ∫ w, f w ∂potentialMeasure n V : ℝ) : ℂ)) 2
      (potentialMeasure n V) := by
  let := potentialMeasure_isProbabilityMeasure n hn hV hfin
  exact (hf.sub (memLp_const _)).ofReal

/-- The centred function `f - ∫ f ∂(potentialMeasure n V)`, viewed as a complex element of
`L²(potentialMeasure n V)`. -/
def potentialCenteredL2 (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V)) :
    Lp ℂ 2 (potentialMeasure n V) :=
  (potentialCentered_memLp n hn hV hfin f hf).toLp _

theorem potentialCenteredL2_coeFn (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V)) :
    (potentialCenteredL2 n hn hV hfin f hf : Configuration n → ℂ) =ᵐ[potentialMeasure n V]
      fun z => ((f z - ∫ w, f w ∂potentialMeasure n V : ℝ) : ℂ) :=
  (potentialCentered_memLp n hn hV hfin f hf).coeFn_toLp

theorem potentialCenteredL2_norm_sq (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V)) :
    ‖potentialCenteredL2 n hn hV hfin f hf‖ ^ 2 = potentialVariance n V f := by
  have he : inner ℂ (potentialCenteredL2 n hn hV hfin f hf)
      (potentialCenteredL2 n hn hV hfin f hf) =
      ∫ z, inner ℂ ((potentialCenteredL2 n hn hV hfin f hf) z)
        ((potentialCenteredL2 n hn hV hfin f hf) z) ∂potentialMeasure n V :=
    L2.inner_def _ _
  rw [inner_self_eq_norm_sq_to_K] at he
  have hc := potentialCenteredL2_coeFn n hn hV hfin f hf
  rw [integral_congr_ae (by
    filter_upwards [hc] with z hz
    rw [hz])] at he
  have hi (r : ℝ) : inner ℂ (r : ℂ) (r : ℂ) = (r ^ 2 : ℝ) := by
    simp only [RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, pow_two]
  simp_rw [hi] at he
  rw [integral_complex_ofReal] at he
  apply Complex.ofReal_injective
  convert he using 1 <;> simp [Complex.ofReal_pow, potentialVariance]

theorem potentialVandermondeCentered_norm_sq (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V)) :
    ‖potentialVandermondeL2 n hn hV hfin (potentialCenteredL2 n hn hV hfin f hf)‖ ^ 2 =
      potentialVariance n V f := by
  rw [(potentialVandermondeL2 n hn hV hfin).norm_map]
  exact potentialCenteredL2_norm_sq n hn hV hfin f hf

theorem potentialSmoothCompact_memLp (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    MemLp f 2 (potentialMeasure n V) := by
  let := potentialMeasure_isProbabilityMeasure n hn hV hfin
  exact hf.memLp_of_hasCompactSupport hc

end
end GinibrePoincare
