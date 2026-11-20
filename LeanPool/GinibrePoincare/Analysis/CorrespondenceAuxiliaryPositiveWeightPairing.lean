/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryPositiveWeightPairing.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryPositiveWeightLocal

/-!
# Correspondence auxiliary positive weight pairing

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `positiveWeightCompactPairing_eq_integral`.
-/

@[expose] public section
open MeasureTheory
open scoped ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- Actual ordinary-volume compact test pairing as a continuous functional
on arbitrary positive-local-weight L². -/
def positiveWeightCompactPairing {n : ℕ} (w : Configuration n → ℝ)
    (hw : ∀ K : Set (Configuration n), IsCompact K →
      ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, c ≤ w z)
    (φ : Configuration n → ℂ) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Lp ℂ 2 (volume.withDensity (fun z => ENNReal.ofReal (w z))) →L[ℝ] ℂ := by
  let c := Classical.choose (hw (tsupport φ) hc)
  have hcw := Classical.choose_spec (hw (tsupport φ) hc)
  let R := positiveWeightLocalRestriction volume w (isClosed_tsupport φ).measurableSet hcw.1 hcw.2
  let hm := ((Complex.continuous_conj.comp hφ).memLp_of_hasCompactSupport (p := 2) (μ := volume)
    (hc.comp_left (map_zero _))).restrict (tsupport φ)
  let g := hm.toLp (conj ∘ φ)
  exact ((innerSL ℂ g).restrictScalars ℝ).comp R

theorem positiveWeightCompactPairing_eq_integral {n : ℕ} (w : Configuration n → ℝ)
    (hw : ∀ K : Set (Configuration n), IsCompact K →
      ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, c ≤ w z)
    (φ : Configuration n → ℂ) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (u : Lp ℂ 2 (volume.withDensity (fun z => ENNReal.ofReal (w z)))) :
    positiveWeightCompactPairing w hw φ hφ hc u = ∫ z, φ z * u z := by
  let c := Classical.choose (hw (tsupport φ) hc)
  have hcw := Classical.choose_spec (hw (tsupport φ) hc)
  let R := positiveWeightLocalRestriction volume w (isClosed_tsupport φ).measurableSet hcw.1 hcw.2
  let hm := ((Complex.continuous_conj.comp hφ).memLp_of_hasCompactSupport (p := 2) (μ := volume)
    (hc.comp_left (map_zero _))).restrict (tsupport φ)
  let g := hm.toLp (conj ∘ φ)
  change inner ℂ g (R u) = _
  rw [L2.inner_def]
  have he : (∫ z in tsupport φ, inner ℂ (g z) ((R u) z)) =
      ∫ z in tsupport φ, φ z * u z := by
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp, positiveWeightLocalRestriction_coe volume w
      (isClosed_tsupport φ).measurableSet hcw.1 hcw.2 u] with z hg hr
    rw [hg, hr]
    simp [RCLike.inner_apply, mul_comm]
  rw [he]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]

end
end GinibrePoincare
