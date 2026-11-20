/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDolbeaultYoungPairing.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDolbeaultYoung
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Correspondence Dolbeault Young pairing

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `dolbeaultCoordinateConvolution_compact_test`.
-/

@[expose] public section
open MeasureTheory
open scoped ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- The bounded functional `u ↦ ∫ z, θ z * u z` on ordinary `L²` defined by a continuous
compactly supported `θ`. -/
def dolbeaultCompactPairing {n : ℕ} (θ : Configuration n → ℂ)
    (hθ : Continuous θ) (hc : HasCompactSupport θ) : dolbeaultOrdinaryL2 n →L[ℂ] ℂ :=
  innerSL ℂ ((Complex.continuous_conj.comp hθ).memLp_of_hasCompactSupport
    (p := 2) (μ := volume) (hc.comp_left (map_zero _))).toLp

theorem dolbeaultCompactPairing_eq_integral {n : ℕ} (θ : Configuration n → ℂ)
    (hθ : Continuous θ) (hc : HasCompactSupport θ) (u : dolbeaultOrdinaryL2 n) :
    dolbeaultCompactPairing θ hθ hc u = ∫ z : Configuration n, θ z*u z := by
  rw [dolbeaultCompactPairing]
  change inner ℂ _ u = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [((Complex.continuous_conj.comp hθ).memLp_of_hasCompactSupport
    (p := 2) (μ := volume) (hc.comp_left (map_zero _))).coeFn_toLp] with z hz
  rw [hz]
  simp [RCLike.inner_apply, mul_comm]

theorem dolbeaultTranslateL2_ae {n : ℕ} (j : Fin n) (y : ℂ) (u : dolbeaultOrdinaryL2 n) :
    (dolbeaultTranslateL2 j y u : Configuration n → ℂ) =ᵐ[volume]
      fun z => u (z-Pi.single j y) :=
  Lp.coeFn_compMeasurePreserving u (dolbeaultCoordinateTranslation_preserving j y)

/-- Literal ordinary-volume compact-test pairing of coordinate convolution.
This needs only L¹ for the kernel and L² for the input. -/
theorem dolbeaultCoordinateConvolution_compact_test {n : ℕ} (j : Fin n)
    (k : ℂ → ℂ) (hk : Integrable k volume) (u : dolbeaultOrdinaryL2 n)
    (θ : Configuration n → ℂ) (hθ : Continuous θ) (hc : HasCompactSupport θ) :
    (∫ z : Configuration n, θ z*(dolbeaultCoordinateConvolution j k u) z) =
      ∫ y : ℂ, k y*(∫ z : Configuration n, θ z*u (z-Pi.single j y)) := by
  rw [← dolbeaultCompactPairing_eq_integral θ hθ hc,
    dolbeaultCoordinateConvolution_pairing j k hk u (dolbeaultCompactPairing θ hθ hc)]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    dsimp only
    rw [dolbeaultCompactPairing_eq_integral θ hθ hc]
    congr 1
    apply integral_congr_ae
    filter_upwards [dolbeaultTranslateL2_ae j y u] with z hz
    rw [hz])

end
end GinibrePoincare
