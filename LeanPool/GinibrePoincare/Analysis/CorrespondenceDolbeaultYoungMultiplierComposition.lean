/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDolbeaultYoungMultiplierComposition.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungMultiplier

/-!
# Correspondence Dolbeault Young multiplier composition

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `dolbeaultResidualOperator_norm`, `dolbeaultFiniteOperators_tendsto`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- The derivative-free residual operator in coordinate Dolbeault homotopy. -/
def dolbeaultResidualOperator {n : ℕ} (j : Fin n) (R : ℝ)
    (b : Configuration n → ℂ) (hb : AEStronglyMeasurable b volume) (C : ℝ)
    (hC : ∀ᵐ z : Configuration n ∂volume, ‖b z‖ ≤ C) :
    dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n :=
  (dolbeaultCauchyGreenL2 j R).comp (dolbeaultBoundedMultiplier b hb C hC)

theorem dolbeaultResidualOperator_norm {n : ℕ} (j : Fin n) (R : ℝ)
    (b : Configuration n → ℂ) (hb : AEStronglyMeasurable b volume) (C : ℝ)
    (hC : ∀ᵐ z : Configuration n ∂volume, ‖b z‖ ≤ C) (u : dolbeaultOrdinaryL2 n) :
    ‖dolbeaultResidualOperator j R b hb C hC u‖ ≤
      ((∫ y : ℂ, ‖dolbeaultTruncatedCauchyGreen R y‖)*C)*‖u‖ := by
  apply (dolbeaultCauchyGreenL2_norm j R (dolbeaultBoundedMultiplier b hb C hC u)).trans
  have h := mul_le_mul_of_nonneg_left (dolbeaultBoundedMultiplier_norm b hb C hC u)
    (integral_nonneg (μ := volume) (fun y => norm_nonneg (dolbeaultTruncatedCauchyGreen R y)))
  change (∫ y : ℂ, ‖dolbeaultTruncatedCauchyGreen R y‖)*
    ‖dolbeaultBoundedMultiplierValue b hb C hC u‖ ≤ _
  simpa only [mul_assoc] using h

/-- A finite sequence of genuine bounded homotopy/residual maps. -/
def dolbeaultFiniteOperators {n : ℕ}
    (Ts : List (dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n)) :
    dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n :=
  Ts.foldr (fun T S => T.comp S) (ContinuousLinearMap.id ℂ _)

/-- Ordinary strong L² approximation passes through every finite coordinate iteration. -/
theorem dolbeaultFiniteOperators_tendsto {n : ℕ} {ι : Type*} {l : Filter ι}
    (Ts : List (dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n))
    (u : ι → dolbeaultOrdinaryL2 n) (v : dolbeaultOrdinaryL2 n)
    (hu : Tendsto u l (𝓝 v)) :
    Tendsto (fun i => dolbeaultFiniteOperators Ts (u i)) l
      (𝓝 (dolbeaultFiniteOperators Ts v)) :=
  (dolbeaultFiniteOperators Ts).continuous.continuousAt.tendsto.comp hu

end
end GinibrePoincare
