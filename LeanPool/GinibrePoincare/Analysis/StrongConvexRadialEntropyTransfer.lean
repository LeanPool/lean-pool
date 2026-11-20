/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/StrongConvexRadialEntropyTransfer.lean.
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

public import LeanPool.GinibrePoincare.Analysis.StrongConvexRadialProductLSI
public import LeanPool.GinibrePoincare.Analysis.RadialMagnitudeProfile

/-!
# Strong convex radial entropy transfer

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potential_radial_entropy_eq_squaredRadiusProduct_bounded`,
`potential_magnitude_entropy_eq_radiusProduct`.
-/

@[expose] public section

open MeasureTheory Set
namespace GinibrePoincare
noncomputable section

/-- Boundedness, rather than support, suffices for the literal Kostlan entropy identity. -/
theorem potential_radial_entropy_eq_squaredRadiusProduct_bounded
    (n : ℕ) (hn : 0 < n) {V : Potential} (hVc : Continuous V)
    (hVr : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F)
    (hS : IsSymmetricRadiusTest n F) (C : ℝ) (hC : ∀ r, |F r| ≤ C) :
    squareEntropy (potentialMeasure n V) (fun z => F (fun i => Complex.normSq (z i))) =
      squareEntropy (potentialSquaredRadiusProduct n V) F := by
  have hC0 : 0 ≤ C := (abs_nonneg (F 0)).trans (hC 0)
  apply squareEntropy_eq_of_moments
  · apply potential_radial_expectation_eq_squaredRadiusProduct n hn hVc hVr hfin
      (fun r => F r ^ 2) (hF.pow 2)
      (by intro σ r; exact congrArg (fun x : ℝ => x ^ 2) (hS σ r)) (C ^ 2)
    intro r
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC r) _
  · obtain ⟨D, hD⟩ := (isCompact_Icc : IsCompact (Icc (-C) C)).exists_bound_of_continuousOn
      (continuous_square_mul_log (continuous_id : Continuous (fun x : ℝ => x))).continuousOn
    apply potential_radial_expectation_eq_squaredRadiusProduct n hn hVc hVr hfin
      (fun r => F r ^ 2 * Real.log (F r ^ 2)) (continuous_square_mul_log hF)
      (by intro σ r; exact congrArg (fun x : ℝ => x ^ 2 * Real.log (x ^ 2)) (hS σ r)) D
    intro r
    exact hD (F r) (abs_le.mp (hC r))

/-- The genuine positive-radius product is the coordinatewise square-root pushforward. -/
theorem potentialSquaredRadiusProduct_sqrt_map (n : ℕ) (hn : 0 < n)
    {V : Potential} (hVc : Continuous V) (hVr : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) :
    (potentialSquaredRadiusProduct n V).map (fun r i => Real.sqrt (r i)) =
      potentialRadiusProduct n V := by
  let (i : Fin n) := potentialSquaredRadiusLaw_isProbabilityMeasure n hn hVc hVr hfin i
  unfold potentialSquaredRadiusProduct potentialRadiusProduct
  exact Measure.pi_map_pi (fun i => Real.continuous_sqrt.measurable.aemeasurable)

/-- Actual bounded symmetric magnitude expectations under the interacting law. -/
theorem potential_magnitude_expectation_eq_radiusProduct
    (n : ℕ) (hn : 0 < n) {V : Potential} (hVc : Continuous V)
    (hVr : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F)
    (hS : IsSymmetricRadiusTest n F) (C : ℝ) (hC : ∀ r, ‖F r‖ ≤ C) :
    (∫ z, F (magnitudeVector z) ∂potentialMeasure n V) =
      ∫ r, F r ∂potentialRadiusProduct n V := by
  have hsqrt : Continuous (fun r : Fin n → ℝ => fun i => Real.sqrt (r i)) := by fun_prop
  have ht := potential_radial_expectation_eq_squaredRadiusProduct n hn hVc hVr hfin
    (fun r => F (fun i => Real.sqrt (r i))) (hF.comp hsqrt)
    (by intro σ r; exact hS σ (fun i => Real.sqrt (r i))) C (fun r => hC _)
  have he : (fun z : Configuration n => F (fun i => Real.sqrt (Complex.normSq (z i)))) =
      (fun z => F (magnitudeVector z)) := by
    funext z
    congr 1
    funext i
    simp only [magnitudeVector, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [he] at ht
  rw [← potentialSquaredRadiusProduct_sqrt_map n hn hVc hVr hfin]
  rw [integral_map hsqrt.measurable.aemeasurable hF.aestronglyMeasurable]
  exact ht

/-- Entropy of a bounded symmetric magnitude profile under the genuine interacting law. -/
theorem potential_magnitude_entropy_eq_radiusProduct
    (n : ℕ) (hn : 0 < n) {V : Potential} (hVc : Continuous V)
    (hVr : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F)
    (hS : IsSymmetricRadiusTest n F) (C : ℝ) (hC : ∀ r, |F r| ≤ C) :
    squareEntropy (potentialMeasure n V) (fun z => F (magnitudeVector z)) =
      squareEntropy (potentialRadiusProduct n V) F := by
  apply squareEntropy_eq_of_moments
  · apply potential_magnitude_expectation_eq_radiusProduct n hn hVc hVr hfin
      (fun r => F r ^ 2) (hF.pow 2)
      (by intro σ r; exact congrArg (fun x : ℝ => x ^ 2) (hS σ r)) (C ^ 2)
    intro r
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC r) _
  · obtain ⟨D, hD⟩ := (isCompact_Icc : IsCompact (Icc (-C) C)).exists_bound_of_continuousOn
      (continuous_square_mul_log (continuous_id : Continuous (fun x : ℝ => x))).continuousOn
    apply potential_magnitude_expectation_eq_radiusProduct n hn hVc hVr hfin
      (fun r => F r ^ 2 * Real.log (F r ^ 2)) (continuous_square_mul_log hF)
      (by intro σ r; exact congrArg (fun x : ℝ => x ^ 2 * Real.log (x ^ 2)) (hS σ r)) D
    intro r
    exact hD (F r) (abs_le.mp (hC r))

end
end GinibrePoincare
