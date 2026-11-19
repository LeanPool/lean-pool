/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/RadialMagnitudeProfile.lean.
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

public import LeanPool.GinibrePoincare.Analysis.RadialSobolevClosure
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Radial magnitude profile

Part of the polynomial, radial and equilibrium sectors development of the
Ginibre Poincaré formalization.

Main results: `contDiff_magnitudeProfile`, `compactSupport_magnitudeProfile`,
`magnitudeProfile_symmetric`, `ginibre_magnitude_entropy_eq_gamma`.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

/-- The real-coordinate section of a radial observable. -/
def magnitudeProfile {n : ℕ} (f : Configuration n → ℝ) (r : Fin n → ℝ) : ℝ :=
  f (fun i => (r i : ℂ))

/-- The vector `(‖z i‖)ᵢ` of moduli of the coordinates. -/
def magnitudeVector {n : ℕ} (z : Configuration n) : Fin n → ℝ := fun i => ‖z i‖

/-- Every radial function is recovered from its actual real-coordinate section;
no regularity of the existential radial witness is needed. -/
theorem radial_eq_magnitudeProfile {n : ℕ} (f : Configuration n → ℝ)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (z : Configuration n) : f z = magnitudeProfile f (magnitudeVector z) := by
  obtain ⟨F, hF⟩ := hr
  unfold magnitudeProfile magnitudeVector
  rw [hF z, hF]
  congr 1
  funext i
  simp [Complex.normSq_eq_norm_sq]

theorem contDiff_magnitudeProfile {n : ℕ} (f : Configuration n → ℝ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (magnitudeProfile f) := by
  apply hf.comp
  apply contDiff_pi.mpr
  intro i
  exact Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ (fun _ => ℝ) i)

theorem compactSupport_magnitudeProfile {n : ℕ} (f : Configuration n → ℝ)
    (hc : HasCompactSupport f) : HasCompactSupport (magnitudeProfile f) := by
  have he : Isometry (fun r : Fin n → ℝ => fun i => (r i : ℂ)) :=
    isometry_iff_dist_eq.mpr (by
      intro r s
      simp only [dist_pi_def, Complex.isometry_ofReal.nndist_eq])
  exact hc.comp_isClosedEmbedding he.isClosedEmbedding

theorem magnitudeProfile_symmetric {n : ℕ} (f : Configuration n → ℝ)
    (hs : IsSymmetric f) : IsSymmetricRadiusTest n (magnitudeProfile f) := by
  intro σ r
  exact hs σ (fun i => (r i : ℂ))

/-- Passing from scaled squared radii to magnitudes on the entire real domain. -/
def gammaMagnitudes (n : ℕ) (r : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.sqrt (r i / (n : ℝ))

theorem continuous_gammaMagnitudes (n : ℕ) : Continuous (gammaMagnitudes n) := by
  unfold gammaMagnitudes
  fun_prop

theorem gammaMagnitudes_scaledSquaredRadii (n : ℕ) (hn : 0 < n) (z : Configuration n) :
    gammaMagnitudes n (scaledSquaredRadii n z) = magnitudeVector z := by
  ext i
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [gammaMagnitudes, scaledSquaredRadii, kostlanSquaredRadius, hnR,
    Complex.normSq_eq_norm_sq, magnitudeVector]

/-- The Kostlan identity also applies directly to bounded continuous magnitude profiles. -/
theorem ginibre_magnitude_expectation_eq_gamma (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hf : Continuous F) (hs : IsSymmetricRadiusTest n F)
    (C : ℝ) (hC : ∀ r, ‖F r‖ ≤ C) :
    (∫ z, F (magnitudeVector z) ∂ginibreMeasure n) =
      ∫ r, F (gammaMagnitudes n r) ∂kostlanGammaProduct n := by
  have ht := ginibre_radial_expectation_eq_gamma_product n hn
    (F ∘ gammaMagnitudes n) (hf.comp (continuous_gammaMagnitudes n))
    (by intro σ r; exact hs σ (gammaMagnitudes n r)) C (fun r => hC _)
  change (∫ z, F (gammaMagnitudes n (scaledSquaredRadii n z)) ∂ginibreMeasure n) = _ at ht
  simpa only [gammaMagnitudes_scaledSquaredRadii n hn, Function.comp_apply, kostlanGammaProduct]
      using ht

/-- Transfer of entropy for bounded continuous magnitude profiles. -/
theorem ginibre_magnitude_entropy_eq_gamma (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hf : Continuous F) (hs : IsSymmetricRadiusTest n F)
    (hc : HasCompactSupport F) :
    squareEntropy (ginibreMeasure n) (fun z => F (magnitudeVector z)) =
      squareEntropy (kostlanGammaProduct n) (fun r => F (gammaMagnitudes n r)) := by
  apply squareEntropy_eq_of_moments
  · have hsupp : HasCompactSupport (fun r => F r ^ 2) := by
      apply hc.mono
      intro r hr hz
      exact hr (by simp [hz])
    obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous (hf.pow 2)
    exact ginibre_magnitude_expectation_eq_gamma n hn (fun r => F r ^ 2)
      (hf.pow 2) (by intro σ r; dsimp; rw [hs σ r]) C hC
  · obtain ⟨C, hC⟩ := (compactSupport_square_mul_log hc).exists_bound_of_continuous
      (continuous_square_mul_log hf)
    exact ginibre_magnitude_expectation_eq_gamma n hn
      (fun r => F r ^ 2 * Real.log (F r ^ 2)) (continuous_square_mul_log hf)
      (by intro σ r; dsimp; rw [hs σ r]) C hC

end
end GinibrePoincare
