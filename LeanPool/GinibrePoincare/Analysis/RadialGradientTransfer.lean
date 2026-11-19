/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/RadialGradientTransfer.lean.
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

public import LeanPool.GinibrePoincare.Analysis.KostlanEntropyTransfer
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Radial gradient transfer

Part of the polynomial, radial and equilibrium sectors development of the
Ginibre Poincaré formalization.

Main results: `smoothGinibreEnergy_radial_eq_gamma`.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

/-- The vector of scaled squared radii `n |z i|²` of the coordinates. -/
def scaledSquaredRadii (n : ℕ) (z : Configuration n) : Fin n → ℝ :=
  fun i => kostlanSquaredRadius n (z i)

/-- The partial derivative of `F` at `r` in the `i`-th coordinate. -/
def radiusPartial {n : ℕ} (F : (Fin n → ℝ) → ℝ) (r : Fin n → ℝ) (i : Fin n) : ℝ :=
  fderiv ℝ F r (Pi.single i 1)

/-- Gamma-coordinate energy density in the paper's exact normalization. -/
def gammaRadialEnergyDensity {n : ℕ} (F : (Fin n → ℝ) → ℝ) (r : Fin n → ℝ) : ℝ :=
  4 * ∑ i, r i * radiusPartial F r i ^ 2

/-- The Fréchet derivative at `z` of `scaledSquaredRadii n`: its `i`-th component is
`2n (Re (z i) · Re + Im (z i) · Im)` applied to the `i`-th coordinate. -/
def squaredRadiiDerivative (n : ℕ) (z : Configuration n) :
    Configuration n →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i =>
    (2 * (n : ℝ) * (z i).re) • (Complex.reCLM.comp (ContinuousLinearMap.proj i)) +
    (2 * (n : ℝ) * (z i).im) • (Complex.imCLM.comp (ContinuousLinearMap.proj i)))

theorem hasFDerivAt_scaledSquaredRadii (n : ℕ) (z : Configuration n) :
    HasFDerivAt (scaledSquaredRadii n) (squaredRadiiDerivative n z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  have hr := Complex.reCLM.hasFDerivAt.comp z (ContinuousLinearMap.proj i).hasFDerivAt
  have hi := Complex.imCLM.hasFDerivAt.comp z (ContinuousLinearMap.proj i).hasFDerivAt
  have h := ((hr.mul hr).add (hi.mul hi)).const_mul (n : ℝ)
  convert! h using 1
  ext v
  simp
  ring

private theorem squaredRadiiDerivative_real (n : ℕ) (z : Configuration n) (i : Fin n) :
    squaredRadiiDerivative n z (realCoordinateDirection i) =
      (2 * (n : ℝ) * (z i).re) • (Pi.single i 1 : Fin n → ℝ) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [squaredRadiiDerivative, realCoordinateDirection, coordinateDirection]
  · simp [squaredRadiiDerivative, realCoordinateDirection, coordinateDirection, h]

private theorem squaredRadiiDerivative_imag (n : ℕ) (z : Configuration n) (i : Fin n) :
    squaredRadiiDerivative n z (imaginaryCoordinateDirection i) =
      (2 * (n : ℝ) * (z i).im) • (Pi.single i 1 : Fin n → ℝ) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [squaredRadiiDerivative, imaginaryCoordinateDirection, coordinateDirection]
  · simp [squaredRadiiDerivative, imaginaryCoordinateDirection, coordinateDirection, h]

/-- The squared-radius chain rule holds even when a coordinate vanishes. -/
theorem realGradientNormSq_radial (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (hF : Differentiable ℝ F) (z : Configuration n) :
    realGradientNormSq (fun z => F (scaledSquaredRadii n z)) z =
      (n : ℝ) * gammaRadialEnergyDensity F (scaledSquaredRadii n z) := by
  have hd := ((hF _).hasFDerivAt.comp z (hasFDerivAt_scaledSquaredRadii n z)).fderiv
  unfold realGradientNormSq
  change fderiv ℝ (fun z => F (scaledSquaredRadii n z)) z = _ at hd
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply, squaredRadiiDerivative_real,
    squaredRadiiDerivative_imag, map_smul, smul_eq_mul]
  unfold gammaRadialEnergyDensity radiusPartial scaledSquaredRadii kostlanSquaredRadius
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.normSq_apply]
  ring

private def radiusPermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (σ i))

/-- Differentiation of permutation symmetry permutes the partial derivatives. -/
theorem radiusPartial_permutation {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (hF : Differentiable ℝ F) (hS : IsSymmetricRadiusTest n F)
    (σ : Equiv.Perm (Fin n)) (r : Fin n → ℝ) (i : Fin n) :
    radiusPartial F (r ∘ σ) i = radiusPartial F r (σ i) := by
  have heq : F ∘ radiusPermutation σ = F := by
    funext r
    exact hS σ r
  have hd := ((hF _).hasFDerivAt.comp r (radiusPermutation σ).hasFDerivAt).fderiv
  rw [heq] at hd
  have hv := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single (σ i) 1)) hd
  have he : radiusPermutation σ (Pi.single (σ i) 1) = (Pi.single i 1 : Fin n → ℝ) := by
    ext j
    simp [radiusPermutation, Pi.single_apply, σ.injective.eq_iff]
  simp only [ContinuousLinearMap.comp_apply] at hv
  rw [he] at hv
  exact hv.symm

/-- The weighted Gamma energy density retains permutation symmetry. -/
theorem gammaRadialEnergyDensity_symmetric {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (hF : Differentiable ℝ F) (hS : IsSymmetricRadiusTest n F) :
    IsSymmetricRadiusTest n (gammaRadialEnergyDensity F) := by
  intro σ r
  unfold gammaRadialEnergyDensity
  simp only [radiusPartial_permutation F hF hS σ r, Function.comp_apply]
  rw [Equiv.sum_comp σ (fun i => r i * radiusPartial F r i ^ 2)]

/-- Smooth compact profiles have continuous compactly supported energy densities. -/
theorem gammaRadialEnergyDensity_regular {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    Continuous (gammaRadialEnergyDensity F) ∧ HasCompactSupport (gammaRadialEnergyDensity F) := by
  constructor
  · unfold gammaRadialEnergyDensity radiusPartial
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro i hi
    exact (continuous_apply i).mul
      (((hF.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2)
  · apply (hc.fderiv (𝕜 := ℝ)).mono
    intro r hr hz
    apply hr
    simp [gammaRadialEnergyDensity, radiusPartial, hz]

/-- The actual Ginibre Dirichlet energy is exactly the weighted Gamma energy. -/
theorem smoothGinibreEnergy_radial_eq_gamma (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hS : IsSymmetricRadiusTest n F) :
    smoothGinibreEnergy n (fun z => F (scaledSquaredRadii n z)) =
      ∫ r, gammaRadialEnergyDensity F r ∂kostlanGammaProduct n := by
  have hd : Differentiable ℝ F := hF.differentiable (by simp)
  obtain ⟨hcont, hcomp⟩ := gammaRadialEnergyDensity_regular F hF hc
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuous hcont
  have ht := ginibre_radial_expectation_eq_gamma_product n hn
    (gammaRadialEnergyDensity F) hcont (gammaRadialEnergyDensity_symmetric F hd hS) C hC
  unfold smoothGinibreEnergy
  simp_rw [realGradientNormSq_radial n F hd]
  rw [integral_const_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← mul_assoc, one_div, inv_mul_cancel₀ hnR, one_mul]
  exact ht

end
end GinibrePoincare
