/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Endgame/FullTheoremOneTen.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianDbarSmoothTests
public import LeanPool.GinibrePoincare.Endgame.FullTheoremOneNine
public import LeanPool.GinibrePoincare.Analysis.HermiteSecondDbarWeakClosure
public import LeanPool.GinibrePoincare.Analysis.HermiteSecondDbarInfiniteEnergy
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorCenterEigenvectors
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupConstants
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupDeficitConsequences
public import LeanPool.GinibrePoincare.Analysis.HolomorphicQuotientPhaseProjection

/-! # Differential deficit vector and its genuine weak derivatives

The vector is the inverse square root of the antiholomorphic number operator
applied to the positive-mode projection of the actual centered Vandermonde
transform. Its weak derivatives follow from the concrete Ginibre weak gradient.

## Proof organization

Centering preserves the ordinary weak gradient. The transformed gradient gives
the Hermite coefficient lowering identities, from which inverse-square-root
synthesis constructs both weak derivatives. Parseval identifies their summed
second-derivative energy with `n` times the Hermite tail. Substituting this
identity in Theorem 1.9 yields the coefficients `4 / n` and `8 / n` below.

`fullTheoremOneTen_named` exposes the conclusions as named fields. The
Schwartz version at the end uses the proved equivalence between the compact
weak-test definition and ordinary distributional Wirtinger derivatives.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- The inverse square root `N⁻¹ᐟ²` of the number operator applied to the centered
Vandermonde transform of `u` with its antiholomorphic-degree-zero Hermite mode removed. -/
def ginibreDifferentialDeficitVector (n : ℕ) (hn : 0 < n) (u : GinibreFullValueL2 n) :
    Lp ℂ 2 (complexGaussianMeasure n) :=
  gaussianHermiteInverseSquareRoot hn
    (ginibreFullCenteredTransform n hn u -
      gaussianHermiteMode hn 0 (ginibreFullCenteredTransform n hn u))

/-- The first inverse square root synthesis of the transformed weak `∂̄_j` derivative of the
gradient field `g`. -/
def ginibreDifferentialFirstDerivative (n : ℕ) (hn : 0 < n)
    (g : GinibreFullGradientL2 n) (j : Fin n) : Lp ℂ 2 (complexGaussianMeasure n) :=
  gaussianInverseSquareRootFirstSynthesis hn (ginibreFullTransformedDbar n hn j g) j

/-- The second inverse square root synthesis, in coordinates `j` and `k`, of the transformed
weak `∂̄_j` derivative of the gradient field `g`. -/
def ginibreDifferentialSecondDerivative (n : ℕ) (hn : 0 < n)
    (g : GinibreFullGradientL2 n) (j k : Fin n) : Lp ℂ 2 (complexGaussianMeasure n) :=
  gaussianInverseSquareRootSecondSynthesis hn (ginibreFullTransformedDbar n hn j g) j k

/-- Actual weak first and second Wirtinger derivatives for every symmetric
ordinary Ginibre weak pair, without a spectral-domain assumption. -/
theorem ginibreDifferentialDeficit_weak_derivatives {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (hs : IsGinibreSymmetricWeakPair (u, g)) :
    (∀ j, IsGaussianWeakDbar n (ginibreDifferentialDeficitVector n hn u)
      (ginibreDifferentialFirstDerivative n hn g j) j) ∧
    (∀ j k, IsGaussianWeakDbar n (ginibreDifferentialFirstDerivative n hn g j)
      (ginibreDifferentialSecondDerivative n hn g j k) k) := by
  obtain ⟨huc, hsc⟩ := ginibreFullCenter_weak_pair hn u g hu hs
  have hcoeff := ginibreFullTransformedDbar_weak_coefficient hn
    (ginibreFullCenter n hn u) g huc hsc
  have hweak := gaussianInverseSquareRoot_weak_derivatives hn
    (ginibreFullCenteredTransform n hn u) (ginibreFullTransformedDbar n hn · g) hcoeff
  simpa only [ginibreDifferentialDeficitVector,
    gaussianHermiteInverseSquareRoot_positiveProjection,
    ginibreDifferentialFirstDerivative, ginibreDifferentialSecondDerivative] using hweak

/-- The second-order energy `∑ j, ∑ k, ‖ginibreDifferentialSecondDerivative n hn g j k‖ ^ 2`. -/
def ginibreDifferentialSecondEnergy (n : ℕ) (hn : 0 < n)
    (g : GinibreFullGradientL2 n) : ℝ :=
  ∑ j : Fin n, ∑ k : Fin n, ‖ginibreDifferentialSecondDerivative n hn g j k‖ ^ 2

theorem gaussianL2_norm_sq_eq_integral_normSq {n : ℕ}
    (q : Lp ℂ 2 (complexGaussianMeasure n)) :
    ‖q‖ ^ 2 = ∫ z, Complex.normSq (q z) ∂complexGaussianMeasure n := by
  have hinner : inner ℂ q q =
      ∫ z, inner ℂ (q z) (q z) ∂complexGaussianMeasure n :=
    MeasureTheory.L2.inner_def q q
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hi : (fun z => inner ℂ (q z) (q z)) =
      fun z => (Complex.normSq (q z) : ℂ) := by
    funext z
    rw [inner_self_eq_norm_sq_to_K]
    calc
      (‖q z‖ : ℂ) ^ 2 = ((‖q z‖ ^ 2 : ℝ) : ℂ) := by norm_cast
      _ = _ := congrArg Complex.ofReal (Complex.sq_norm (q z))
  rw [hi, integral_complex_ofReal] at hinner
  apply Complex.ofReal_injective
  push_cast
  exact hinner

/-- The differential energy is literally the Gaussian integral of the squared
weak second derivatives, summed over all ordered coordinate pairs. -/
theorem ginibreDifferentialSecondEnergy_eq_integral {n : ℕ} (hn : 0 < n)
    (g : GinibreFullGradientL2 n) :
    ginibreDifferentialSecondEnergy n hn g =
      ∑ j : Fin n, ∑ k : Fin n, ∫ z,
        Complex.normSq (ginibreDifferentialSecondDerivative n hn g j k z)
          ∂complexGaussianMeasure n := by
  unfold ginibreDifferentialSecondEnergy
  simp_rw [gaussianL2_norm_sq_eq_integral_normSq]

theorem ginibreDifferentialSecondEnergy_eq_tail {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (hs : IsGinibreSymmetricWeakPair (u, g)) :
    ginibreDifferentialSecondEnergy n hn g =
      n * modeTail (positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u)) := by
  obtain ⟨huc, hsc⟩ := ginibreFullCenter_weak_pair hn u g hu hs
  exact (gaussianInverseSquareRootSecondSynthesis_total_energy_modeTail hn
    (ginibreFullCenteredTransform n hn u) (ginibreFullTransformedDbar n hn · g)
    (ginibreFullTransformedDbar_weak_coefficient hn
      (ginibreFullCenter n hn u) g huc hsc)).2

/-- Theorem 1.10: both differential sum-of-squares deficits, with the actual
inverse-square-root vector and its actual weak second Wirtinger derivatives.
All derivative and spectral facts are derived from full generator membership. -/
theorem fullTheoremOneTen {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph) :
    ∃ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n u.val g ∧
      IsGinibreSymmetricWeakPair (u.val, g) ∧
      (∀ j, IsGaussianWeakDbar n (ginibreDifferentialDeficitVector n hn u.val)
        (ginibreDifferentialFirstDerivative n hn g j) j) ∧
      (∀ j k, IsGaussianWeakDbar n (ginibreDifferentialFirstDerivative n hn g j)
        (ginibreDifferentialSecondDerivative n hn g j k) k) ∧
      ginibreWeakEnergy n g - 2 * ginibreL2Variance n hn u.val =
        2 * ‖ginibreFullHolomorphicRemainder n hn u.val‖ ^ 2 +
          (4 / (n : ℝ)) * ginibreDifferentialSecondEnergy n hn g ∧
      ‖v.val‖ ^ 2 - 2 * ginibreWeakEnergy n g =
        ‖v.val + (2 : ℝ) • ginibreFullCenter n hn u.val‖ ^ 2 +
          4 * ‖ginibreFullHolomorphicRemainder n hn u.val‖ ^ 2 +
          (8 / (n : ℝ)) * ginibreDifferentialSecondEnergy n hn g ∧
      (ginibreWeakEnergy n g = 2 * ginibreL2Variance n hn u.val ↔
        ∃ (a : ℝ) (c : ℂ), (u.val : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
          fun z => a + 2 * (c * coordinateSum z).re) := by
  obtain ⟨g, deficits⟩ := fullTheoremOneNine_named hn u v hgraph
  obtain ⟨hfirstDerivative, hsecondDerivative⟩ :=
    ginibreDifferentialDeficit_weak_derivatives hn u.val g
      deficits.distributional_gradient deficits.symmetric_gradient
  have hsecondEnergy := ginibreDifferentialSecondEnergy_eq_tail hn u.val g
    deficits.distributional_gradient deficits.symmetric_gradient
  have hnNonzero : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hfirstCoefficient : (4 / (n : ℝ)) * ginibreDifferentialSecondEnergy n hn g =
      4 * modeTail (positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u.val)) := by
    rw [hsecondEnergy]
    field_simp
  have hsecondCoefficient : (8 / (n : ℝ)) * ginibreDifferentialSecondEnergy n hn g =
      8 * modeTail (positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u.val)) := by
    rw [hsecondEnergy]
    field_simp
  refine ⟨g, deficits.distributional_gradient, deficits.symmetric_gradient,
    hfirstDerivative, hsecondDerivative, ?_, ?_, deficits.equality_iff_affine⟩
  · rw [hfirstCoefficient]
    exact deficits.poincare_deficit
  · rw [hsecondCoefficient]
    exact deficits.generator_deficit

/-- Named differential conclusions for the same value, generator value, and
ordinary weak gradient. The derivatives refer to the explicit synthesis
functions defined above. -/
structure GinibreDifferentialDeficits {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n) (g : GinibreFullGradientL2 n) : Prop where
  /-- The value has this ordinary distributional gradient. -/
  distributional_gradient : IsGinibreDistributionalGradient n u.val g
  /-- Particle symmetry holds for the value-gradient pair. -/
  symmetric_gradient : IsGinibreSymmetricWeakPair (u.val, g)
  /-- First weak Wirtinger derivatives of the inverse-square-root vector. -/
  first_derivatives : ∀ j,
    IsGaussianWeakDbar n (ginibreDifferentialDeficitVector n hn u.val)
      (ginibreDifferentialFirstDerivative n hn g j) j
  /-- Second weak Wirtinger derivatives, for every ordered coordinate pair. -/
  second_derivatives : ∀ j k,
    IsGaussianWeakDbar n (ginibreDifferentialFirstDerivative n hn g j)
      (ginibreDifferentialSecondDerivative n hn g j k) k
  /-- The Poincaré deficit in terms of the summed second-derivative energy. -/
  poincare_deficit : ginibreWeakEnergy n g - 2 * ginibreL2Variance n hn u.val =
    2 * ‖ginibreFullHolomorphicRemainder n hn u.val‖ ^ 2 +
      (4 / (n : ℝ)) * ginibreDifferentialSecondEnergy n hn g
  /-- The generator deficit using the same second-derivative energy. -/
  generator_deficit : ‖v.val‖ ^ 2 - 2 * ginibreWeakEnergy n g =
    ‖v.val + (2 : ℝ) • ginibreFullCenter n hn u.val‖ ^ 2 +
      4 * ‖ginibreFullHolomorphicRemainder n hn u.val‖ ^ 2 +
      (8 / (n : ℝ)) * ginibreDifferentialSecondEnergy n hn g
  /-- The exhaustive almost-everywhere affine equality classification. -/
  equality_iff_affine : ginibreWeakEnergy n g = 2 * ginibreL2Variance n hn u.val ↔
    ∃ (a : ℝ) (c : ℂ), (u.val : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      fun z => a + 2 * (c * coordinateSum z).re

/-- Theorem 1.10 with field access to its derivative and deficit conclusions. -/
theorem fullTheoremOneTen_named {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph) :
    ∃ g : GinibreFullGradientL2 n, GinibreDifferentialDeficits hn u v g := by
  obtain ⟨g, hgradient, hsymmetry, hfirstDerivative, hsecondDerivative,
    hpoincare, hgenerator, hequality⟩ := fullTheoremOneTen hn u v hgraph
  exact ⟨g, ⟨hgradient, hsymmetry, hfirstDerivative, hsecondDerivative,
    hpoincare, hgenerator, hequality⟩⟩

/-- Theorem 1.10 with literal ordinary Schwartz distributional derivatives. -/
theorem fullTheoremOneTenSchwartz {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph) :
    ∃ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n u.val g ∧
      IsGinibreSymmetricWeakPair (u.val, g) ∧
      (∀ j, IsGaussianSchwartzDbar n (ginibreDifferentialDeficitVector n hn u.val)
        (ginibreDifferentialFirstDerivative n hn g j) j) ∧
      (∀ j k, IsGaussianSchwartzDbar n (ginibreDifferentialFirstDerivative n hn g j)
        (ginibreDifferentialSecondDerivative n hn g j k) k) ∧
      ginibreWeakEnergy n g - 2 * ginibreL2Variance n hn u.val =
        2 * ‖ginibreFullHolomorphicRemainder n hn u.val‖ ^ 2 +
          (4 / (n : ℝ)) * ginibreDifferentialSecondEnergy n hn g ∧
      ‖v.val‖ ^ 2 - 2 * ginibreWeakEnergy n g =
        ‖v.val + (2 : ℝ) • ginibreFullCenter n hn u.val‖ ^ 2 +
          4 * ‖ginibreFullHolomorphicRemainder n hn u.val‖ ^ 2 +
          (8 / (n : ℝ)) * ginibreDifferentialSecondEnergy n hn g ∧
      (ginibreWeakEnergy n g = 2 * ginibreL2Variance n hn u.val ↔
        ∃ (a : ℝ) (c : ℂ), (u.val : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
          fun z => a + 2 * (c * coordinateSum z).re) := by
  obtain ⟨g, deficits⟩ := fullTheoremOneTen_named hn u v hgraph
  exact ⟨g, deficits.distributional_gradient, deficits.symmetric_gradient,
    fun j => (gaussianSchwartzDbar_iff_weak hn _ _ j).mpr (deficits.first_derivatives j),
    fun j k => (gaussianSchwartzDbar_iff_weak hn _ _ k).mpr (deficits.second_derivatives j k),
    deficits.poincare_deficit, deficits.generator_deficit, deficits.equality_iff_affine⟩

end
end GinibrePoincare

