/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeSpectralPoincare.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityWeakDeficit
public import LeanPool.GinibrePoincare.Analysis.GaussianGinibreProjectionIntertwining
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorEnergy
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupConstants

/-! # Section 3: the two number-operator forms

The Gaussian number forms are defined by their Hermite spectral resolution.
Their domains require convergence of the energy series. The Gaussian gap below
is obtained by comparing the spectral multipliers, without a deficit identity.
The anti-Vandermonde factor is the conjugate of the Vandermonde factor on real
inputs. Thus both factors, not just the holomorphic half-distance bound, enter
into the final weak-domain inequality.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory ComplexHermite
open scoped BigOperators

/-- Quadratic form of `N_bar`, with eigenvalues `n |q|`. -/
def spectralGaussianBarNumberForm {n : ℕ} (hn : 0 < n)
    (w : Lp ℂ 2 (complexGaussianMeasure n)) : ℝ :=
  (n : ℝ) * ∑' k : ℕ, (k + 1) * positiveHermiteModeMass hn w k

/-- The actual form domain, rather than a totalized divergent spectral sum. -/
def spectralGaussianBarNumberDomain {n : ℕ} (hn : 0 < n)
    (w : Lp ℂ 2 (complexGaussianMeasure n)) : Prop :=
  Summable (fun k : ℕ => (k + 1) * positiveHermiteModeMass hn w k)

/-- `N_z` is the conjugate number form, with the conjugate form domain. -/
def spectralGaussianNumberForm {n : ℕ} (hn : 0 < n)
    (w : Lp ℂ 2 (complexGaussianMeasure n)) : ℝ :=
  spectralGaussianBarNumberForm hn (star w)

/-- The form domain of the conjugate number operator `N_z`: `star w` lies in the form domain
of `N_bar`. -/
def spectralGaussianNumberDomain {n : ℕ} (hn : 0 < n)
    (w : Lp ℂ 2 (complexGaussianMeasure n)) : Prop :=
  spectralGaussianBarNumberDomain hn (star w)

/-- Spectral multiplier comparison: `N_bar ≥ n (I-P_H)`. -/
theorem spectralGaussianBarNumberForm_gap {n : ℕ} (hn : 0 < n)
    (w : Lp ℂ 2 (complexGaussianMeasure n))
    (hw : spectralGaussianBarNumberDomain hn w) :
    (n : ℝ) * (‖w‖ ^ 2 - ‖gaussianHermiteMode hn 0 w‖ ^ 2) ≤
      spectralGaussianBarNumberForm hn w := by
  have hcompare : (∑' k, positiveHermiteModeMass hn w k) ≤
      ∑' k : ℕ, (k + 1) * positiveHermiteModeMass hn w k := by
    apply Summable.tsum_le_tsum _ (summable_positiveHermiteModeMass hn w) hw
    intro k
    have hm : 0 ≤ positiveHermiteModeMass hn w k := sq_nonneg _
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) k
      linarith
    nlinarith
  have hparseval := norm_sq_eq_zeroMode_add_positiveModeMass hn w
  unfold spectralGaussianBarNumberForm
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  linarith

/-- The number form agrees with the actual Gaussian derivative energy. -/
theorem spectralGaussianBarNumberForm_eq_dbar {n : ℕ} (hn : 0 < n)
    (w : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hc : ∀ j pq, gaussianHermiteCoefficient hn (D j) pq =
      (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn w (raiseHermiteIndex j pq)) :
    spectralGaussianBarNumberDomain hn w ∧
      spectralGaussianBarNumberForm hn w = ∑ j, ‖D j‖ ^ 2 := by
  have he := hasSum_weighted_gaussianHermiteMode_of_coefficient_raise hn w D hc
  have hp := hasSum_weighted_positiveHermiteModeMass_of_hasSum_modes hn w _ he
  refine ⟨hp.summable, ?_⟩
  unfold spectralGaussianBarNumberForm
  rw [hp.tsum_eq]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- Normalized anti-Vandermonde transform. Its pointwise multiplier is
`conj(V_n)/sqrt(c'_n)`; it is defined on actual weighted L² classes. -/
def spectralAntiVandermonde {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (ginibreMeasure n)) : Lp ℂ 2 (complexGaussianMeasure n) :=
  star (normalizedVandermondeL2 n hn (star u))

theorem spectralAntiVandermonde_ae {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (ginibreMeasure n)) :
    (spectralAntiVandermonde hn u : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n]
      fun z => star (normalizedVandermondeMultiplier n z) * u z := by
  have hu := (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure
    (ginibreMassEvaluation n hn)).ae_eq (Lp.coeFn_star u)
  filter_upwards [Lp.coeFn_star (normalizedVandermondeL2 n hn (star u)),
    normalizedVandermondeL2_coeFn_public n hn (star u), hu] with z hs hv hu
  change (star (normalizedVandermondeL2 n hn (star u))) z = _
  simp only [Pi.star_apply] at hs hu
  rw [hs, hv, hu]
  simp

private theorem gaussianLp_star_star {n : ℕ}
    (w : Lp ℂ 2 (complexGaussianMeasure n)) : star (star w) = w := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (star w), Lp.coeFn_star w] with z h1 h2
  simp only [Pi.star_apply] at h1 h2
  rw [h1, h2]
  simp

private theorem realValue_star {n : ℕ} (u : GinibreFullValueL2 n) :
    star (ginibreFullComplexOfReal n u) = ginibreFullComplexOfReal n u := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (ginibreFullComplexOfReal n u),
    ginibreFullComplexOfReal_ae n u] with z hs hu
  simp only [Pi.star_apply] at hs
  rw [hs, hu]
  simp

/-- Two-sided factorization (3.10), extended to every actual symmetric real
weak-H¹ pair. Both number forms have internally proved finite energy. -/
theorem spectralGinibre_two_number_factorization {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (hs : IsGinibreSymmetricWeakPair (u, g)) :
    let w := ginibreFullCenteredTransform n hn u
    let a := spectralAntiVandermonde hn
      (ginibreFullComplexOfReal n (ginibreFullCenter n hn u))
    spectralGaussianBarNumberDomain hn w ∧ spectralGaussianNumberDomain hn a ∧
      ginibreWeakEnergy n g = (2 / (n : ℝ)) *
        (spectralGaussianBarNumberForm hn w + spectralGaussianNumberForm hn a) := by
  dsimp
  obtain ⟨huc, hsc⟩ := ginibreFullCenter_weak_pair hn u g hu hs
  obtain ⟨hd, he⟩ := spectralGaussianBarNumberForm_eq_dbar hn
    (ginibreFullCenteredTransform n hn u) (ginibreFullTransformedDbar n hn · g)
    (ginibreFullTransformedDbar_weak_coefficient hn (ginibreFullCenter n hn u) g huc hsc)
  have ha : spectralGaussianNumberForm hn (spectralAntiVandermonde hn
      (ginibreFullComplexOfReal n (ginibreFullCenter n hn u))) =
      spectralGaussianBarNumberForm hn (ginibreFullCenteredTransform n hn u) := by
    unfold spectralGaussianNumberForm spectralAntiVandermonde
    rw [gaussianLp_star_star, realValue_star]
    rfl
  have had : spectralGaussianNumberDomain hn (spectralAntiVandermonde hn
      (ginibreFullComplexOfReal n (ginibreFullCenter n hn u))) := by
    unfold spectralGaussianNumberDomain spectralAntiVandermonde
    rw [gaussianLp_star_star, realValue_star]
    exact hd
  refine ⟨hd, had, ?_⟩
  rw [ha, he, ginibreFullTransformedDbar_norm_sum hn g]
  unfold ginibreWeakEnergy
  ring

/-- Section 3's independently assembled spectral proof of the sharp inequality
on the full symmetric ordinary distributional weak-H¹ domain. -/
theorem spectral_ginibre_symmetric_weak_poincare {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (hs : IsGinibreSymmetricWeakPair (u, g)) :
    ginibreL2Variance n hn u ≤ ginibreWeakEnergy n g / 2 := by
  obtain ⟨hd, _, hfac⟩ := spectralGinibre_two_number_factorization hn u g hu hs
  have hgap := spectralGaussianBarNumberForm_gap hn (ginibreFullCenteredTransform n hn u) hd
  have hw : ‖ginibreFullCenteredTransform n hn u‖ ^ 2 = ginibreL2Variance n hn u := by
    unfold ginibreFullCenteredTransform
    rw [(normalizedVandermondeL2 n hn).norm_map, ginibreFullCenteredValue_norm_sq]
  have hz := ginibreFullWeak_zero_mode_norm hn u g hu hs
  have hgeom := ginibreFullWeak_holomorphic_geometry hn u g hu hs
  have ha : spectralGaussianNumberForm hn (spectralAntiVandermonde hn
      (ginibreFullComplexOfReal n (ginibreFullCenter n hn u))) =
      spectralGaussianBarNumberForm hn (ginibreFullCenteredTransform n hn u) := by
    unfold spectralGaussianNumberForm spectralAntiVandermonde
    rw [gaussianLp_star_star, realValue_star]
    rfl
  rw [ha] at hfac
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hEn : (n : ℝ) * ginibreWeakEnergy n g =
      4 * spectralGaussianBarNumberForm hn (ginibreFullCenteredTransform n hn u) := by
    rw [hfac]
    field_simp
    ring
  rw [hw, hz] at hgap
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have htarget : 2 * ginibreL2Variance n hn u ≤ ginibreWeakEnergy n g := by
    have hp : (n : ℝ) * (2 * ginibreL2Variance n hn u) ≤
        (n : ℝ) * ginibreWeakEnergy n g := by
      nlinarith [sq_nonneg ‖ginibreFullHolomorphicRemainder n hn u‖]
    nlinarith
  linarith

/-- Section 3's generator gap on the actual full complex self-adjoint graph.
The real and imaginary parts use the independently assembled spectral route. -/
theorem spectral_ginibre_full_generator_gap {n : ℕ} (hn : 0 < n)
    (u v : ginibreSymmetricL2 n) (hgraph : (u, v) ∈ (ginibreFullGenerator n hn).graph) :
    2 * (ginibreL2Variance n hn (ginibreFullSymmetricRe n u).val +
      ginibreL2Variance n hn (ginibreFullSymmetricIm n u).val) ≤ -(inner ℂ v u).re := by
  obtain ⟨gr, gi, hgr, hsr, hgi, hsi, he⟩ :=
    ginibreFullGenerator_complex_energy_identity hn u v hgraph
  have hr := spectral_ginibre_symmetric_weak_poincare hn
    (ginibreFullSymmetricRe n u).val gr hgr hsr
  have hi := spectral_ginibre_symmetric_weak_poincare hn
    (ginibreFullSymmetricIm n u).val gi hgi hsi
  linarith

end
end GinibrePoincare

