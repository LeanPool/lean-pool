/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeSpectralDifferentialFactorization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeBochnerKodairaDifferential
public import LeanPool.GinibrePoincare.Analysis.GinibreIntegrationByParts
public import LeanPool.GinibrePoincare.Analysis.ComplexGeneratorCalculus
public import LeanPool.GinibrePoincare.Analysis.FiniteHermiteDeficit
public import LeanPool.GinibrePoincare.Analysis.L2RepresentativeBridges
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-!
# Alternative spectral differential factorization

Part of the poincaré deficits and equality development of the
Ginibre Poincaré formalization.

Main results: `spectralDifferentialBarNumber_eq_adjoint`,
`spectral_complex_differential_factorization`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

/-- Literal Gaussian antiholomorphic number operator `∂bar*∂bar`. -/
def spectralDifferentialBarNumber {n : ℕ} (f : Configuration n → ℂ)
    (z : Configuration n) : ℂ :=
  ∑ j : Fin n, ((n : ℂ) * conj (z j) * dbarComponent f j z -
    bkPartial (dbarComponent f j) j z)

/-- Literal Gaussian holomorphic number operator `∂*∂`. -/
def spectralDifferentialNumber {n : ℕ} (f : Configuration n → ℂ)
    (z : Configuration n) : ℂ :=
  ∑ j : Fin n, ((n : ℂ) * z j * bkPartial f j z - dbarComponent (bkPartial f j) j z)

theorem spectralDifferentialBarNumber_eq_adjoint {n : ℕ} (f : Configuration n → ℂ)
    (hf : ContDiff ℝ ∞ f) (z : Configuration n) :
    spectralDifferentialBarNumber f z =
      ∑ j : Fin n, gaussianDbarAdjointTest j (dbarComponent f j) z := by
  unfold spectralDifferentialBarNumber
  apply Finset.sum_congr rfl
  intro j hj
  rw [bkAdjoint_eq ((bkDbar_contDiff hf j).differentiable (by simp))]

theorem spectralPartial_vandermonde {n : ℕ} (z : Configuration n)
    (hz : CollisionFree z) (j : Fin n) :
    bkPartial vandermonde j z = vandermonde z * ∑ k ∈ Finset.univ.erase j, (1 : ℂ) / (z j - z k) :=
        by
  unfold bkPartial bkDirectional
  change (1 / 2 : ℂ) *
    (fderiv ℝ vandermonde z (coordinateDirection j 1) -
      Complex.I * fderiv ℝ vandermonde z (coordinateDirection j Complex.I)) = _
  rw [fderiv_vandermonde_apply_coordinateDirection z hz j 1,
    fderiv_vandermonde_apply_coordinateDirection z hz j Complex.I]
  have hi : (∑ k ∈ Finset.univ.erase j, Complex.I / (z j - z k)) =
      Complex.I * ∑ k ∈ Finset.univ.erase j, (1 : ℂ) / (z j - z k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hi]
  calc
    _ = (1 / 2 : ℂ) * (1 - Complex.I^2) * vandermonde z *
        ∑ k ∈ Finset.univ.erase j, (1 : ℂ) / (z j - z k) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

private theorem spectralPartial_conj_vandermonde {n : ℕ} (j : Fin n) (z : Configuration n) :
    bkPartial (fun w => conj (vandermonde w)) j z = 0 := by
  have hc : Differentiable ℝ (fun w : Configuration n => conj (vandermonde w)) :=
    Complex.conjCLE.differentiable.comp ((differentiable_vandermonde n).restrictScalars ℝ)
  rw [bkPartial_eq_conj_dbar hc]
  simp only [starRingEnd_self_apply]
  change conj (dbarComponent vandermonde j z) = 0
  rw [dbarComponent_vandermonde]
  simp

private theorem spectralDbar_conj_vandermonde {n : ℕ} (j : Fin n) (z : Configuration n) :
    dbarComponent (fun w => conj (vandermonde w)) j z = conj (bkPartial vandermonde j z) := by
  rw [bkPartial_eq_conj_dbar ((differentiable_vandermonde n).restrictScalars ℝ)]
  simp

/-- Coordinate version of (3.3), before grouping the Coulomb pairs. -/
theorem spectralBarNumber_vandermonde_coordinate {n : ℕ}
    (f : Configuration n → ℂ) (hf : ContDiff ℝ ∞ f)
    (z : Configuration n) (hz : CollisionFree z) (j : Fin n) :
    ((n : ℂ) * conj (z j) * dbarComponent (fun w => vandermonde w * f w) j z -
      bkPartial (dbarComponent (fun w => vandermonde w * f w) j) j z) / vandermonde z =
    -bkPartial (dbarComponent f j) j z + (n : ℂ) * conj (z j) * dbarComponent f j z -
      (∑ k ∈ Finset.univ.erase j, (1 : ℂ) / (z j - z k)) * dbarComponent f j z := by
  have he : dbarComponent (fun w => vandermonde w * f w) j =
      fun w => vandermonde w * dbarComponent f j w := by
    funext w
    exact dbarComponent_holomorphic_mul (differentiable_vandermonde n)
      (hf.differentiable (by simp)) j w
  rw [he, bkPartial_mul ((differentiable_vandermonde n).restrictScalars ℝ)
    ((bkDbar_contDiff hf j).differentiable (by simp)), spectralPartial_vandermonde z hz j]
  have hv : vandermonde z ≠ 0 := (vandermonde_ne_zero_iff z).mpr hz
  field_simp
  ring

/-- Coordinate version of (3.4), for the anti-Vandermonde factor. -/
theorem spectralNumber_antivandermonde_coordinate {n : ℕ}
    (f : Configuration n → ℂ) (hf : ContDiff ℝ ∞ f)
    (z : Configuration n) (hz : CollisionFree z) (j : Fin n) :
    ((n : ℂ) * z j * bkPartial (fun w => conj (vandermonde w) * f w) j z -
      dbarComponent (bkPartial (fun w => conj (vandermonde w) * f w) j) j z) / conj (vandermonde z)
          =
    -bkPartial (dbarComponent f j) j z + (n : ℂ) * z j * bkPartial f j z -
      (∑ k ∈ Finset.univ.erase j, (1 : ℂ) / conj (z j - z k)) * bkPartial f j z := by
  have hc : Differentiable ℝ (fun w : Configuration n => conj (vandermonde w)) :=
    Complex.conjCLE.differentiable.comp ((differentiable_vandermonde n).restrictScalars ℝ)
  have he : bkPartial (fun w => conj (vandermonde w) * f w) j =
      fun w => conj (vandermonde w) * bkPartial f j w := by
    funext w
    rw [bkPartial_mul hc (hf.differentiable (by simp)), spectralPartial_conj_vandermonde,
      zero_mul, zero_add]
  rw [he, dbarComponent_mul hc ((bkPartial_contDiff hf j).differentiable (by simp)),
    spectralDbar_conj_vandermonde, spectralPartial_vandermonde z hz j]
  simp only [map_mul, map_sum]
  rw [← bkDbar_partial_comm hf j j]
  have hv : conj (vandermonde z) ≠ 0 := by
    simpa using (vandermonde_ne_zero_iff z).mpr hz
  field_simp
  ring_nf
  simp only [map_inv₀]

/-- Every off-diagonal Coulomb sum groups into unordered particle pairs. -/
theorem spectralCoulomb_pair_sum {n : ℕ} (z : Configuration n) (a : Fin n → ℂ) :
    (∑ j : Fin n, (∑ k ∈ Finset.univ.erase j, (1 : ℂ) / (z j - z k)) * a j) =
      ∑ j : Fin n, ∑ k ∈ Finset.Ioi j, (a j - a k) / (z j - z k) := by
  have herase (j : Fin n) :
      (∑ k ∈ Finset.univ.erase j, (1 : ℂ) / (z j - z k)) * a j =
        ∑ k : Fin n, a j / (z j - z k) := by
    rw [Finset.sum_mul]
    have hh := Finset.sum_erase_add Finset.univ (fun k => a j / (z j - z k)) (Finset.mem_univ j)
    simp only [sub_self, div_zero, add_zero] at hh
    rw [← hh]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp_rw [herase]
  have hsplit (j k : Fin n) : a j / (z j - z k) =
      (if j < k then a j / (z j - z k) else 0) +
        (if k < j then a j / (z j - z k) else 0) := by
    rcases lt_trichotomy j k with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst k; simp
    · simp [h, not_lt_of_gt h]
  rw [show (∑ j : Fin n, ∑ k : Fin n, a j / (z j - z k)) =
    ∑ j : Fin n, ∑ k : Fin n,
      ((if j < k then a j / (z j - z k) else 0) +
        (if k < j then a j / (z j - z k) else 0)) by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    exact hsplit j k]
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun j k => if k < j then a j / (z j - z k) else 0)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_add_distrib]
  have hfilter : (∑ k : Fin n, ((if j < k then a j / (z j - z k) else 0) +
      if j < k then a k / (z k - z j) else 0)) =
      ∑ k ∈ Finset.Ioi j, (a j - a k) / (z j - z k) := by
    have hh (k : Fin n) : ((if j < k then a j / (z j - z k) else 0) +
      if j < k then a k / (z k - z j) else 0) =
        if j < k then a j / (z j - z k) + a k / (z k - z j) else 0 := by
      split_ifs <;> simp
    simp_rw [hh]
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (fun k : Fin n => j < k) = Finset.Ioi j := by ext k; simp
    rw [he]
    apply Finset.sum_congr rfl
    intro k hk
    rw [show z k - z j = -(z j - z k) by ring, div_neg]
    ring
  exact hfilter

/-- Literal first number pullback (3.3). -/
theorem spectralBarNumber_vandermonde {n : ℕ}
    (f : Configuration n → ℂ) (hf : ContDiff ℝ ∞ f)
    (z : Configuration n) (hz : CollisionFree z) :
    spectralDifferentialBarNumber (fun w => vandermonde w * f w) z / vandermonde z =
      -(∑ j : Fin n, bkPartial (dbarComponent f j) j z) +
        (n : ℂ) * ∑ j : Fin n, conj (z j) * dbarComponent f j z -
        ∑ j : Fin n, ∑ k ∈ Finset.Ioi j,
          (dbarComponent f j z - dbarComponent f k z) / (z j - z k) := by
  unfold spectralDifferentialBarNumber
  rw [Finset.sum_div]
  simp_rw [spectralBarNumber_vandermonde_coordinate f hf z hz]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [spectralCoulomb_pair_sum]
  rw [Finset.mul_sum]
  simp only [mul_assoc]

/-- Literal second number pullback (3.4). -/
theorem spectralNumber_antivandermonde {n : ℕ}
    (f : Configuration n → ℂ) (hf : ContDiff ℝ ∞ f)
    (z : Configuration n) (hz : CollisionFree z) :
    spectralDifferentialNumber (fun w => conj (vandermonde w) * f w) z / conj (vandermonde z) =
      -(∑ j : Fin n, bkPartial (dbarComponent f j) j z) +
        (n : ℂ) * ∑ j : Fin n, z j * bkPartial f j z -
        ∑ j : Fin n, ∑ k ∈ Finset.Ioi j,
          (bkPartial f j z - bkPartial f k z) / conj (z j - z k) := by
  unfold spectralDifferentialNumber
  rw [Finset.sum_div]
  simp_rw [spectralNumber_antivandermonde_coordinate f hf z hz]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hp := spectralCoulomb_pair_sum (fun j => conj (z j)) (fun j => bkPartial f j z)
  simp only [← map_sub] at hp
  rw [hp, Finset.mul_sum]
  simp only [mul_assoc]

/-- Real-linear derivatives decompose exactly into the two Wirtinger terms. -/
theorem spectral_coordinate_derivative {n : ℕ} (f : Configuration n → ℂ)
    (j : Fin n) (w : ℂ) (z : Configuration n) :
    fderiv ℝ f z (coordinateDirection j w) =
      w * bkPartial f j z + conj w * dbarComponent f j z := by
  rw [coordinateDirection_eq_re_smul_real_add_im_smul_imaginary, map_add, map_smul, map_smul]
  unfold bkPartial bkDirectional dbarComponent
  simp only [Complex.real_smul]
  rcases w with ⟨a, b⟩
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;>
      ring

/-- The mixed Wirtinger derivative is exactly one quarter of the real coordinate Laplacian. -/
theorem spectral_partial_dbar_laplacian {n : ℕ} (f : Configuration n → ℂ)
    (hf : ContDiff ℝ ∞ f) (j : Fin n) (z : Configuration n) :
    4 * bkPartial (dbarComponent f j) j z =
      complexSecondDirectionalDerivative f (realCoordinateDirection j) z +
        complexSecondDirectionalDerivative f (imaginaryCoordinateDirection j) z := by
  unfold bkPartial
  rw [bkDirectional_dbar _ hf, bkDirectional_dbar _ hf,
    bkDirectional_comm (imaginaryCoordinateDirection j) (realCoordinateDirection j) hf]
  change 4 * ((1 / 2 : ℂ) *
    ((1 / 2 : ℂ) * (_ + Complex.I * _) - Complex.I * ((1 / 2 : ℂ) * (_ + Complex.I * _)))) = _
  simp only [complexSecondDirectionalDerivative, bkDirectional]
  ring_nf
  simp only [Complex.I_sq]
  ring_nf
  rfl

/-- Each Coulomb directional derivative is the paired holomorphic and
antiholomorphic drift from (3.3)–(3.4). -/
theorem spectral_coulomb_derivative {n : ℕ} (f : Configuration n → ℂ)
    (j k : Fin n) (z : Configuration n) :
    fderiv ℝ f z (coulombPairDirection j k z) =
      (bkPartial f j z - bkPartial f k z) / conj (z j - z k) +
        (dbarComponent f j z - dbarComponent f k z) / (z j - z k) := by
  unfold coulombPairDirection
  rw [map_sub, spectral_coordinate_derivative, spectral_coordinate_derivative]
  have hw : (z j - z k) / (Complex.normSq (z j - z k) : ℂ) = (conj (z j - z k))⁻¹ := by
    rw [Complex.inv_def, starRingEnd_self_apply, Complex.normSq_conj]
    simp only [div_eq_mul_inv, Complex.ofReal_inv]
  rw [hw]
  simp only [map_inv₀, starRingEnd_self_apply]
  ring

/-- The literal two-sided number-operator factorization (3.1), on the
paper's complex smooth collision-free core (and, more generally, at every
collision-free point of a smooth complex observable). -/
theorem spectral_complex_differential_factorization {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℂ) (hf : ContDiff ℝ ∞ f)
    (z : Configuration n) (hz : CollisionFree z) :
    complexGinibrePregenerator n f z = -(2 / (n : ℂ)) *
      (spectralDifferentialBarNumber (fun w => vandermonde w * f w) z / vandermonde z +
        spectralDifferentialNumber (fun w => conj (vandermonde w) * f w) z / conj (vandermonde z))
            := by
  rw [complexGinibrePregenerator_eq_direct n f (hf.differentiable (by simp))
      (fun v => (bkDirectional_contDiff v hf).differentiable (by simp)),
    spectralBarNumber_vandermonde f hf z hz, spectralNumber_antivandermonde f hf z hz]
  unfold directComplexGinibrePregenerator
  simp_rw [← spectral_partial_dbar_laplacian f hf,
    spectral_coordinate_derivative, spectral_coulomb_derivative]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_natCast]
  simp_rw [Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

end
end GinibrePoincare

