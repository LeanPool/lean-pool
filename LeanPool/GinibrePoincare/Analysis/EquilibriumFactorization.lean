/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/EquilibriumFactorization.lean.
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

public import LeanPool.GinibrePoincare.Concrete.CenterOfMass
public import LeanPool.GinibrePoincare.Concrete.MeasureModel
public import LeanPool.GinibrePoincare.Analysis.GinibreMassFiniteness

/-!
# Equilibrium Factorization (Theorem 1.2)

The geometric decomposition and pointwise density identity of Theorem 1.2.
The normalized density below is identified with the actual `ginibreMeasure`.
The probabilistic independence and Gaussian marginal law are proved in
`EquilibriumProbability.lean`. The recentered-radius Gamma law is proved in
`GinibreRadialGamma.lean`.
-/


@[expose] public section


open MeasureTheory
open scoped BigOperators

namespace GinibrePoincare

noncomputable section

-- Define the projection operators
/-- The unit vector along the common-translation line when the particle number is positive. -/
def unitAllOnes (n : ℕ) : Configuration n :=
  fun _ => (1 : ℂ) / Real.sqrt (n : ℝ)

/-- Orthogonal projection of a configuration onto its common-translation line. -/
def projectToCenterLine (n : ℕ) (z : Configuration n) : Configuration n :=
  fun _ => (coordinateSum z) / (n : ℂ)

/-- Remove the common-translation component from each particle coordinate. -/
def projectToOrthogonal (n : ℕ) (z : Configuration n) : Configuration n :=
  fun i => z i - (coordinateSum z) / (n : ℂ)

/-- The centered configuration obtained by subtracting the empirical particle mean. -/
def recenteredConfiguration (n : ℕ) (z : Configuration n) : Configuration n :=
  projectToOrthogonal n z

theorem decomposition_eq (n : ℕ) (z : Configuration n) :
    (fun i => z i) = (fun i => projectToCenterLine n z i + projectToOrthogonal n z i) := by
  ext i
  simp only [projectToCenterLine, projectToOrthogonal, coordinateSum]
  ring

/-- The total squared Euclidean norm used in the equilibrium factorization identities. -/
def configurationSqNorm' (z : Configuration n) : ℝ := configurationNormSq z

/-- Squared modulus of the unnormalized coordinate sum. -/
def centerOfMassSqNorm (n : ℕ) (z : Configuration n) : ℝ :=
  Complex.normSq (coordinateSum z)

/-- Total squared norm of the centered particle configuration. -/
def recenteredSqNorm (n : ℕ) (z : Configuration n) : ℝ :=
  configurationNormSq (recenteredConfiguration n z)

/-- Squared radius of the centered configuration, scaled by the particle number. -/
def radialObservable (n : ℕ) (z : Configuration n) : ℝ :=
  n * recenteredSqNorm n z

/-- Unnormalized Ginibre density with respect to configuration Lebesgue measure. -/
def rawGinibreDensity' (n : ℕ) (z : Configuration n) : ℝ :=
  ginibreLebesgueDensityReal n z

/-- The historical factorization order agrees with the canonical real density. -/
theorem rawGinibreDensity'_eq (n : ℕ) (z : Configuration n) :
    rawGinibreDensity' n z =
      ((n : ℝ) / Real.pi) ^ n * Real.exp (-n * configurationNormSq z) *
        Complex.normSq (vandermonde z) := by
  unfold rawGinibreDensity' ginibreLebesgueDensityReal gaussianWeight vandermondeWeight
  ring

/-- The recentered configuration belongs to the zero-sum hyperplane. -/
theorem coordinateSum_recentered (n : ℕ) (z : Configuration n) :
    coordinateSum (recenteredConfiguration n z) = 0 := by
  by_cases hn : n = 0
  · subst n
    simp [coordinateSum]
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    simp only [coordinateSum, recenteredConfiguration, projectToOrthogonal,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    simp

/-- Recentering is the identity on the zero-sum hyperplane. -/
theorem recentered_eq_self {n : ℕ} (z : Configuration n)
    (hz : coordinateSum z = 0) : recenteredConfiguration n z = z := by
  ext i
  simp [recenteredConfiguration, projectToOrthogonal, hz]

/-- Recentering is an idempotent projection. -/
theorem recentered_idempotent (n : ℕ) (z : Configuration n) :
    recenteredConfiguration n (recenteredConfiguration n z) =
      recenteredConfiguration n z :=
  recentered_eq_self _ (coordinateSum_recentered n z)

/-- The complex hyperplane orthogonal to the constant configurations. -/
def zeroSumHyperplane (n : ℕ) : Submodule ℂ (Configuration n) where
  carrier := {z | coordinateSum z = 0}
  zero_mem' := by simp [coordinateSum]
  add_mem' := by
    intro z w hz hw
    simp only [Set.mem_ofPred_eq, coordinateSum, Pi.add_apply, Finset.sum_add_distrib] at *
    rw [hz, hw, add_zero]
  smul_mem' := by
    intro a z hz
    simp only [Set.mem_ofPred_eq, coordinateSum, Pi.smul_apply, smul_eq_mul,
      ← Finset.mul_sum] at *
    rw [hz, mul_zero]

/-- The sum of the coordinates of the center-line projection is unchanged. -/
theorem coordinateSum_projectToCenterLine (n : ℕ) (hn : 0 < n)
    (z : Configuration n) :
    coordinateSum (projectToCenterLine n z) = coordinateSum z := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [coordinateSum, projectToCenterLine, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Splitting coordinates into their sum and their zero-sum component is a
complex linear equivalence. This also records the inverse coordinate change. -/
def equilibriumCoordinates (n : ℕ) (hn : 0 < n) :
    Configuration n ≃ₗ[ℂ] ℂ × zeroSumHyperplane n where
  toFun z := (coordinateSum z,
    ⟨recenteredConfiguration n z, coordinateSum_recentered n z⟩)
  invFun p := fun i => p.1 / (n : ℂ) + p.2.val i
  left_inv z := by
    ext i
    simp only [recenteredConfiguration, projectToOrthogonal]
    ring
  right_inv p := by
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hp : coordinateSum p.2.val = 0 := p.2.property
    have hs : coordinateSum (fun i => p.1 / (n : ℂ) + p.2.val i) = p.1 := by
      simp only [coordinateSum, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      change (n : ℂ) * (p.1 / (n : ℂ)) + coordinateSum p.2.val = p.1
      rw [hp, add_zero]
      field_simp
    apply Prod.ext
    · exact hs
    · apply Subtype.ext
      ext i
      simp only [recenteredConfiguration, projectToOrthogonal, hs]
      ring
  map_add' z w := by
    apply Prod.ext
    · simp [coordinateSum, Finset.sum_add_distrib]
    · apply Subtype.ext
      ext i
      simp [recenteredConfiguration, projectToOrthogonal, coordinateSum,
        Finset.sum_add_distrib]
      ring
  map_smul' a z := by
    apply Prod.ext
    · simp [coordinateSum, ← Finset.mul_sum]
    · apply Subtype.ext
      ext i
      simp [recenteredConfiguration, projectToOrthogonal, coordinateSum,
        ← Finset.mul_sum]
      ring

/-- The two components are orthogonal for the standard Hermitian form. -/
theorem center_recentered_orthogonal (n : ℕ) (z : Configuration n) :
    ∑ i : Fin n, star (projectToCenterLine n z i) *
      recenteredConfiguration n z i = 0 := by
  simp only [projectToCenterLine, ← Finset.mul_sum]
  change _ * coordinateSum (recenteredConfiguration n z) = 0
  rw [coordinateSum_recentered, mul_zero]

/-- Pythagorean identity for the decomposition: |z|^2 = |S|^2/n + |W|^2. -/
theorem pythagorean_identity (n : ℕ) (z : Configuration n) :
    configurationNormSq z =
      (centerOfMassSqNorm n z) / (n : ℝ) + recenteredSqNorm n z := by
  by_cases hn : n = 0
  · subst n
    simp [configurationNormSq, centerOfMassSqNorm, coordinateSum, recenteredSqNorm]
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    let c : ℂ := coordinateSum z / (n : ℂ)
    have hc : (n : ℂ) * c = coordinateSum z := by
      dsimp [c]
      field_simp
    have hs : ∑ i : Fin n, (z i - c) = 0 := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      change coordinateSum z - (n : ℂ) * c = 0
      rw [hc, sub_self]
    have hcross : ∑ i : Fin n, ((z i - c) * (starRingEnd ℂ) c).re = 0 := by
      rw [← Complex.re_sum, ← Finset.sum_mul, hs, zero_mul, Complex.zero_re]
    have hnorm : ∑ i : Fin n, Complex.normSq (z i) =
        ∑ i : Fin n, Complex.normSq (z i - c) + (n : ℝ) * Complex.normSq c := by
      calc
        _ = ∑ i : Fin n, Complex.normSq ((z i - c) + c) := by simp
        _ = _ := by
          simp only [Complex.normSq_add, Finset.sum_add_distrib,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← Finset.mul_sum, hcross, mul_zero, add_zero]
    have hcNorm : (n : ℝ) * Complex.normSq c =
        Complex.normSq (coordinateSum z) / (n : ℝ) := by
      dsimp [c]
      rw [map_div₀, Complex.normSq_natCast]
      field_simp
    change (∑ i : Fin n, Complex.normSq (z i)) =
      Complex.normSq (coordinateSum z) / (n : ℝ) +
        ∑ i : Fin n, Complex.normSq (z i - c)
    rw [hnorm, hcNorm, add_comm]

/-- The Vandermonde is invariant under translation along the center line. -/
theorem vandermonde_translation_invariant (n : ℕ) (z : Configuration n) :
    vandermonde z = vandermonde (recenteredConfiguration n z) := by
  unfold recenteredConfiguration projectToOrthogonal
  rw [vandermonde_eq_product, vandermonde_eq_product]
  refine Finset.prod_congr rfl fun i _ => ?_
  refine Finset.prod_congr rfl fun j hj => ?_
  ring

/-- Equilibrium Factorization: φ_n(z) = e^{-|S(z)|^2} φ_n(W). -/
theorem equilibrium_factorization (n : ℕ) (hn : 0 < n) (z : Configuration n) :
    rawGinibreDensity' n z =
      Real.exp (-centerOfMassSqNorm n z) * rawGinibreDensity' n (recenteredConfiguration n z) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [rawGinibreDensity'_eq]
  rw [pythagorean_identity n z, vandermonde_translation_invariant n z]
  have he : -(n : ℝ) * (centerOfMassSqNorm n z / (n : ℝ) + recenteredSqNorm n z) =
      -centerOfMassSqNorm n z + -(n : ℝ) * recenteredSqNorm n z := by
    field_simp
    ring
  rw [he, Real.exp_add]
  change _ = _ * (_ * Real.exp (-(n : ℝ) * recenteredSqNorm n z) * _)
  ring

/-- Explicit real-valued Lebesgue density of the normalized Ginibre measure. -/
def equilibriumGinibreDensity (n : ℕ) (z : Configuration n) : ℝ :=
  (ginibreNormalizingMass n).toReal⁻¹ * rawGinibreDensity' n z

theorem rawGinibreDensity_nonneg (n : ℕ) (z : Configuration n) :
    0 ≤ rawGinibreDensity' n z :=
  ginibreLebesgueDensityReal_nonneg n z

/-- The canonical real density is measurable. -/
theorem measurable_ginibreLebesgueDensityReal (n : ℕ) :
    Measurable (ginibreLebesgueDensityReal n) := by
  unfold ginibreLebesgueDensityReal gaussianWeight vandermondeWeight configurationNormSq
  have hv := continuous_vandermonde (n := n)
  fun_prop

theorem measurable_rawGinibreDensity (n : ℕ) :
    Measurable (rawGinibreDensity' n) :=
  measurable_ginibreLebesgueDensityReal n

/-- The raw density is the product of the existing Gaussian and Vandermonde densities. -/
theorem ofReal_rawGinibreDensity (n : ℕ) (z : Configuration n) :
    ENNReal.ofReal (rawGinibreDensity' n z) =
      complexGaussianDensity n z * vandermondeDensity z := by
  simpa only [rawGinibreDensity', mul_comm] using
    (vandermondeDensity_mul_complexGaussianDensity n z).symm

/-- The density in the factorization is the density of the concrete raw measure. -/
theorem rawGinibreMeasure_eq_equilibriumDensity (n : ℕ) (hn : 0 < n) :
    rawGinibreMeasure n = (configurationVolume n).withDensity
      (fun z => ENNReal.ofReal (rawGinibreDensity' n z)) := by
  unfold rawGinibreMeasure
  rw [complexGaussianDensityIdentification n hn]
  unfold complexGaussianDensityMeasure
  have hm : Measurable (complexGaussianDensity n) := by
    unfold complexGaussianDensity gaussianWeight configurationNormSq
    fun_prop
  rw [← withDensity_mul _ hm (measurable_vandermondeDensity (n := n))]
  congr 1
  funext z
  exact (ofReal_rawGinibreDensity n z).symm

/-- Identification with the normalized measure, with its actual normalizing mass. -/
theorem ginibreMeasure_eq_equilibriumDensity (n : ℕ) (hn : 0 < n) :
    ginibreMeasure n = (configurationVolume n).withDensity
      (fun z => ENNReal.ofReal (equilibriumGinibreDensity n z)) := by
  have hm := ginibreMassEvaluation n hn
  have hmass : ENNReal.ofReal ((ginibreNormalizingMass n).toReal⁻¹) =
      (ginibreNormalizingMass n)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hm.1.ne' hm.2.ne),
      ENNReal.ofReal_toReal hm.2.ne]
  unfold ginibreMeasure
  rw [rawGinibreMeasure_eq_equilibriumDensity n hn]
  have hf : Measurable (fun z => ENNReal.ofReal (rawGinibreDensity' n z)) :=
    ENNReal.measurable_ofReal.comp (measurable_rawGinibreDensity n)
  rw [← withDensity_smul _ hf]
  congr 1
  funext z
  simp only [equilibriumGinibreDensity, Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.ofReal_mul (by positivity), hmass]

/-- The paper's factorization identity for the actual normalized density. -/
theorem normalized_equilibrium_factorization (n : ℕ) (hn : 0 < n)
    (z : Configuration n) :
    equilibriumGinibreDensity n z = Real.exp (-centerOfMassSqNorm n z) *
      equilibriumGinibreDensity n (recenteredConfiguration n z) := by
  unfold equilibriumGinibreDensity
  rw [equilibrium_factorization n hn z]
  ring

/-- For one particle, the recentered component and radius vanish. -/
theorem recentered_one (z : Configuration 1) :
    recenteredConfiguration 1 z = 0 := by
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [recenteredConfiguration, projectToOrthogonal, coordinateSum]

theorem radialObservable_one (z : Configuration 1) : radialObservable 1 z = 0 := by
  simp [radialObservable, recenteredSqNorm, recentered_one, configurationNormSq]

/-- The density, Pythagorean and Vandermonde identities separating the center-of-mass
component. -/
structure EquilibriumFactorization (n : ℕ) : Prop where
  densityFactorization :
    ∀ z : Configuration n,
      rawGinibreDensity' n z =
        Real.exp (-centerOfMassSqNorm n z) *
        rawGinibreDensity' n (recenteredConfiguration n z)
  pythagoras :
    ∀ z : Configuration n,
      configurationNormSq z =
        (centerOfMassSqNorm n z) / (n : ℝ) + recenteredSqNorm n z
  vandermondeInvariant :
    ∀ z : Configuration n,
      vandermonde z = vandermonde (recenteredConfiguration n z)

theorem equilibriumFactorization_instance (n : ℕ) (hn : 0 < n) :
    EquilibriumFactorization n := by
  constructor
  · intro z
    exact equilibrium_factorization n hn z
  · intro z
    exact pythagorean_identity n z
  · intro z
    exact vandermonde_translation_invariant n z

end

end GinibrePoincare
