/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/PermutationLp.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreMassPositivity

/-! # Permutation actions and symmetric/alternating `L²` subspaces -/


@[expose] public section


open MeasureTheory
open scoped ENNReal

namespace GinibrePoincare

noncomputable section

/-- Coordinate permutation as a measurable equivalence of configuration
space. -/
def permutationMeasurableEquiv {n : ℕ} (σ : ParticlePermutation n) :
    Configuration n ≃ᵐ Configuration n :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℂ) σ.symm

@[simp]
theorem permutationMeasurableEquiv_apply {n : ℕ}
    (σ : ParticlePermutation n) (z : Configuration n) :
    permutationMeasurableEquiv σ z = permute σ z := by
  simp [permutationMeasurableEquiv, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft, Equiv.piCongrLeft']
  rfl

/-- The product complex Gaussian law is invariant under coordinate
permutations. -/
theorem gaussian_measurePreserving_permute {n : ℕ}
    (σ : ParticlePermutation n) :
    MeasurePreserving (permute σ) (complexGaussianMeasure n)
      (complexGaussianMeasure n) := by
  unfold complexGaussianMeasure complexGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_pi]
  have heq : ⇑(permutationMeasurableEquiv σ) = permute σ := by
    funext z
    exact permutationMeasurableEquiv_apply σ z
  rw [← heq]
  exact measurePreserving_piCongrLeft
    (fun _ : Fin n ↦ (complexCoordinateGaussianProbability n : Measure ℂ)) σ.symm

theorem vandermondeDensity_permute {n : ℕ} (σ : ParticlePermutation n)
    (z : Configuration n) :
    vandermondeDensity (permute σ z) = vandermondeDensity z := by
  unfold vandermondeDensity vandermondeWeight
  rw [vandermonde_permute]
  congr 1
  rw [map_mul]
  have hs : Complex.normSq (permutationSign σ) = 1 := by
    unfold permutationSign
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · simp [h, Complex.normSq_apply]
    · simp [h, Complex.normSq_apply]
  rw [hs, one_mul]

/-- The normalized Ginibre law is invariant under coordinate permutations. -/
theorem ginibre_measurePreserving_permute {n : ℕ}
    (σ : ParticlePermutation n) :
    MeasurePreserving (permute σ) (ginibreMeasure n)
      (ginibreMeasure n) := by
  refine ⟨(gaussian_measurePreserving_permute σ).measurable, ?_⟩
  unfold ginibreMeasure rawGinibreMeasure
  rw [Measure.map_smul _ (gaussian_measurePreserving_permute σ).measurable.aemeasurable]
  congr 1
  have hd : vandermondeDensity ∘ permute σ =
      (vandermondeDensity : Configuration n → ℝ≥0∞) := by
    funext z
    exact vandermondeDensity_permute σ z
  nth_rw 1 [← hd]
  have heq : ⇑(permutationMeasurableEquiv σ) = permute σ := by
    funext z
    exact permutationMeasurableEquiv_apply σ z
  rw [← heq] at hd ⊢
  exact MeasurePreserving.map_withDensity_comp
    (permutationMeasurableEquiv σ)
    (heq ▸ gaussian_measurePreserving_permute σ)
    measurable_vandermondeDensity

/-- Pullback by a particle permutation on Gaussian `L²`. -/
def gaussianPermutationL2 {n : ℕ} (σ : ParticlePermutation n) :
    Lp ℂ 2 (complexGaussianMeasure n) →ₗᵢ[ℂ]
      Lp ℂ 2 (complexGaussianMeasure n) :=
  Lp.compMeasurePreservingₗᵢ ℂ (permute σ)
    (gaussian_measurePreserving_permute σ)

/-- Pullback by a particle permutation on Ginibre `L²`. -/
def ginibrePermutationL2 {n : ℕ} (σ : ParticlePermutation n) :
    Lp ℂ 2 (ginibreMeasure n) →ₗᵢ[ℂ] Lp ℂ 2 (ginibreMeasure n) :=
  Lp.compMeasurePreservingₗᵢ ℂ (permute σ)
    (ginibre_measurePreserving_permute σ)

/-- The AE-symmetric subspace of Gaussian `L²`. -/
def gaussianSymmetricL2 (n : ℕ) :
    Submodule ℂ (Lp ℂ 2 (complexGaussianMeasure n)) :=
  { carrier := {u | ∀ σ : ParticlePermutation n,
      gaussianPermutationL2 σ u = u}
    zero_mem' := by simp
    add_mem' := by
      intro u v hu hv σ
      simp [map_add, hu σ, hv σ]
    smul_mem' := by
      intro c u hu σ
      simp [map_smul, hu σ] }

/-- The AE-alternating subspace of Gaussian `L²`. -/
def gaussianAlternatingL2 (n : ℕ) :
    Submodule ℂ (Lp ℂ 2 (complexGaussianMeasure n)) :=
  { carrier := {u | ∀ σ : ParticlePermutation n,
      gaussianPermutationL2 σ u = permutationSign σ • u}
    zero_mem' := by simp
    add_mem' := by
      intro u v hu hv σ
      simp [map_add, hu σ, hv σ, smul_add]
    smul_mem' := by
      intro c u hu σ
      rw [map_smul, hu σ]
      simp [smul_smul, mul_comm] }

/-- The AE-symmetric subspace of Ginibre `L²`. -/
def ginibreSymmetricL2 (n : ℕ) :
    Submodule ℂ (Lp ℂ 2 (ginibreMeasure n)) :=
  { carrier := {u | ∀ σ : ParticlePermutation n,
      ginibrePermutationL2 σ u = u}
    zero_mem' := by simp
    add_mem' := by
      intro u v hu hv σ
      simp [map_add, hu σ, hv σ]
    smul_mem' := by
      intro c u hu σ
      simp [map_smul, hu σ] }

/-- The AE-alternating subspace of Ginibre `L²`. -/
def ginibreAlternatingL2 (n : ℕ) :
    Submodule ℂ (Lp ℂ 2 (ginibreMeasure n)) :=
  { carrier := {u | ∀ σ : ParticlePermutation n,
      ginibrePermutationL2 σ u = permutationSign σ • u}
    zero_mem' := by simp
    add_mem' := by
      intro u v hu hv σ
      simp [map_add, hu σ, hv σ, smul_add]
    smul_mem' := by
      intro c u hu σ
      rw [map_smul, hu σ]
      simp [smul_smul, mul_comm] }

theorem isClosed_gaussianSymmetricL2 (n : ℕ) :
    IsClosed (gaussianSymmetricL2 n :
      Set (Lp ℂ 2 (complexGaussianMeasure n))) := by
  change IsClosed {u | ∀ σ : ParticlePermutation n,
    gaussianPermutationL2 σ u = u}
  rw [show {u | ∀ σ : ParticlePermutation n,
      gaussianPermutationL2 σ u = u} =
      ⋂ σ, {u | gaussianPermutationL2 σ u = u} by ext; simp]
  exact isClosed_iInter fun σ ↦ isClosed_eq
    (gaussianPermutationL2 σ).continuous continuous_id

theorem isClosed_gaussianAlternatingL2 (n : ℕ) :
    IsClosed (gaussianAlternatingL2 n :
      Set (Lp ℂ 2 (complexGaussianMeasure n))) := by
  change IsClosed {u | ∀ σ : ParticlePermutation n,
    gaussianPermutationL2 σ u = permutationSign σ • u}
  rw [show {u | ∀ σ : ParticlePermutation n,
      gaussianPermutationL2 σ u = permutationSign σ • u} =
      ⋂ σ, {u | gaussianPermutationL2 σ u = permutationSign σ • u} by
        ext; simp]
  exact isClosed_iInter fun σ ↦ isClosed_eq
    (gaussianPermutationL2 σ).continuous (continuous_const_smul _)

theorem isClosed_ginibreSymmetricL2 (n : ℕ) :
    IsClosed (ginibreSymmetricL2 n : Set (Lp ℂ 2 (ginibreMeasure n))) := by
  change IsClosed {u | ∀ σ : ParticlePermutation n,
    ginibrePermutationL2 σ u = u}
  rw [show {u | ∀ σ : ParticlePermutation n,
      ginibrePermutationL2 σ u = u} =
      ⋂ σ, {u | ginibrePermutationL2 σ u = u} by ext; simp]
  exact isClosed_iInter fun σ ↦ isClosed_eq
    (ginibrePermutationL2 σ).continuous continuous_id

theorem isClosed_ginibreAlternatingL2 (n : ℕ) :
    IsClosed (ginibreAlternatingL2 n : Set (Lp ℂ 2 (ginibreMeasure n))) := by
  change IsClosed {u | ∀ σ : ParticlePermutation n,
    ginibrePermutationL2 σ u = permutationSign σ • u}
  rw [show {u | ∀ σ : ParticlePermutation n,
      ginibrePermutationL2 σ u = permutationSign σ • u} =
      ⋂ σ, {u | ginibrePermutationL2 σ u = permutationSign σ • u} by
        ext; simp]
  exact isClosed_iInter fun σ ↦ isClosed_eq
    (ginibrePermutationL2 σ).continuous (continuous_const_smul _)

end

end GinibrePoincare
