/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FiniteSourcePairCoordinates
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianProductReference
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianFaithfulRenyiComparison

/-!
# Actual Gaussian density and product reference for two physical source systems

The record below packages conclusions of the construction, rather than an
assumed representation theorem. Its existence is proved from bounded spatial
localization, disjoint regions and the literal canonical source conditions.
The same map handles every bounded observable in the joint physical algebra.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian
open scoped Matrix
open scoped InnerProductSpace

variable {m : ℝ} (hm : 0 < m) {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (V : FreeFieldVacuum m H) (S T : Submodule ℝ TimeZeroSource)

/-- A Gaussian oscillator model of the two finite local source algebras, with their joint density
and the product reference on one space. -/
structure FiniteGaussianPairModel where
  /-- Number of canonical oscillator modes in the joint source space. -/
  modes : ℕ
  /-- Canonical field and momentum basis for the span of both source spaces. -/
  basis : Module.Basis (Fin modes × Fin 2) ℝ (FiniteSourceSpace hm (S ⊔ T))
  /-- The joint Gaussian density on the oscillator space. -/
  density : MultiModeOscillatorSpace modes →L[ℂ] MultiModeOscillatorSpace modes
  /-- The product of the two regional Gaussian densities in the same oscillator representation. -/
  reference : MultiModeOscillatorSpace modes →L[ℂ] MultiModeOscillatorSpace modes
  /-- Representation of the original local operators on the joint oscillator space. -/
  toOperator : (H →L[ℂ] H) →
    (MultiModeOscillatorSpace modes →L[ℂ] MultiModeOscillatorSpace modes)
  faithful_density : IsFaithfulDensity density
  faithful_reference : IsFaithfulDensity reference
  symplectic : finiteSourceSymplecticMatrix hm (S ⊔ T) basis = modeSymplecticForm
  characteristic : HasGaussianPhysicalCharacteristic density
    (finiteSourceCovarianceMatrix hm (S ⊔ T) basis)
  complementary : IsCompl (finiteSourceLabelSubspace hm (S ⊔ T) basis S)
    (finiteSourceLabelSubspace hm (S ⊔ T) basis T)
  reference_characteristic : HasGaussianPhysicalCharacteristic reference
    (labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hm (S ⊔ T) basis)
      (finiteSourceLabelSubspace hm (S ⊔ T) basis S)
      (finiteSourceLabelSubspace hm (S ⊔ T) basis T) complementary)
  map_one : toOperator 1 = 1
  map_star : ∀ A, toOperator (star A) = star (toOperator A)
  map_nonneg : ∀ A, 0 ≤ A → 0 ≤ toOperator A
  map_le_one : ∀ A, A ≤ 1 → toOperator A ≤ 1
  map_norm_le : ∀ A, ‖toOperator A‖ ≤ ‖A‖
  map_mul : ∀ A ∈ canonicalSourceAlgebra V hm (S ⊔ T),
    ∀ B ∈ canonicalSourceAlgebra V hm (S ⊔ T),
      toOperator (A * B) = toOperator A * toOperator B
  vacuum_expectation : ∀ A ∈ canonicalSourceAlgebra V hm (S ⊔ T),
    ⟪V.vacuum, A V.vacuum⟫_ℂ =
      densityExpectation (multiModeNumberBasis modes) density (toOperator A)
  left_membership : ∀ A ∈ canonicalSourceAlgebra V hm S,
    toOperator A ∈ generatedVNA (regionalWeylGenerators (finiteSourceLabelSubspace hm
      (S ⊔ T) basis S))
  right_membership : ∀ B ∈ canonicalSourceAlgebra V hm T,
    toOperator B ∈ generatedVNA (regionalWeylGenerators (finiteSourceLabelSubspace hm
      (S ⊔ T) basis T))
  left_marginal : ∀ A ∈ canonicalSourceAlgebra V hm S,
    densityExpectation (multiModeNumberBasis modes) reference (toOperator A) =
      ⟪V.vacuum, A V.vacuum⟫_ℂ
  right_marginal : ∀ B ∈ canonicalSourceAlgebra V hm T,
    densityExpectation (multiModeNumberBasis modes) reference (toOperator B) =
      ⟪V.vacuum, B V.vacuum⟫_ℂ
  product_expectation : ∀ A ∈ canonicalSourceAlgebra V hm S,
    ∀ B ∈ canonicalSourceAlgebra V hm T,
      densityExpectation (multiModeNumberBasis modes) reference (toOperator (A * B)) =
        ⟪V.vacuum, A V.vacuum⟫_ℂ * ⟪V.vacuum, B V.vacuum⟫_ℂ

theorem regionalWeylGenerators_eq_image {n : ℕ} (L : Submodule ℝ (Fin n × Fin 2 → ℝ)) :
    regionalWeylGenerators L = physicalOscillatorWeyl '' (L : Set (Fin n × Fin 2 → ℝ)) := by
  ext A
  constructor
  · rintro ⟨x, hx, hA⟩
    exact ⟨x, hx, hA.symm⟩
  · rintro ⟨x, hx, hA⟩
    exact ⟨x, hx, hA.symm⟩

/-- No Gaussian representation or reference existence is assumed here. -/
theorem nonempty_finiteGaussianPairModel
    {U W : Set (EuclideanSpace ℝ (Fin 3))}
    (hU : Bornology.IsBounded U) (hW : Bornology.IsBounded W) (hUW : Disjoint U W)
    (hS : IsCanonicalSourceSystem U S) (hT : IsCanonicalSourceSystem W T) :
    Nonempty (FiniteGaussianPairModel hm V S T) := by
  classical
  have hR := canonicalSourcePair_sup_isCanonical hUW hS hT
  let : FiniteDimensional ℝ ↥(S ⊔ T) := hR.1
  obtain ⟨n, b, ρ, Φ, hρ, hΩ, hGρ, hΦ1, hΦstar, hΦW, hΦlocal,
    hΦ0, hΦle, hΦnorm, hΦmul, hΦvac⟩ :=
    exists_finite_physical_gaussian_observable_model hm (S ⊔ T) V hR.2.1 (hU.union hW) hR.2.2
  let L := finiteSourceLabelSubspace hm (S ⊔ T) b S
  let M := finiteSourceLabelSubspace hm (S ⊔ T) b T
  have hLM : IsCompl L M := finiteSourceLabelSubspace_isCompl hm (S ⊔ T) b rfl
    (canonicalSourcePair_disjoint hUW hS hT)
  have hcross : ∀ x ∈ L, ∀ y ∈ M, x ⬝ᵥ (modeSymplecticForm *ᵥ y) = 0 := by
    intro x hx y hy
    exact finiteSourceLabelSubspace_symplectic_cross hm (S ⊔ T) b hΩ S T
      (fun u hu v hv => canonicalSourcePair_cross hUW hS hT hu hv) hx hy
  have hQ := actual_faithful_gaussian_quantum_posDef hρ
    (finiteSourceCovarianceMatrix_isHermitian hm (S ⊔ T) b) hGρ
  obtain ⟨σ, hσ, hGσ, hσL, hσM, hσprod⟩ :=
    exists_faithful_gaussian_product_reference hρ.isPositiveTraceClass hGρ hQ L M hLM hcross
  have hleft : ∀ A ∈ canonicalSourceAlgebra V hm S,
      Φ A ∈ generatedVNA (regionalWeylGenerators L) := by
    intro A hA
    rw [regionalWeylGenerators_eq_image]
    apply hΦlocal (L : Set (Fin n × Fin 2 → ℝ))
    rwa [generatedVNA_finiteSourceLabelSubspace hm (S ⊔ T) b V S le_sup_left]
  have hright : ∀ B ∈ canonicalSourceAlgebra V hm T,
      Φ B ∈ generatedVNA (regionalWeylGenerators M) := by
    intro B hB
    rw [regionalWeylGenerators_eq_image]
    apply hΦlocal (M : Set (Fin n × Fin 2 → ℝ))
    rwa [generatedVNA_finiteSourceLabelSubspace hm (S ⊔ T) b V T le_sup_right]
  have hSL := canonicalSourceAlgebra_mono V hm (show S ≤ S ⊔ T from le_sup_left)
  have hTR := canonicalSourceAlgebra_mono V hm (show T ≤ S ⊔ T from le_sup_right)
  refine ⟨{
    modes := n, basis := b, density := ρ, reference := σ, toOperator := Φ
    faithful_density := hρ, faithful_reference := hσ, symplectic := hΩ
    characteristic := hGρ, complementary := hLM, reference_characteristic := hGσ
    map_one := hΦ1, map_star := hΦstar, map_nonneg := hΦ0, map_le_one := hΦle
    map_norm_le := hΦnorm, map_mul := hΦmul, vacuum_expectation := hΦvac
    left_membership := hleft, right_membership := hright
    left_marginal := ?_, right_marginal := ?_, product_expectation := ?_ }⟩
  · intro A hA
    rw [hσL _ (hleft A hA), ← hΦvac A (hSL hA)]
  · intro B hB
    rw [hσM _ (hright B hB), ← hΦvac B (hTR hB)]
  · intro A hA B hB
    rw [hΦmul A (hSL hA) B (hTR hB), hσprod _ (hleft A hA) _ (hright B hB),
      ← hΦvac A (hSL hA), ← hΦvac B (hTR hB)]

end VacuumBellSeparation
