/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.RegionalProductAllOperators

/-!
# Equal Gaussian covariance restrictions give equal regional marginals

Equality of the actual Gaussian characteristic on a real label subspace
extends through its Weyl span, norm closure, and genuine bounded Kaplansky
nets. Thus both density expectations agree on every bounded operator in
the generated regional algebra, not only on Weyl generators.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open Matrix Filter Topology

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem densityExpectations_eq_on_generatedVNA_effects
    (b : HilbertBasis ι ℂ E) {ρ σ : E →L[ℂ] E}
    (hρ : IsPositiveTraceClass ρ) (hσ : IsPositiveTraceClass σ)
    (S : StarSubalgebra ℂ (E →L[ℂ] E)) (hS : IsClosed (S : Set (E →L[ℂ] E)))
    (hagree : ∀ A ∈ S, densityExpectation b ρ A = densityExpectation b σ A)
    {A : E →L[ℂ] E} (hA : A ∈ generatedVNA (S : Set (E →L[ℂ] E)))
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) :
    densityExpectation b ρ A = densityExpectation b σ A := by
  classical
  let : IsClosed (S : Set (E →L[ℂ] E)) := hS
  obtain ⟨As, hAs, hlim⟩ := exists_effect_strong_approximation S
    (fun f A hA => cfc_mem (𝕜' := ℂ) (s := S) f hA) hA hA0 hA1
  have hb : ∀ᶠ i : Finset E × ℕ in atTop, ‖As i‖ ≤ (1 : ℝ) := Eventually.of_forall fun i =>
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hAs i).2.1).mpr (hAs i).2.2
  have hρlim := tendsto_densityExpectation_of_strong b hρ
    (α := Finset E × ℕ) (l := atTop) (As := As) (A := A) hlim hb
  have hσlim := tendsto_densityExpectation_of_strong b hσ
    (α := Finset E × ℕ) (l := atTop) (As := As) (A := A) hlim hb
  exact tendsto_nhds_unique hρlim (hσlim.congr'
    (Eventually.of_forall fun i => (hagree _ (hAs i).1).symm))

theorem densityExpectations_eq_on_generatedVNA
    (b : HilbertBasis ι ℂ E) {ρ σ : E →L[ℂ] E}
    (hρ : IsPositiveTraceClass ρ) (hσ : IsPositiveTraceClass σ)
    (S : StarSubalgebra ℂ (E →L[ℂ] E)) (hS : IsClosed (S : Set (E →L[ℂ] E)))
    (hagree : ∀ A ∈ S, densityExpectation b ρ A = densityExpectation b σ A)
    {A : E →L[ℂ] E} (hA : A ∈ generatedVNA (S : Set (E →L[ℂ] E))) :
    densityExpectation b ρ A = densityExpectation b σ A := by
  let M := generatedVNA (S : Set (E →L[ℂ] E))
  apply LinearMap.eqOn_span (f := (densityExpectationCLM b hρ).toLinearMap)
    (g := (densityExpectationCLM b hσ).toLinearMap)
    (s := {A | A ∈ M ∧ 0 ≤ A ∧ A ≤ 1}) ?_
    (mem_span_effects_of_mem_closed_starSubalgebra M.toStarSubalgebra
      (vonNeumannAlgebra_isClosed M) hA)
  intro B hB
  exact densityExpectations_eq_on_generatedVNA_effects b hρ hσ S hS hagree hB.1 hB.2.1 hB.2.2

theorem gaussianPhysical_regional_cstar_marginal {m : ℕ}
    {ρ σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hρ : IsPositiveTraceClass ρ) (hσ : IsPositiveTraceClass σ)
    {V W : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hGρ : HasGaussianPhysicalCharacteristic ρ V)
    (hGσ : HasGaussianPhysicalCharacteristic σ W)
    (L : Submodule ℝ (Fin m × Fin 2 → ℝ))
    (hcov : ∀ x ∈ L, x ⬝ᵥ (V *ᵥ x) = x ⬝ᵥ (W *ᵥ x))
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : A ∈ regionalWeylCStarAlgebra L) :
    densityExpectation (multiModeNumberBasis m) ρ A =
      densityExpectation (multiModeNumberBasis m) σ A := by
  have hpoly : ∀ B ∈ regionalWeylPolynomialAlgebra L,
      densityExpectation (multiModeNumberBasis m) ρ B =
        densityExpectation (multiModeNumberBasis m) σ B := by
    intro B hB
    apply LinearMap.eqOn_span
      (f := (densityExpectationCLM (multiModeNumberBasis m) hρ).toLinearMap)
      (g := (densityExpectationCLM (multiModeNumberBasis m) hσ).toLinearMap) ?_ hB
    rintro _ ⟨x, hx, rfl⟩
    change densityExpectation (multiModeNumberBasis m) ρ (physicalOscillatorWeyl x) =
      densityExpectation (multiModeNumberBasis m) σ (physicalOscillatorWeyl x)
    rw [gaussianPhysical_physicalOscillatorWeyl hGρ,
      gaussianPhysical_physicalOscillatorWeyl hGσ, hcov x hx]
  have hsubset : (regionalWeylPolynomialAlgebra L : Set _) ⊆
      {B | densityExpectation (multiModeNumberBasis m) ρ B =
        densityExpectation (multiModeNumberBasis m) σ B} :=
    fun _ hB => hpoly _ hB
  exact (closure_minimal hsubset
    (isClosed_eq (densityExpectationCLM (multiModeNumberBasis m) hρ).continuous
      (densityExpectationCLM (multiModeNumberBasis m) hσ).continuous)) hA

/-- Every bounded regional observable has the same actual marginal. -/
theorem gaussianPhysical_regional_vna_marginal {m : ℕ}
    {ρ σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hρ : IsPositiveTraceClass ρ) (hσ : IsPositiveTraceClass σ)
    {V W : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hGρ : HasGaussianPhysicalCharacteristic ρ V)
    (hGσ : HasGaussianPhysicalCharacteristic σ W)
    (L : Submodule ℝ (Fin m × Fin 2 → ℝ))
    (hcov : ∀ x ∈ L, x ⬝ᵥ (V *ᵥ x) = x ⬝ᵥ (W *ᵥ x))
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : A ∈ generatedVNA (regionalWeylGenerators L)) :
    densityExpectation (multiModeNumberBasis m) ρ A =
      densityExpectation (multiModeNumberBasis m) σ A := by
  apply densityExpectations_eq_on_generatedVNA (multiModeNumberBasis m) hρ hσ
    (regionalWeylCStarAlgebra L) (regionalWeylPolynomialAlgebra L).isClosed_topologicalClosure
    (fun B hB => gaussianPhysical_regional_cstar_marginal hρ hσ hGρ hGσ L hcov hB)
  simpa only [generatedVNA_regionalWeylCStarAlgebra] using hA

end VacuumBellSeparation.Gaussian
