/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ComplementaryLabelCovariance
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianRegionalMarginal
public import LeanPool.VacuumBellSeparation.Gaussian.FixedGaussianExistence

/-!
# Actual faithful Gaussian product reference with the original marginals

Complementary symplectically orthogonal real label subspaces determine
literal projection matrices and a strictly quantum-positive decorrelated
covariance. The proved fixed-representation Gaussian existence theorem
constructs its actual faithful density. On the full regional von Neumann
algebras, its marginals agree with the original density and its joint
expectation is their product. No reference-state existence or independence
is inserted as a structure field or a hypothesis.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder

variable {m : ℕ}

/-- A genuine product reference on the original canonical oscillator
Hilbert space, with both true regional marginals preserved. -/
theorem exists_faithful_gaussian_product_reference
    {ρ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hρ : IsPositiveTraceClass ρ)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hGρ : HasGaussianPhysicalCharacteristic ρ V)
    (hQ : (quantumCovariance V modeSymplecticForm).PosDef)
    (L R : Submodule ℝ (Fin m × Fin 2 → ℝ)) (h : IsCompl L R)
    (hΩ : ∀ x ∈ L, ∀ y ∈ R, x ⬝ᵥ (modeSymplecticForm *ᵥ y) = 0) :
    ∃ σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m,
      IsFaithfulDensity σ ∧
      HasGaussianPhysicalCharacteristic σ (labelDecorrelatedCovariance V L R h) ∧
      (∀ A ∈ generatedVNA (regionalWeylGenerators L),
        densityExpectation (multiModeNumberBasis m) σ A =
          densityExpectation (multiModeNumberBasis m) ρ A) ∧
      (∀ B ∈ generatedVNA (regionalWeylGenerators R),
        densityExpectation (multiModeNumberBasis m) σ B =
          densityExpectation (multiModeNumberBasis m) ρ B) ∧
      (∀ A ∈ generatedVNA (regionalWeylGenerators L),
        ∀ B ∈ generatedVNA (regionalWeylGenerators R),
          densityExpectation (multiModeNumberBasis m) σ (A * B) =
            densityExpectation (multiModeNumberBasis m) ρ A *
              densityExpectation (multiModeNumberBasis m) ρ B) := by
  let W := labelDecorrelatedCovariance V L R h
  have hWQ : (quantumCovariance W modeSymplecticForm).PosDef :=
    labelDecorrelatedCovariance_quantum_posDef hQ transpose_modeSymplecticForm L R h hΩ
  have hW : W.PosDef := real_posDef_of_quantum_posDef hWQ
  obtain ⟨σ, hσ, hGσ⟩ := exists_fixed_faithful_gaussian_physical_density W hW hWQ
  have hleft : ∀ A ∈ generatedVNA (regionalWeylGenerators L),
      densityExpectation (multiModeNumberBasis m) σ A =
        densityExpectation (multiModeNumberBasis m) ρ A := by
    intro A hA
    exact gaussianPhysical_regional_vna_marginal hσ.isPositiveTraceClass hρ hGσ hGρ L
      (fun x hx => labelDecorrelatedCovariance_left_restriction V L R h hx hx) hA
  have hright : ∀ B ∈ generatedVNA (regionalWeylGenerators R),
      densityExpectation (multiModeNumberBasis m) σ B =
        densityExpectation (multiModeNumberBasis m) ρ B := by
    intro B hB
    exact gaussianPhysical_regional_vna_marginal hσ.isPositiveTraceClass hρ hGσ hGρ R
      (fun y hy => labelDecorrelatedCovariance_right_restriction V L R h hy hy) hB
  refine ⟨σ, hσ, hGσ, hleft, hright, ?_⟩
  intro A hA B hB
  rw [gaussianPhysical_regional_vna_product hσ.isPositiveTraceClass hW.isHermitian hGσ
    L R hΩ (fun x hx y hy => labelDecorrelatedCovariance_cross V L R h hx hy) hA hB,
    hleft A hA, hright B hB]

theorem covariance_sub_decorrelated {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix ι ι ℝ) {P Q : Matrix ι ι ℝ} (hPQ : P + Q = 1) :
    V - decorrelatedCovariance V P Q = Pᵀ * V * Q + Qᵀ * V * P := by
  have hV : V = (P + Q)ᵀ * V * (P + Q) := by
    rw [hPQ, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  calc
    V - decorrelatedCovariance V P Q =
        (P + Q)ᵀ * V * (P + Q) - (Pᵀ * V * P + Qᵀ * V * Q) := by
      rw [← hV]
      rfl
    _ = _ := by rw [Matrix.transpose_add]; noncomm_ring

theorem covariance_sub_labelDecorrelated {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix ι ι ℝ) (L R : Submodule ℝ (ι → ℝ)) (h : IsCompl L R) :
    V - labelDecorrelatedCovariance V L R h =
      (complementaryLabelProjection L R h)ᵀ * V * complementaryLabelProjection R L h.symm +
        (complementaryLabelProjection R L h.symm)ᵀ * V * complementaryLabelProjection L R h :=
  covariance_sub_decorrelated V (complementaryLabelProjection_add L R h)

end VacuumBellSeparation.Gaussian
