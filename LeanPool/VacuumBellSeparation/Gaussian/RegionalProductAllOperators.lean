/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianRegionalVNAProduct
public import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart

/-!
# Regional Gaussian factorization for all bounded operators

The actual effects in a norm-closed star algebra linearly span that algebra.
Applying this proved C-star fact twice promotes the regional VNA effect
identity to the full product-state identity on all bounded local operators.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open Matrix

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem mem_span_effects_of_mem_closed_starSubalgebra
    (S : StarSubalgebra ℂ (E →L[ℂ] E)) (hS : IsClosed (S : Set (E →L[ℂ] E)))
    {A : E →L[ℂ] E} (hA : A ∈ S) :
    A ∈ Submodule.span ℂ {B : E →L[ℂ] E | B ∈ S ∧ 0 ≤ B ∧ B ≤ 1} := by
  let : IsClosed (S : Set (E →L[ℂ] E)) := hS
  let K := Submodule.span ℂ {B : E →L[ℂ] E | B ∈ S ∧ 0 ≤ B ∧ B ≤ 1}
  suffices ∀ x : S, (x : E →L[ℂ] E) ∈ K from this ⟨A, hA⟩
  intro x
  have hx : x ∈ Submodule.span ℂ ({y : S | 0 ≤ y} ∩ Metric.closedBall 0 1) := by
    rw [CStarAlgebra.span_nonneg_inter_unitClosedBall]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    have hy0 : 0 ≤ (y : E →L[ℂ] E) := hy.1
    have hy1 : y ≤ (1 : S) := by
      apply (CStarAlgebra.norm_le_one_iff_of_nonneg y hy.1).mp
      simpa only [Metric.mem_closedBall, dist_zero_right] using hy.2
    exact Submodule.subset_span ⟨y.2, hy0, hy1⟩
  | zero => exact K.zero_mem
  | add y z hy hz ihy ihz => exact K.add_mem ihy ihz
  | smul c y hy ih => exact K.smul_mem c ih

theorem densityExpectation_product_of_vna_effects
    (b : HilbertBasis ι ℂ E) {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass ρ)
    (S T : VonNeumannAlgebra E)
    (hfactor : ∀ A ∈ S, 0 ≤ A → A ≤ 1 → ∀ B ∈ T, 0 ≤ B → B ≤ 1 →
      densityExpectation b ρ (A * B) = densityExpectation b ρ A * densityExpectation b ρ B)
    {A B : E →L[ℂ] E} (hA : A ∈ S) (hB : B ∈ T) :
    densityExpectation b ρ (A * B) = densityExpectation b ρ A * densityExpectation b ρ B := by
  apply linearFunctional_factorization_span (densityExpectationCLM b hρ).toLinearMap
    {A | A ∈ S ∧ 0 ≤ A ∧ A ≤ 1} {B | B ∈ T ∧ 0 ≤ B ∧ B ≤ 1}
    (fun A hA B hB => hfactor A hA.1 hA.2.1 hA.2.2 B hB.1 hB.2.1 hB.2.2)
    (mem_span_effects_of_mem_closed_starSubalgebra S.toStarSubalgebra
      (vonNeumannAlgebra_isClosed S) hA)
    (mem_span_effects_of_mem_closed_starSubalgebra T.toStarSubalgebra
      (vonNeumannAlgebra_isClosed T) hB)

/-- Genuine product-state factorization on the full two regional algebras. -/
theorem gaussianPhysical_regional_vna_product {m : ℕ}
    {ρ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hρ : IsPositiveTraceClass ρ)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hV : V.IsHermitian) (hG : HasGaussianPhysicalCharacteristic ρ V)
    (L R : Submodule ℝ (Fin m × Fin 2 → ℝ))
    (hΩ : ∀ x ∈ L, ∀ y ∈ R, x ⬝ᵥ (modeSymplecticForm *ᵥ y) = 0)
    (hcov : ∀ x ∈ L, ∀ y ∈ R, x ⬝ᵥ (V *ᵥ y) = 0)
    {A B : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : A ∈ generatedVNA (regionalWeylGenerators L))
    (hB : B ∈ generatedVNA (regionalWeylGenerators R)) :
    densityExpectation (multiModeNumberBasis m) ρ (A * B) =
      densityExpectation (multiModeNumberBasis m) ρ A *
        densityExpectation (multiModeNumberBasis m) ρ B := by
  exact densityExpectation_product_of_vna_effects (multiModeNumberBasis m) hρ
    (generatedVNA (regionalWeylGenerators L)) (generatedVNA (regionalWeylGenerators R))
    (fun A hA hA0 hA1 B hB hB0 hB1 =>
      gaussianPhysical_regional_vna_effect_product hρ hV hG L R hΩ hcov
        hA hA0 hA1 hB hB0 hB1) hA hB

end VacuumBellSeparation.Gaussian
