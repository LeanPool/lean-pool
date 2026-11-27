/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.DensityProductExtension
public import LeanPool.VacuumBellSeparation.Bell.KaplanskyEffects
public import LeanPool.VacuumBellSeparation.Bell.DirectedAlgebraUnion
public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroAlgebra

/-!
# Genuine density factorization on generated von Neumann algebra effects

Norm-closed star algebras have the proved real-CFC stability required by
Kaplansky approximation. Two actual effect nets and bounded strong density
continuity extend an already established product expectation identity.
No normality, tensor product, or independence field is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open Filter Topology

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem generatedVNA_closed_star_adjoin (X : Set (E →L[ℂ] E)) :
    generatedVNA ((StarAlgebra.adjoin ℂ X).topologicalClosure : Set (E →L[ℂ] E)) =
      generatedVNA X := by
  apply le_antisymm
  · apply generatedVNA_le_of_subset
    exact StarSubalgebra.topologicalClosure_minimal
      (s := StarAlgebra.adjoin ℂ X) (t := (generatedVNA X).toStarSubalgebra)
      (StarAlgebra.adjoin_le (subset_generatedVNA X))
      (vonNeumannAlgebra_isClosed (generatedVNA X))
  · apply generatedVNA_mono
    intro A hA
    exact (StarAlgebra.adjoin ℂ X).le_topologicalClosure
      (StarAlgebra.subset_adjoin ℂ X hA)

theorem densityExpectation_product_generatedVNA_effects
    (b : HilbertBasis ι ℂ E) {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass ρ)
    (S T : StarSubalgebra ℂ (E →L[ℂ] E))
    (hS : IsClosed (S : Set (E →L[ℂ] E)))
    (hT : IsClosed (T : Set (E →L[ℂ] E)))
    (hfactor : ∀ A ∈ S, ∀ B ∈ T, densityExpectation b ρ (A * B) =
      densityExpectation b ρ A * densityExpectation b ρ B)
    {A B : E →L[ℂ] E}
    (hA : A ∈ generatedVNA (S : Set (E →L[ℂ] E))) (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hB : B ∈ generatedVNA (T : Set (E →L[ℂ] E))) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    densityExpectation b ρ (A * B) = densityExpectation b ρ A * densityExpectation b ρ B := by
  classical
  let : IsClosed (S : Set (E →L[ℂ] E)) := hS
  let : IsClosed (T : Set (E →L[ℂ] E)) := hT
  obtain ⟨As, hAs, hlimA⟩ := exists_effect_strong_approximation S
    (fun f A hA => cfc_mem (𝕜' := ℂ) (s := S) f hA) hA hA0 hA1
  obtain ⟨Bs, hBs, hlimB⟩ := exists_effect_strong_approximation T
    (fun f B hB => cfc_mem (𝕜' := ℂ) (s := T) f hB) hB hB0 hB1
  have hbA : ∀ᶠ i in atTop, ‖As i‖ ≤ (1 : ℝ) := Eventually.of_forall fun i =>
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hAs i).2.1).mpr (hAs i).2.2
  have hbB : ∀ᶠ i in atTop, ‖Bs i‖ ≤ (1 : ℝ) := Eventually.of_forall fun i =>
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hBs i).2.1).mpr (hBs i).2.2
  have hfixed (j : Finset E × ℕ) : densityExpectation b ρ (A * Bs j) =
      densityExpectation b ρ A * densityExpectation b ρ (Bs j) :=
    densityExpectation_factorization_of_strong_left b hρ hlimA hbA
      (Eventually.of_forall fun i => hfactor _ (hAs i).1 _ (hBs j).1)
  exact densityExpectation_factorization_of_strong_right b hρ hlimB hbB
    (Eventually.of_forall hfixed)

end VacuumBellSeparation.Gaussian
