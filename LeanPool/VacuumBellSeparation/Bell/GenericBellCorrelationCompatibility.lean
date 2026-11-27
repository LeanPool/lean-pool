/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.GenericBellCorrelationSpecifications
public import LeanPool.VacuumBellSeparation.Bell.LocalState
public import LeanPool.VacuumBellSeparation.Bell.TsirelsonBound
public import LeanPool.VacuumBellSeparation.Bell.KaplanskyContractions

/-!
Literal quantity and observable bridges for HC00. The state extension used for
bounds is an actual positive unital extension; no normal ambient extension is
assumed or asserted. No density or infinite-type result is used here.
-/

@[expose] public section

universe u
namespace VacuumBellSeparation.Bipartite.HC00

open scoped ComplexOrder InnerProductSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every generator belongs to its generated von Neumann algebra.  This local
proof keeps the generic Bell bridge independent of the free-field continuity API. -/
theorem subset_generatedVNA_for_bell (S : Set (H →L[ℂ] H)) : S ⊆ generatedVNA S := by
  intro T hT
  change T ∈ (commutantOf S).commutant
  rw [VonNeumannAlgebra.mem_commutant_iff]
  intro B hB
  have hb := mem_commutantOf_iff.mp hB
  exact (Set.mem_centralizer_iff.mp hb T (Set.mem_union_left _ hT)).symm

/-- Bundling the four local observables in the joint algebra changes neither
its set of CHSH values nor its conditional real supremum. -/
theorem jointBellCorrelation_eq_localBellCorrelation (A B : VonNeumannAlgebra H)
    (φ : (jointAlgebra A B).toStarSubalgebra →ₚ[ℂ] ℂ)
    (hA : (A : Set (H →L[ℂ] H)) ⊆ (jointAlgebra A B).toStarSubalgebra)
    (hB : (B : Set (H →L[ℂ] H)) ⊆ (jointAlgebra A B).toStarSubalgebra) :
    jointBellCorrelation A B φ =
      localBellCorrelation (jointAlgebra A B).toStarSubalgebra φ A B hA hB := by
  unfold jointBellCorrelation jointBellValues localBellCorrelation
  apply congrArg sSup
  apply Set.ext
  intro r
  constructor
  · rintro ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁, hr⟩
    exact ⟨X₀, hX₀, X₁, hX₁, Y₀, hY₀, Y₁, hY₁, hr⟩
  · rintro ⟨X₀, hX₀, X₁, hX₁, Y₀, hY₀, Y₁, hY₁, hr⟩
    exact ⟨⟨X₀, hA hX₀.1⟩, ⟨X₁, hA hX₁.1⟩,
      ⟨Y₀, hB hY₀.1⟩, ⟨Y₁, hB hY₁.1⟩, hX₀, hX₁, hY₀, hY₁, hr⟩

theorem jointBellQuantityCompatibility_specification :
    JointBellQuantityCompatibilitySpecification (H := H) := by
  intro A B φ hA hB
  exact jointBellCorrelation_eq_localBellCorrelation A B φ hA hB

/-- The full order interval of self-adjoint observables, not just effects. -/
theorem mem_saContractions_iff_order (A : VonNeumannAlgebra H) (X : H →L[ℂ] H) :
    X ∈ saContractions A ↔ X ∈ A ∧ IsSelfAdjoint X ∧ -1 ≤ X ∧ X ≤ 1 := by
  constructor
  · rintro ⟨hX, hsa, hn⟩
    have hp := ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (isPositive_one_add_of_saContraction hsa hn)
    have hm := ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (isPositive_one_sub_of_saContraction hsa hn)
    exact ⟨hX, hsa, neg_le_iff_add_nonneg'.mpr hp, sub_nonneg.mp hm⟩
  · rintro ⟨hX, hsa, hlow, hupp⟩
    let E : H →L[ℂ] H := (1 / 2 : ℝ) • (1 + X)
    have hE : 0 ≤ E :=
      smul_nonneg (by norm_num) (neg_le_iff_add_nonneg'.mp hlow)
    have hE1 : E ≤ 1 := by
      apply sub_nonneg.mp
      have he : 1 - E = (1 / 2 : ℝ) • (1 - X) := by dsimp only [E]; module
      rw [he]
      exact smul_nonneg (by norm_num) (sub_nonneg.mpr hupp)
    have he : (2 : ℝ) • E - 1 = X := by dsimp only [E]; module
    have hn := (two_smul_effect_sub_one_contraction hE hE1).2
    exact ⟨hX, hsa, by simpa only [he] using hn⟩

theorem observableOrderCompatibility_specification :
    ObservableOrderCompatibilitySpecification (H := H) := by
  intro A X
  exact mem_saContractions_iff_order A X

/-- Every intrinsic joint state has the manuscript's bounds. Positivity gives
a general ambient state extension; its agreement on the joint algebra is all
that is used to transfer the existing literal Tsirelson theorem. -/
theorem jointBellCorrelation_bounds (A B : VonNeumannAlgebra H)
    (hcomm : Commuting A B) (φ : StateSpace (jointAlgebra A B)) :
    1 ≤ jointBellCorrelation A B φ.1 ∧
      jointBellCorrelation A B φ.1 ≤ Real.sqrt 2 := by
  obtain ⟨ψ, hψ1, hψ⟩ := φ.2
  have he : (fun T => ψ T) = (fun T => φ.1 T) := funext hψ
  have hA : (A : Set (H →L[ℂ] H)) ⊆ (jointAlgebra A B).toStarSubalgebra := by
    intro X hX
    exact subset_generatedVNA_for_bell _ (Set.mem_union_left _ hX)
  have hB : (B : Set (H →L[ℂ] H)) ⊆ (jointAlgebra A B).toStarSubalgebra := by
    intro Y hY
    exact subset_generatedVNA_for_bell _ (Set.mem_union_right _ hY)
  obtain ⟨ω, hω⟩ := exists_state_extension_vonNeumann (jointAlgebra A B) ψ hψ1
  have hb : jointBellCorrelation A B φ.1 = bellCorrelation ω A B := by
    calc
      jointBellCorrelation A B φ.1 = jointBellCorrelation A B ψ :=
        congrArg (jointBellCorrelation A B) he.symm
      _ = localBellCorrelation (jointAlgebra A B).toStarSubalgebra ψ A B hA hB :=
        jointBellCorrelation_eq_localBellCorrelation A B ψ hA hB
      _ = bellCorrelation ω A B :=
        localBellCorrelation_eq_extension (jointAlgebra A B).toStarSubalgebra
          ψ A B hA hB ω hω
  rw [hb]
  exact ⟨one_le_bellCorrelation ω A B, bellCorrelation_le_sqrt_two ω hcomm⟩

end VacuumBellSeparation.Bipartite.HC00
