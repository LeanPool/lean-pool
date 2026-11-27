/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CoherentTotality
public import LeanPool.VacuumBellSeparation.Weyl.Existence

/-!
# A genuine one-mode Weyl/coherent unitary realization

Normalized ℓ² coherent vectors have the existing Weyl RKHS kernel. The map
on RKHS point masses preserves inner products, extends to the completion,
and is surjective by coherent totality. This constructs the representation
bridge; no uniqueness-of-representation theorem is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open scoped ComplexConjugate

/-- The normalized coherent vector in the actual number-basis Hilbert space. -/
noncomputable def coherentVector (z : ℂ) : OscillatorSpace :=
  Complex.exp ((-(‖z‖ ^ 2 / 2) : ℝ) : ℂ) • exponentialVector z

theorem inner_coherentVector (z w : ℂ) :
    inner ℂ (coherentVector z) (coherentVector w) = weylKernel (id : ℂ → ℂ) z w := by
  rw [coherentVector, coherentVector, inner_smul_left, inner_smul_right,
    inner_exponentialVector, weylKernel_eq]
  simp only [id_eq, RCLike.inner_apply']
  ring

theorem coherentVector_dense_span :
    (Submodule.span ℂ (Set.range coherentVector)).topologicalClosure = ⊤ := by
  have hspan : Submodule.span ℂ (Set.range exponentialVector) ≤
      Submodule.span ℂ (Set.range coherentVector) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    change exponentialVector z ∈ Submodule.span ℂ (Set.range coherentVector)
    have hmem : coherentVector z ∈ Submodule.span ℂ (Set.range coherentVector) :=
      Submodule.subset_span ⟨z, rfl⟩
    have heq : (Complex.exp ((-(‖z‖ ^ 2 / 2) : ℝ) : ℂ))⁻¹ • coherentVector z =
        exponentialVector z := by
      rw [coherentVector, inv_smul_smul₀ (Complex.exp_ne_zero _)]
    rw [← heq]
    exact Submodule.smul_mem (Submodule.span ℂ (Set.range coherentVector)) _ hmem
  apply top_unique
  rw [← exponentialVector_dense_span]
  exact Submodule.topologicalClosure_mono hspan

/-- The map on the existing RKHS pre-Hilbert space. The second coordinate
of a kernel point mass is its scalar vector label. -/
noncomputable def coherentRealization₀ :
    RKHS.H₀ (weylRKHSKernel (id : ℂ → ℂ)) →ₗ[ℂ] OscillatorSpace :=
  Finsupp.linearCombination ℂ (fun p : ℂ × ℂ => p.2 • coherentVector p.1)

@[simp]
theorem coherentRealization₀_single (z v a : ℂ) :
    coherentRealization₀ (Finsupp.single (z, v) a) = a • (v • coherentVector z) := by
  simp [coherentRealization₀]

theorem inner_coherentRealization₀
    (f g : RKHS.H₀ (weylRKHSKernel (id : ℂ → ℂ))) :
    inner ℂ (coherentRealization₀ f) (coherentRealization₀ g) = inner ℂ f g := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, inner_zero_left]
  | add f₁ f₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]
  | single p a =>
    induction g using Finsupp.induction_linear with
    | zero => simp only [map_zero, inner_zero_right]
    | add g₁ g₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
    | single q b =>
      obtain ⟨z, v⟩ := p
      obtain ⟨w, u⟩ := q
      rw [coherentRealization₀_single, coherentRealization₀_single, inner_H₀_single]
      simp only [inner_smul_left, inner_smul_right, inner_coherentVector]
      ring

/-- Linear isometry for the coherent realization iso₀, of type `ℂ → ℂ)) →ₗᵢ[ℂ] OscillatorSpace`. -/
noncomputable def coherentRealizationIso₀ :
    RKHS.H₀ (weylRKHSKernel (id : ℂ → ℂ)) →ₗᵢ[ℂ] OscillatorSpace :=
  coherentRealization₀.isometryOfInner inner_coherentRealization₀

/-- The actual isometry from the completed Weyl representation to ℓ². -/
noncomputable def coherentRealization : WeylSpace (id : ℂ → ℂ) →ₗᵢ[ℂ] OscillatorSpace :=
  coherentRealizationIso₀.fromCompletion

theorem coherentRealization_weylVec (z : ℂ) :
    coherentRealization (weylVec (id : ℂ → ℂ) z) = coherentVector z := by
  rw [weylVec_def, coherentRealization, LinearIsometry.fromCompletion_apply_coe]
  change coherentRealization₀ (Finsupp.single (z, 1) 1) = coherentVector z
  simp

theorem coherentRealization_surjective : Function.Surjective coherentRealization := by
  have hclosed : IsClosed (Set.range coherentRealization) :=
    coherentRealization.isometry.isClosedEmbedding.isClosed_range
  have hspan : Submodule.span ℂ (Set.range coherentVector) ≤
      coherentRealization.toLinearMap.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    exact ⟨weylVec (id : ℂ → ℂ) z, coherentRealization_weylVec z⟩
  have hclosure := (Submodule.span ℂ (Set.range coherentVector)).topologicalClosure_minimal
    hspan hclosed
  rw [coherentVector_dense_span] at hclosure
  exact LinearMap.range_eq_top.mp (top_unique hclosure)

/-- The constructed one-mode Weyl/coherent unitary equivalence. -/
noncomputable def weylCoherentEquiv : WeylSpace (id : ℂ → ℂ) ≃ₗᵢ[ℂ] OscillatorSpace :=
  LinearIsometryEquiv.ofSurjective coherentRealization coherentRealization_surjective

theorem weylCoherentEquiv_weylVec (z : ℂ) :
    weylCoherentEquiv (weylVec (id : ℂ → ℂ) z) = coherentVector z :=
  coherentRealization_weylVec z

end VacuumBellSeparation.Gaussian
