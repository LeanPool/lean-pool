/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CanonicalSourceHull
public import LeanPool.VacuumBellSeparation.Gaussian.SkewMatrixNormalForm

/-!
# The actual covariance Hilbert space of a finite canonical source system

The carrier is the given subspace of smooth test pairs. Its norm is induced
by the physical one-particle map, and its commutation operator represents
the literal symplectic integral. Nondegeneracy constructs positive-frequency
orthonormal skew coordinates; no representation or normal-form data are
assumed as part of a source system.
-/

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace

namespace VacuumBellSeparation

/-- The mass determines the covariance norm on this copy of the actual sources. -/
def FiniteSourceSpace {m : ℝ} (_hm : 0 < m)
    (S : Submodule ℝ TimeZeroSource) : Type := S

variable {m : ℝ} (hm : 0 < m) (S : Submodule ℝ TimeZeroSource)

instance : AddCommGroup (FiniteSourceSpace hm S) := inferInstanceAs (AddCommGroup S)
instance : Module ℝ (FiniteSourceSpace hm S) := inferInstanceAs (Module ℝ S)

/-- Finite source map of type `FiniteSourceSpace hm S →ₗ[ℝ] Lp ℂ 2 (oneParticleMeasure m)`. -/
noncomputable def finiteSourceMap :
    FiniteSourceSpace hm S →ₗ[ℝ] Lp ℂ 2 (oneParticleMeasure m) :=
  (timeZeroLinear hm).comp S.subtype

theorem finiteSourceMap_injective : Function.Injective (finiteSourceMap hm S) :=
  (timeZeroLinear_injective hm).comp Subtype.val_injective

noncomputable instance : NormedAddCommGroup (FiniteSourceSpace hm S) :=
  NormedAddCommGroup.induced _ _ (finiteSourceMap hm S) (finiteSourceMap_injective hm S)

noncomputable instance : InnerProductSpace ℝ (FiniteSourceSpace hm S) :=
  InnerProductSpace.induced (finiteSourceMap hm S)

instance [FiniteDimensional ℝ S] : FiniteDimensional ℝ (FiniteSourceSpace hm S) :=
  inferInstanceAs (FiniteDimensional ℝ S)

noncomputable instance [FiniteDimensional ℝ S] : CompleteSpace (FiniteSourceSpace hm S) :=
  FiniteDimensional.completeSpace ℝ (FiniteSourceSpace hm S)

/-- Finite source isometry of type `FiniteSourceSpace hm S →ₗᵢ[ℝ] Lp ℂ 2 (oneParticleMeasure m)
where __`. -/
noncomputable def finiteSourceIsometry :
    FiniteSourceSpace hm S →ₗᵢ[ℝ] Lp ℂ 2 (oneParticleMeasure m) where
  __ := finiteSourceMap hm S
  norm_map' _ := rfl

theorem finiteSourceSpace_norm_sq (u : FiniteSourceSpace hm S) :
    ‖u‖ ^ 2 = timeZeroFourierCovariance m u.1 u.1 :=
  norm_timeZeroL2_sq hm u.1

theorem finiteSourceSpace_inner (u v : FiniteSourceSpace hm S) :
    ⟪u, v⟫_ℝ = timeZeroFourierCovariance m u.1 v.1 := by
  have hr := norm_add_sq_real u v
  have hc := norm_add_sq (𝕜 := ℂ) (finiteSourceMap hm S u) (finiteSourceMap hm S v)
  rw [← map_add] at hc
  change ‖u + v‖ ^ 2 = ‖u‖ ^ 2 +
    2 * (⟪timeZeroL2 hm u.1, timeZeroL2 hm v.1⟫_ℂ).re + ‖v‖ ^ 2 at hc
  have he : ⟪u, v⟫_ℝ = (⟪timeZeroL2 hm u.1, timeZeroL2 hm v.1⟫_ℂ).re := by
    linarith
  rw [he]
  rw [inner_timeZeroL2_gram]
  simp [Complex.mul_re]

variable [FiniteDimensional ℝ S]

/-- The commutation operator is constructed from the actual physical embedding. -/
noncomputable def finiteSourceCommutation :
    FiniteSourceSpace hm S →L[ℝ] FiniteSourceSpace hm S :=
  realCommutation (finiteSourceIsometry hm S)

theorem finiteSourceCommutation_symplectic (u v : FiniteSourceSpace hm S) :
    ⟪u, finiteSourceCommutation hm S v⟫_ℝ = timeZeroSymplectic u.1 v.1 := by
  erw [finiteSourceCommutation, inner_realCommutation]
  change 2 * (⟪timeZeroL2 hm u.1, timeZeroL2 hm v.1⟫_ℂ).im = _
  rw [inner_timeZeroL2_gram]
  simp [Complex.mul_im]

theorem finiteSourceCommutation_adjoint :
    (finiteSourceCommutation hm S).adjoint = -(finiteSourceCommutation hm S) :=
  realCommutation_mem_skewAdjoint (finiteSourceIsometry hm S)

theorem norm_finiteSourceCommutation_le_two : ‖finiteSourceCommutation hm S‖ ≤ 2 :=
  norm_realCommutation_le_two (finiteSourceIsometry hm S)

theorem finiteSourceCommutation_injective
    (hnd : ∀ u ∈ S, (∀ v ∈ S, timeZeroSymplectic u v = 0) → u = 0) :
    Function.Injective (finiteSourceCommutation hm S) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  apply Subtype.ext
  apply hnd u.1 u.2
  intro v hv
  erw [← finiteSourceCommutation_symplectic hm S u (⟨v, hv⟩ : FiniteSourceSpace hm S)]
  have h := realCommutation_skew_inner (finiteSourceIsometry hm S) u ⟨v, hv⟩
  change ⟪finiteSourceCommutation hm S u, (⟨v, hv⟩ : FiniteSourceSpace hm S)⟫_ℝ =
    -⟪u, finiteSourceCommutation hm S ⟨v, hv⟩⟫_ℝ at h
  change finiteSourceCommutation hm S u = 0 at hu
  erw [hu, inner_zero_left] at h
  exact neg_eq_zero.mp h.symm

/-- Positive skew frequencies and an actual orthonormal basis are consequences
of the source symplectic nondegeneracy, including the zero-dimensional case. -/
theorem finiteSource_exists_skew_basis
    (hnd : ∀ u ∈ S, (∀ v ∈ S, timeZeroSymplectic u v = 0) → u = 0) :
    ∃ (n : ℕ) (ν : Fin n → ℝ)
      (b : OrthonormalBasis (Fin n × Fin 2) ℝ (FiniteSourceSpace hm S)),
      (∀ i, 0 < ν i) ∧ ∀ i,
        finiteSourceCommutation hm S (b (i, 0)) = (-ν i) • b (i, 1) ∧
        finiteSourceCommutation hm S (b (i, 1)) = ν i • b (i, 0) := by
  apply Gaussian.exists_real_skew_symplectic_basis
    (finiteSourceCommutation hm S).toLinearMap
  · rw [ContinuousLinearMap.adjoint_toLinearMap, finiteSourceCommutation_adjoint]
    rfl
  · exact finiteSourceCommutation_injective hm S hnd

end VacuumBellSeparation
