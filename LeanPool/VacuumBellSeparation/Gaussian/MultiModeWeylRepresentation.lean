/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeCoherentTotality
public import LeanPool.VacuumBellSeparation.Weyl.Existence

/-!
# A genuine finite-mode Weyl/coherent unitary realization

The actual full occupation-space coherent vectors realize the Gaussian
kernel on finite-dimensional complex Euclidean phase space. The map on
RKHS point masses extends through the null quotient and completion and
is onto by the proved coherent totality. Thus the unitary equivalence is
constructed, including the zero-mode case.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open scoped ComplexConjugate

/-- Multi mode phase space with underlying type `EuclideanSpace ℂ (Fin m)`. -/
abbrev MultiModePhaseSpace (m : ℕ) := EuclideanSpace ℂ (Fin m)

/-- Multi coherent vector given by `Complex.exp ((-(‖z‖ ^ 2 / 2) : ℝ) : ℂ) • multiExponentialVector
(fun j => z j)`. -/
def multiCoherentVector {m : ℕ} (z : MultiModePhaseSpace m) : MultiModeOscillatorSpace m :=
  Complex.exp ((-(‖z‖ ^ 2 / 2) : ℝ) : ℂ) • multiExponentialVector (fun j => z j)

theorem inner_multiCoherentVector {m : ℕ} (z w : MultiModePhaseSpace m) :
    inner ℂ (multiCoherentVector z) (multiCoherentVector w) =
      weylKernel (id : MultiModePhaseSpace m → MultiModePhaseSpace m) z w := by
  rw [multiCoherentVector, multiCoherentVector, inner_smul_left, inner_smul_right,
    inner_multiExponentialVector, weylKernel_eq]
  simp only [id_eq, PiLp.inner_apply, RCLike.inner_apply']
  ring

theorem multiCoherentVector_dense_span (m : ℕ) :
    (Submodule.span ℂ (Set.range (multiCoherentVector (m := m)))).topologicalClosure = ⊤ := by
  have hspan : Submodule.span ℂ (Set.range (multiExponentialVector (m := m))) ≤
      Submodule.span ℂ (Set.range (multiCoherentVector (m := m))) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    let w : MultiModePhaseSpace m := WithLp.toLp 2 z
    have hmem : multiCoherentVector w ∈
        Submodule.span ℂ (Set.range (multiCoherentVector (m := m))) :=
      Submodule.subset_span ⟨w, rfl⟩
    have h := Submodule.smul_mem
      (Submodule.span ℂ (Set.range (multiCoherentVector (m := m))))
      (Complex.exp ((-(‖w‖ ^ 2 / 2) : ℝ) : ℂ))⁻¹ hmem
    have hw : (fun j => w j) = z := by
      funext j
      rfl
    have hcancel : (Complex.exp ((-(‖w‖ ^ 2 / 2) : ℝ) : ℂ))⁻¹ •
        multiCoherentVector w = multiExponentialVector z := by
      calc
        _ = multiExponentialVector (fun j => w j) :=
          inv_smul_smul₀ (Complex.exp_ne_zero _) _
        _ = _ := congrArg (multiExponentialVector (m := m)) hw
    rw [hcancel] at h
    exact h
  have h := Submodule.topologicalClosure_mono hspan
  rw [multiExponentialVector_dense_span] at h
  exact top_unique h

/-- Linear map for the multi coherent realization₀, of type `MultiModePhaseSpace m →
MultiModePhaseSpace m)) →ₗ[ℂ] MultiModeOscillatorSpace m`. -/
def multiCoherentRealization₀ (m : ℕ) :
    RKHS.H₀ (weylRKHSKernel (id : MultiModePhaseSpace m → MultiModePhaseSpace m)) →ₗ[ℂ]
      MultiModeOscillatorSpace m :=
  Finsupp.linearCombination ℂ
    (fun p : MultiModePhaseSpace m × ℂ => p.2 • multiCoherentVector p.1)

@[simp] theorem multiCoherentRealization₀_single {m : ℕ} (z : MultiModePhaseSpace m) (v a : ℂ) :
    multiCoherentRealization₀ m (Finsupp.single (z, v) a) = a • (v • multiCoherentVector z) := by
  simp [multiCoherentRealization₀]

theorem inner_multiCoherentRealization₀ {m : ℕ}
    (f g : RKHS.H₀ (weylRKHSKernel (id : MultiModePhaseSpace m → MultiModePhaseSpace m))) :
    inner ℂ (multiCoherentRealization₀ m f) (multiCoherentRealization₀ m g) = inner ℂ f g := by
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
      rw [multiCoherentRealization₀_single, multiCoherentRealization₀_single, inner_H₀_single]
      simp only [inner_smul_left, inner_smul_right, inner_multiCoherentVector]
      ring

/-- Linear isometry for the multi coherent realization iso₀, of type `MultiModePhaseSpace m →
MultiModePhaseSpace m)) →ₗᵢ[ℂ] MultiModeOscillatorSpace m`. -/
def multiCoherentRealizationIso₀ (m : ℕ) :
    RKHS.H₀ (weylRKHSKernel (id : MultiModePhaseSpace m → MultiModePhaseSpace m)) →ₗᵢ[ℂ]
      MultiModeOscillatorSpace m :=
  (multiCoherentRealization₀ m).isometryOfInner inner_multiCoherentRealization₀

/-- Linear isometry for the multi coherent realization, of type `MultiModePhaseSpace m →
MultiModePhaseSpace m) →ₗᵢ[ℂ] MultiModeOscillatorSpace m`. -/
def multiCoherentRealization (m : ℕ) :
    WeylSpace (id : MultiModePhaseSpace m → MultiModePhaseSpace m) →ₗᵢ[ℂ]
      MultiModeOscillatorSpace m :=
  (multiCoherentRealizationIso₀ m).fromCompletion

theorem multiCoherentRealization_weylVec {m : ℕ} (z : MultiModePhaseSpace m) :
    multiCoherentRealization m (weylVec (id : MultiModePhaseSpace m → MultiModePhaseSpace m) z) =
      multiCoherentVector z := by
  rw [weylVec_def, multiCoherentRealization, LinearIsometry.fromCompletion_apply_coe]
  change multiCoherentRealization₀ m (Finsupp.single (z, 1) 1) = multiCoherentVector z
  simp

theorem multiCoherentRealization_surjective (m : ℕ) :
    Function.Surjective (multiCoherentRealization m) := by
  have hclosed : IsClosed (Set.range (multiCoherentRealization m)) :=
    (multiCoherentRealization m).isometry.isClosedEmbedding.isClosed_range
  have hspan : Submodule.span ℂ (Set.range (multiCoherentVector (m := m))) ≤
      (multiCoherentRealization m).toLinearMap.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    exact ⟨weylVec (id : MultiModePhaseSpace m → MultiModePhaseSpace m) z,
      multiCoherentRealization_weylVec z⟩
  have hclosure := (Submodule.span ℂ (Set.range (multiCoherentVector
    (m := m)))).topologicalClosure_minimal
    hspan hclosed
  rw [multiCoherentVector_dense_span] at hclosure
  exact LinearMap.range_eq_top.mp (top_unique hclosure)

/-- Unitary identification of the multimode Weyl representation with its coherent-vector model. -/
def multiWeylCoherentEquiv (m : ℕ) :
    WeylSpace (id : MultiModePhaseSpace m → MultiModePhaseSpace m) ≃ₗᵢ[ℂ]
      MultiModeOscillatorSpace m :=
  LinearIsometryEquiv.ofSurjective (multiCoherentRealization m)
    (multiCoherentRealization_surjective m)

theorem multiWeylCoherentEquiv_weylVec {m : ℕ} (z : MultiModePhaseSpace m) :
    multiWeylCoherentEquiv m (weylVec (id : MultiModePhaseSpace m → MultiModePhaseSpace m) z) =
      multiCoherentVector z := multiCoherentRealization_weylVec z

end VacuumBellSeparation.Gaussian
