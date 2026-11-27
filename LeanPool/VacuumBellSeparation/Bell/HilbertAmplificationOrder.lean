/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.HilbertAmplificationCommutant
public import LeanPool.VacuumBellSeparation.Gaussian.Compression

/-!
# Order and norm of the actual extracted amplified operator

A single-coordinate embedding is a Hilbert isometry. The diagonal block
is precisely compression along that isometry, so positive contractions
extract to positive contractions. The anchor index is explicit.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian ContinuousLinearMap
open scoped InnerProductSpace ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (ι : Type*)

/-- Hilbert coordinate isometry. -/
noncomputable def hilbertCoordinateIsometry (k : ι) : H →ₗᵢ[ℂ] lp (fun _ : ι => H) 2 := by
  classical
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  exact (lp.lsingle (𝕜 := ℂ) (E := fun _ : ι => H) 2 k).toLinearIsometry
    (lp.isometry_single (E := fun _ : ι => H) (p := 2) k)

theorem hilbertCoordinateIsometry_adjoint (k : ι) (v : lp (fun _ : ι => H) 2) :
    (hilbertCoordinateIsometry (H := H) ι k).toContinuousLinearMap.adjoint v = v k := by
  classical
  apply ext_inner_left ℂ
  intro x
  rw [adjoint_inner_right]
  exact lp.inner_single_left (𝕜 := ℂ) (G := fun _ : ι => H) k x v

theorem hilbertAmplificationBlock_diagonal_eq_compression
    (B : lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2) (k : ι) :
    hilbertAmplificationBlock ι B k k = compression (hilbertCoordinateIsometry ι k) B := by
  classical
  ext x
  rw [hilbertAmplificationBlock_apply]
  change B (lp.single 2 k x) k =
    (hilbertCoordinateIsometry ι k).toContinuousLinearMap.adjoint (B (lp.single 2 k x))
  rw [hilbertCoordinateIsometry_adjoint]

theorem hilbertAmplificationBlock_nonneg
    {B : lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2} (hB : 0 ≤ B) (k : ι) :
    0 ≤ hilbertAmplificationBlock ι B k k := by
  rw [hilbertAmplificationBlock_diagonal_eq_compression]
  exact compression_nonneg _ hB

theorem hilbertAmplificationBlock_le_one
    {B : lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2} (hB : B ≤ 1) (k : ι) :
    hilbertAmplificationBlock ι B k k ≤ 1 := by
  rw [hilbertAmplificationBlock_diagonal_eq_compression, ← compression_one
    (hilbertCoordinateIsometry ι k)]
  exact compression_mono _ hB

omit [CompleteSpace H] in
theorem norm_hilbertAmplificationBlock_le
    (B : lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2) (k : ι) :
    ‖hilbertAmplificationBlock ι B k k‖ ≤ ‖B‖ := by
  classical
  apply opNorm_le_bound _ (norm_nonneg B)
  intro x
  rw [hilbertAmplificationBlock_apply]
  exact (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) _ k).trans
    (by simpa only [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
      using B.le_opNorm (lp.single 2 k x))

/-- Every actual amplified-algebra effect has a genuine oscillator effect
whose amplification is exactly the original operator. -/
theorem exists_effect_of_mem_amplifiedVNA (S : Set (H →L[ℂ] H)) (k : ι)
    {B : lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2}
    (hB : B ∈ generatedVNA (hilbertAmplification ι '' S)) (hB₀ : 0 ≤ B) (hB₁ : B ≤ 1) :
    ∃ A : H →L[ℂ] H, 0 ≤ A ∧ A ≤ 1 ∧ B = hilbertAmplification ι A :=
  ⟨hilbertAmplificationBlock ι B k k, hilbertAmplificationBlock_nonneg ι hB₀ k,
    hilbertAmplificationBlock_le_one ι hB₁ k,
    eq_hilbertAmplification_of_mem_generatedVNA ι S k hB⟩

end VacuumBellSeparation
