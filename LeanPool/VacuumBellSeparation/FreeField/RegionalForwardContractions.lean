/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CanonicalContractionExhaustion
public import Mathlib.Analysis.Complex.Basic

/-!
# Regional covariance for arbitrary complex contractions

The actual selfadjoint exhaustion suffices: real and imaginary parts of
a contraction are selfadjoint contractions in the same von Neumann
algebra. Bilinearity gives four terms and a universal factor four.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open ContinuousLinearMap
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem realPart_mem_saContractions {M : VonNeumannAlgebra H}
    {A : H →L[ℂ] H} (hA : A ∈ M) (hAn : ‖A‖ ≤ 1) :
    (realPart A : H →L[ℂ] H) ∈ saContractions M := by
  refine ⟨?_, (realPart A).2, (realPart.norm_le A).trans hAn⟩
  rw [realPart_apply_coe]
  exact starSubalgebra_real_smul_mem M.toStarSubalgebra
    (M.toStarSubalgebra.add_mem hA (M.toStarSubalgebra.star_mem' hA)) _

theorem imaginaryPart_mem_saContractions {M : VonNeumannAlgebra H}
    {A : H →L[ℂ] H} (hA : A ∈ M) (hAn : ‖A‖ ≤ 1) :
    (imaginaryPart A : H →L[ℂ] H) ∈ saContractions M := by
  refine ⟨?_, (imaginaryPart A).2, (imaginaryPart.norm_le A).trans hAn⟩
  rw [imaginaryPart_apply_coe]
  exact M.toStarSubalgebra.smul_mem
    (starSubalgebra_real_smul_mem M.toStarSubalgebra
      (M.toStarSubalgebra.sub_mem hA (M.toStarSubalgebra.star_mem' hA)) _) _

theorem vacuumComplexCovariance_real_imaginary (Ω : H) (A B : H →L[ℂ] H) :
    vacuumComplexCovariance Ω A B =
      (vacuumComplexCovariance Ω (realPart A) (realPart B) +
        Complex.I * vacuumComplexCovariance Ω (realPart A) (imaginaryPart B)) +
      (Complex.I * vacuumComplexCovariance Ω (imaginaryPart A) (realPart B) +
        Complex.I * Complex.I * vacuumComplexCovariance Ω (imaginaryPart A) (imaginaryPart B)) := by
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart A, ← realPart_add_I_smul_imaginaryPart B]
  simp only [vacuumComplexCovariance, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, add_apply, smul_apply, inner_add_right, inner_smul_right]
  ring

/-- Full complex contractions, with no selfadjointness or approximation
hypothesis in the conclusion. -/
theorem covariance_bound_all_contractions_of_selfAdjoint
    (Ω : H) (M N : VonNeumannAlgebra H) (C : ℝ)
    (hbound : ∀ A ∈ saContractions M, ∀ B ∈ saContractions N,
      ‖vacuumComplexCovariance Ω A B‖ ≤ C)
    {A B : H →L[ℂ] H} (hA : A ∈ M) (hB : B ∈ N)
    (hAn : ‖A‖ ≤ 1) (hBn : ‖B‖ ≤ 1) :
    ‖vacuumComplexCovariance Ω A B‖ ≤ 4 * C := by
  have har := realPart_mem_saContractions hA hAn
  have hai := imaginaryPart_mem_saContractions hA hAn
  have hbr := realPart_mem_saContractions hB hBn
  have hbi := imaginaryPart_mem_saContractions hB hBn
  have hrr := hbound _ har _ hbr
  have hri := hbound _ har _ hbi
  have hir := hbound _ hai _ hbr
  have hii := hbound _ hai _ hbi
  rw [vacuumComplexCovariance_real_imaginary]
  calc
    _ ≤ (‖vacuumComplexCovariance Ω (realPart A) (realPart B)‖ +
          ‖Complex.I * vacuumComplexCovariance Ω (realPart A) (imaginaryPart B)‖) +
        (‖Complex.I * vacuumComplexCovariance Ω (imaginaryPart A) (realPart B)‖ +
          ‖Complex.I * Complex.I * vacuumComplexCovariance Ω (imaginaryPart A)
            (imaginaryPart B)‖) :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ 4 * C := by
      simp only [norm_mul, Complex.norm_I, one_mul]
      linarith

theorem canonical_covariance_bound_extends_to_all_local_contractions
    {m : ℝ} (V : FreeFieldVacuum m H) (hm : 0 < m)
    (U W : Set (EuclideanSpace ℝ (Fin 3))) (C : ℝ)
    (hfinite : ∀ S T : Submodule ℝ TimeZeroSource,
      IsCanonicalSourceSystem U S → IsCanonicalSourceSystem W T →
      ∀ A ∈ canonicalSourceAlgebra V hm S, ∀ B ∈ canonicalSourceAlgebra V hm T,
        ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ‖vacuumComplexCovariance V.vacuum A B‖ ≤ C)
    {A B : H →L[ℂ] H} (hA : A ∈ timeZeroLocalAlgebra V hm U)
    (hB : B ∈ timeZeroLocalAlgebra V hm W) (hAn : ‖A‖ ≤ 1) (hBn : ‖B‖ ≤ 1) :
    ‖vacuumComplexCovariance V.vacuum A B‖ ≤ 4 * C := by
  apply covariance_bound_all_contractions_of_selfAdjoint V.vacuum
    (timeZeroLocalAlgebra V hm U) (timeZeroLocalAlgebra V hm W) C _ hA hB hAn hBn
  intro A hA B hB
  exact canonical_covariance_bound_extends_to_local V hm U W C
    (fun S T hS hT A hA B hB => hfinite S T hS hT A hA.1 B hB.1 hA.2.2 hB.2.2) hA hB

end VacuumBellSeparation
