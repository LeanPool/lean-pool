/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.EventConstants

/-!
# The literal Tsirelson bound with the manuscript normalization

The Hilbert-space parallelogram identity bounds the CHSH operator by
2 sqrt(2). Commutativity makes it selfadjoint, so every original positive
unital state has normalized CHSH expectation at most sqrt(2).
-/

@[expose] public section

namespace VacuumBellSeparation
open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem norm_chshOp_le_two_sqrt_two {A₀ A₁ B₀ B₁ : H →L[ℂ] H}
    (hA₀ : ‖A₀‖ ≤ 1) (hA₁ : ‖A₁‖ ≤ 1) (hB₀ : ‖B₀‖ ≤ 1) (hB₁ : ‖B₁‖ ≤ 1) :
    ‖chshOp A₀ A₁ B₀ B₁‖ ≤ 2 * Real.sqrt 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hB0 : ‖B₀ x‖ ≤ ‖x‖ := (B₀.le_opNorm x).trans
    (by simpa using mul_le_mul_of_nonneg_right hB₀ (norm_nonneg x))
  have hB1 : ‖B₁ x‖ ≤ ‖x‖ := (B₁.le_opNorm x).trans
    (by simpa using mul_le_mul_of_nonneg_right hB₁ (norm_nonneg x))
  have hA0 : ‖A₀ (B₀ x + B₁ x)‖ ≤ ‖B₀ x + B₁ x‖ :=
    (A₀.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right hA₀ (norm_nonneg _))
  have hA1 : ‖A₁ (B₀ x - B₁ x)‖ ≤ ‖B₀ x - B₁ x‖ :=
    (A₁.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right hA₁ (norm_nonneg _))
  have hpar := parallelogram_law_with_norm ℂ (B₀ x) (B₁ x)
  have hsq0 := pow_le_pow_left₀ (norm_nonneg _) hB0 2
  have hsq1 := pow_le_pow_left₀ (norm_nonneg _) hB1 2
  have hs : ‖B₀ x + B₁ x‖ + ‖B₀ x - B₁ x‖ ≤ 2 * Real.sqrt 2 * ‖x‖ := by
    have ht : (‖B₀ x + B₁ x‖ + ‖B₀ x - B₁ x‖) ^ 2 ≤ 8 * ‖x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖B₀ x + B₁ x‖ - ‖B₀ x - B₁ x‖)]
    have hroot : (2 * Real.sqrt 2 * ‖x‖) ^ 2 = 8 * ‖x‖ ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    exact nonneg_le_nonneg_of_sq_le_sq (by positivity)
      (by simpa only [pow_two] using ht.trans_eq hroot.symm)
  change ‖A₀ (B₀ x + B₁ x) + A₁ (B₀ x - B₁ x)‖ ≤ _
  exact (norm_add_le _ _).trans ((add_le_add hA0 hA1).trans hs)

theorem chshOp_isSelfAdjoint {𝔄 𝔅 : VonNeumannAlgebra H} (hcomm : Commuting 𝔄 𝔅)
    {A₀ A₁ B₀ B₁ : H →L[ℂ] H}
    (hA₀ : A₀ ∈ saContractions 𝔄) (hA₁ : A₁ ∈ saContractions 𝔄)
    (hB₀ : B₀ ∈ saContractions 𝔅) (hB₁ : B₁ ∈ saContractions 𝔅) :
    IsSelfAdjoint (chshOp A₀ A₁ B₀ B₁) := by
  rw [isSelfAdjoint_iff]
  simp only [chshOp, star_add, star_sub, star_mul,
    hA₀.2.1.star_eq, hA₁.2.1.star_eq, hB₀.2.1.star_eq, hB₁.2.1.star_eq,
    mul_add, mul_sub,
    hcomm A₀ hA₀.1 B₀ hB₀.1, hcomm A₀ hA₀.1 B₁ hB₁.1,
    hcomm A₁ hA₁.1 B₀ hB₀.1, hcomm A₁ hA₁.1 B₁ hB₁.1]

theorem chshValue_le_sqrt_two (ω : State H) {𝔄 𝔅 : VonNeumannAlgebra H}
    (hcomm : Commuting 𝔄 𝔅) {A₀ A₁ B₀ B₁ : H →L[ℂ] H}
    (hA₀ : A₀ ∈ saContractions 𝔄) (hA₁ : A₁ ∈ saContractions 𝔄)
    (hB₀ : B₀ ∈ saContractions 𝔅) (hB₁ : B₁ ∈ saContractions 𝔅) :
    (1 / 2 : ℝ) * ‖ω (chshOp A₀ A₁ B₀ B₁)‖ ≤ Real.sqrt 2 := by
  have h := ω.norm_apply_le_of_isSelfAdjoint (chshOp_isSelfAdjoint hcomm hA₀ hA₁ hB₀ hB₁)
    (by positivity : (0 : ℝ) < 2 * Real.sqrt 2)
    (norm_chshOp_le_two_sqrt_two hA₀.2.2 hA₁.2.2 hB₀.2.2 hB₁.2.2)
  linarith

/-- Source Section 2.1, with the original supremum over all admissible
selfadjoint contractions and the original general state definition. -/
theorem bellCorrelation_le_sqrt_two (ω : State H) {𝔄 𝔅 : VonNeumannAlgebra H}
    (hcomm : Commuting 𝔄 𝔅) : bellCorrelation ω 𝔄 𝔅 ≤ Real.sqrt 2 := by
  apply csSup_le ⟨1, one_mem_chshValues ω 𝔄 𝔅⟩
  rintro x ⟨A₀, hA₀, A₁, hA₁, B₀, hB₀, B₁, hB₁, rfl⟩
  exact chshValue_le_sqrt_two ω hcomm hA₀ hA₁ hB₀ hB₁

end VacuumBellSeparation
