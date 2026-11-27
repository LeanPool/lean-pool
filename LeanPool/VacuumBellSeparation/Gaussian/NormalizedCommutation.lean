/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalCompression
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

/-!
# Normalized commutation coordinates

Algebraic transport from a bounded complex skew-adjoint `J`, with norm at
most two, to `B=iJ/2`, `G±=1±B`, `d=|B|` and the manuscript's reserve and
thermal operators. Constructing this complex `J` from the real source
covariance/symplectic form is done in other modules (`complexCommutation_mem_skewAdjoint` and
`norm_complexCommutation_le_two` in `Gaussian/SourceGram.lean`; for the free field,
`sourceCommutation_symplectic` in `FreeField/SourceSpace.lean`).
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The normalized commutation operator `iJ/2`. -/
noncomputable def normalizedCommutation (J : F →L[ℂ] F) : F →L[ℂ] F :=
  (Complex.I / 2) • J

theorem normalizedCommutation_isSelfAdjoint {J : F →L[ℂ] F}
    (hJ : J ∈ skewAdjoint (F →L[ℂ] F)) : IsSelfAdjoint (normalizedCommutation J) := by
  apply isSelfAdjoint_smul_of_mem_skewAdjoint _ hJ
  change star (Complex.I / 2) = -(Complex.I / 2)
  simp [neg_div]

theorem norm_normalizedCommutation_le_one {J : F →L[ℂ] F} (hJ : ‖J‖ ≤ 2) :
    ‖normalizedCommutation J‖ ≤ 1 := by
  rw [normalizedCommutation, norm_smul, norm_div]
  norm_num
  linarith

/-- The two normalized Gram expressions. -/
def gramPlus (B : F →L[ℂ] F) : F →L[ℂ] F := 1 + B

/-- Gram minus given by `1 - B`. -/
def gramMinus (B : F →L[ℂ] F) : F →L[ℂ] F := 1 - B

omit [CompleteSpace F] in
theorem gramPlus_add_gramMinus (B : F →L[ℂ] F) : gramPlus B + gramMinus B = 2 := by
  unfold gramPlus gramMinus
  calc
    (1 : F →L[ℂ] F) + B + (1 - B) = 1 + 1 := by abel
    _ = 2 := by norm_num

omit [CompleteSpace F] in
theorem gramPlus_mul_gramMinus (B : F →L[ℂ] F) :
    gramPlus B * gramMinus B = reserveSquare B := by
  unfold gramPlus gramMinus reserveSquare
  noncomm_ring

omit [CompleteSpace F] in
theorem gramPlus_commute_gramMinus (B : F →L[ℂ] F) : Commute (gramPlus B) (gramMinus B) := by
  change (1 + B) * (1 - B) = (1 - B) * (1 + B)
  noncomm_ring

theorem gramPlus_nonneg {B : F →L[ℂ] F} (hB : IsSelfAdjoint B) (hnorm : ‖B‖ ≤ 1) :
    0 ≤ gramPlus B := by
  change 0 ≤ 1 + B
  rw [← cfc_one_add_id B hB]
  apply cfc_nonneg
  intro x hx
  have h := spectrum_mem_Icc_of_norm_le_one hnorm hx
  linarith [h.1]

theorem gramMinus_nonneg {B : F →L[ℂ] F} (hB : IsSelfAdjoint B) (hnorm : ‖B‖ ≤ 1) :
    0 ≤ gramMinus B := by
  change 0 ≤ 1 - B
  rw [← cfc_one_sub_id B hB]
  apply cfc_nonneg
  intro x hx
  have h := spectrum_mem_Icc_of_norm_le_one hnorm hx
  linarith [h.2]

theorem reserve_eq_sqrt_gramProduct (B : F →L[ℂ] F) :
    reserve B = CFC.sqrt (gramPlus B * gramMinus B) := by
  rw [gramPlus_mul_gramMinus]
  rfl

theorem reserve_eq_sqrt_one_sub_abs_sq {B : F →L[ℂ] F} (hB : IsSelfAdjoint B) :
    reserve B = CFC.sqrt (1 - (CFC.abs B) ^ 2) := by
  rw [CFC.abs_sq, hB.star_eq, ← pow_two]
  rfl

/-- The thermal operator, the manuscript's `H_b(I)` written as a function of `d=|B|`. -/
noncomputable def normalizedThermal (b : ℝ) (B : F →L[ℂ] F) : F →L[ℂ] F :=
  cfc (thermalIncrement b) (CFC.abs B)

theorem normalizedThermal_eq_cfc_abs {b : ℝ} (hb : 0 < b)
    {B : F →L[ℂ] F} (hB : IsSelfAdjoint B) (hnorm : ‖B‖ ≤ 1) :
    normalizedThermal b B = cfc (fun x : ℝ => thermalIncrement b |x|) B := by
  have himage : (fun x : ℝ => ‖x‖) '' spectrum ℝ B ⊆ Set.Icc (0 : ℝ) 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨norm_nonneg x, (IsometricContinuousFunctionalCalculus.norm_spectrum_le B hx hB).trans
      hnorm⟩
  rw [normalizedThermal, CFC.abs_eq_cfc_norm B hB,
    ← cfc_comp' (thermalIncrement b) (fun x : ℝ => ‖x‖) B
      ((continuousOn_thermalIncrement hb).mono himage) continuous_norm.continuousOn hB]
  simp only [Real.norm_eq_abs]

/-- The high-compression chain (4.11), with the manuscript's `H_b` written as a function of
`|B|`. -/
theorem normalizedThermal_compression_chain (ι : E →ₗᵢ[ℂ] F)
    {B : F →L[ℂ] F} (hB : IsSelfAdjoint B) (hnorm : ‖B‖ ≤ 1) (n : ℕ) :
    let b : ℝ := ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)
    thermalConst b • compression ι ((reserve B) ^ (2 * b)) ≤
        compression ι (normalizedThermal b B) ∧
      compression ι (normalizedThermal b B) ≤ normalizedThermal b (compression ι B) := by
  dsimp only
  have hb : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) := by positivity
  rw [normalizedThermal_eq_cfc_abs hb hB hnorm,
    normalizedThermal_eq_cfc_abs hb (compression_isSelfAdjoint ι hB)
      ((norm_compression_le ι B).trans hnorm)]
  exact high_compression_chain ι hB hnorm n

end VacuumBellSeparation.Gaussian
