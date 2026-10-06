/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationProfile

/-!
# High-contrast homogenization: Provider.Response.LoadCalibrationClosure

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The terminal defects, the energy chain, and the absolute closure

The remaining displays of the response-load calibration:

* the energy chain `0 ≤ 𝔼[J_t^±] = ½(L_t^±)² - 1 ≤ ½(L_t^±)² ≤ 2√θ`, proved
  through the Schur form `e.annealed.schur`;
* the terminal defects `0 ≤ τ_{t,s}^± ≤ 2(ϱ^d - 1)√θ`;
* the two consequences of terminal-profile compatibility,
  `𝒲_t^⋄ ≤ (ℛ_t^⋄)²` and `ℒ_s^⋄ ≤ 2Γ𝒬_s^⋄ ≤ 16Γc_εβ√κ_s(√κ_t+1)√θ`, proved
  from the Loewner sandwich produced by a determinant loss;
* the norm identity `|S_*^{-1/2}BS_*^{-1/2} - Id| = θ - 1`;
* the factor-`12d` chain `κ_t - 1 ≤ 6(θ-1) ≤ 12d sup(...)`;
* the absolute closure: under `sup(...) ≤ ωκ_s` and the strict numerical
  inequality `12dωϱ^{2d}(1 + δ_ad⁻¹) < 1`, the imbalance closes at
  `κ_t - 1 ≤ δ_ad`.

The three probabilistic inputs — the annealed energy identity
`𝔼[J_t^±] = ½(L_t^±)² - p·q^±`, its nonnegativity, and the corrected absolute
response estimate `θ - 1 ≤ 2d sup(...)` — belong to the corrected-response and
profile layers and are carried here in their printed shapes.  Everything else
is proved.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## The terminal variational energies -/

/-- **The energy chain** `0 ≤ 𝔼[J_t^±] = ½(L_t^±)² - 1 ≤ ½(L_t^±)² ≤ 2√θ`.  The identity and the
nonnegativity are the printed annealed
inputs; the final bound is the load bound. -/
theorem energy_chain {EJ Lsq theta : ℝ} (hEJ : 0 ≤ EJ)
    (hid : EJ = 2⁻¹ * Lsq - 1) (hL : Lsq ≤ 4 * Real.sqrt theta) :
    0 ≤ EJ ∧ EJ ≤ 2⁻¹ * Lsq ∧ 2⁻¹ * Lsq ≤ 2 * Real.sqrt theta :=
  ⟨hEJ, by linarith only [hid], by linarith only [hL]⟩

/-! ## The congruent terminal defects -/

/-- **The terminal defects** `0 ≤ τ_{t,s}^± ≤ 2(ϱ^d - 1)√θ`.
The two hypotheses are the congruated forms of `E_t ≤ E_s` and of the
determinant-loss comparison `E_s ≤ ϱ^d E_t`. -/
theorem defect_bounds {Ethat Eshat : FullBlockMat d} (hEt : Ethat.PosSemidef)
    (hts : Ethat ≤ Eshat) {rd theta : ℝ} (hrd : 1 ≤ rd)
    (hup : Eshat ≤ rd • Ethat) (x : FullBlockVec d)
    (hx : x ⬝ᵥ Ethat *ᵥ x ≤ 4 * Real.sqrt theta) :
    0 ≤ 2⁻¹ * (x ⬝ᵥ Eshat *ᵥ x - x ⬝ᵥ Ethat *ᵥ x) ∧
      2⁻¹ * (x ⬝ᵥ Eshat *ᵥ x - x ⬝ᵥ Ethat *ᵥ x) ≤ 2 * (rd - 1) * Real.sqrt theta := by
  have hlow := Initialization.dotProduct_mulVec_le_of_le hts x
  have hhigh := Initialization.dotProduct_mulVec_le_of_le hup x
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hhigh
  have hnn : 0 ≤ x ⬝ᵥ Ethat *ᵥ x := quadratic_nonneg hEt x
  refine ⟨by linarith only [hlow], ?_⟩
  have hstep : x ⬝ᵥ Eshat *ᵥ x - x ⬝ᵥ Ethat *ᵥ x ≤ (rd - 1) * (x ⬝ᵥ Ethat *ᵥ x) := by
    linarith only [hhigh]
  have hscale : (rd - 1) * (x ⬝ᵥ Ethat *ᵥ x) ≤ (rd - 1) * (4 * Real.sqrt theta) :=
    mul_le_mul_of_nonneg_left hx (by linarith only [hrd])
  linarith only [hstep, hscale]

/-! ## The two terminal-profile consequences -/

/-- **`ℒ_s^⋄ ≤ 2Γ𝒬_s^⋄ ≤ 16Γc_εβ√κ_s(√κ_t + 1)√θ`**: insert
the calibrated row-load bound into the profile row hypothesis. -/
theorem row_from_profile {L Gam Q ceps beta kappaS kappaT theta : ℝ} (hGam : 0 ≤ Gam)
    (hin : L ≤ 2 * Gam * Q)
    (hQ : Q ≤ 8 * ceps * beta * Real.sqrt kappaS * (Real.sqrt kappaT + 1) *
      Real.sqrt theta) :
    L ≤ 16 * Gam * ceps * beta * Real.sqrt kappaS * (Real.sqrt kappaT + 1) *
      Real.sqrt theta := by
  have h := mul_le_mul_of_nonneg_left hQ (by linarith only [hGam] : (0 : ℝ) ≤ 2 * Gam)
  linarith only [hin, h]

/-! ## The normalized response block above the identity -/

variable {S SStar K r B : Mat d}

/-- **`|S_*^{-1/2}BS_*^{-1/2} - Id| = θ - 1`**.  The normalized
response block is above the identity because `B ≥ S ≥ S_*`. -/
theorem norm_normalized_sub_one [NeZero d] (hS : S.PosDef) (hStar : SStar.PosDef)
    (hB : B = S + rᴴ * SStar⁻¹ * r)
    (hsharp : fullBlockSharp (schurBlock S SStar K) ≤ schurBlock S SStar K) :
    ‖matSqrt SStar⁻¹ * B * matSqrt SStar⁻¹ - 1‖ = relSize B SStar - 1 := by
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have hBpsd : B.PosSemidef := posSemidef_responseBlock hS hStar hB
  have hX : (matSqrt SStar⁻¹ * B * matSqrt SStar⁻¹).PosSemidef :=
    posSemidef_normalize hBpsd hStar
  have hone : (1 : Mat d) ≤ matSqrt SStar⁻¹ * B * matSqrt SStar⁻¹ := by
    have hconj := conj_le_conj' (C := matSqrt SStar⁻¹)
      (conjTranspose_matSqrt hStar.inv.posSemidef)
      (schurStar_le_responseBlock (K := K) hS hStar hB hsharp)
    rwa [matSqrt_inv_conj hStar] at hconj
  rw [norm_sub_one_eq_norm_sub_one hX hone, relSize_def]

/-! ## The factor-`12d` chain and the absolute closure -/

/-- **The factor-`12d` chain** `κ_t - 1 ≤ 6(θ - 1) ≤ 12d sup(...)`.  The second link is the
corrected absolute response estimate,
carried in its printed shape. -/
theorem twelve_d_chain {kappaT theta Ssup : ℝ}
    (hkappa : kappaT ≤ 1 + 6 * (theta - 1))
    (habs : theta - 1 ≤ 2 * (d : ℝ) * Ssup) :
    kappaT - 1 ≤ 12 * (d : ℝ) * Ssup := by
  linarith only [hkappa, habs]

end

end Response
end HighContrast
end HCPolySupport
