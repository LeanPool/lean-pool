/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.AnnealedPlateau

/-!
# SmallScaleBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The corrected small-scale diffusivity envelope

ABK26's deterministic integration lemma assumes the all-scale estimate

`nu <= s_m <= (1 + nu^(-2) cstar gamma^(-1) 3^(2 gamma m)) nu`.

This file exposes that two-constant boundary directly for the genuine running
diffusivity.  The subsequent deterministic recurrence-integration provider can
therefore consume the sound `cstarPlus` envelope without adding an unproved
interface hypothesis.

## References

* ABK26, `e.small.scale.bound`.
* ABK26, `e.plateau.region.bound`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity

open Algsuperdiff.Section3.Provider.Base

noncomputable section

variable {d : ℕ}

/-- The corrected `e.small.scale.bound` for the genuine running diffusivity.

The envelope constant is `cstarPlus`, as required; this theorem does not
replace the directional `cstar` used by the recurrence or the target profile. -/
theorem annealedPlateau_smallScaleBound (M : ABKModel d) (m : ℤ) :
    M.nu ≤ (Annealed.sigmaBar M m : ℝ) ∧
      (Annealed.sigmaBar M m : ℝ) ≤
        (1 + (M.nu ^ 2)⁻¹ * Disorder.cstarPlus M * M.gamma⁻¹ *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) * M.nu := by
  obtain ⟨hlower, hupper⟩ := annealedPlateau M m
  refine ⟨hlower, ?_⟩
  let B : ℝ :=
    (M.nu ^ 2)⁻¹ * Disorder.cstarPlus M * M.gamma⁻¹ *
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))
  have hnu : 0 < M.nu := M.nu_pos
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hcoefficient : (1 + 4 * M.gamma) / 2 ≤ 1 := by
    linarith only [M.shellPrefix.gamma_le_quarter]
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (inv_nonneg.mpr (sq_nonneg M.nu))
          (Disorder.cstarPlus_pos M).le)
        (inv_pos.mpr hgamma).le)
      (Real.rpow_pos_of_pos (by norm_num) _).le
  have hamplitude :
      Disorder.cstarPlus M * (2 * M.nu ^ 2)⁻¹ * M.gamma⁻¹ *
          (1 + 4 * M.gamma) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) ≤ B := by
    calc
      Disorder.cstarPlus M * (2 * M.nu ^ 2)⁻¹ * M.gamma⁻¹ *
            (1 + 4 * M.gamma) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))
          = ((1 + 4 * M.gamma) / 2) * B := by
              dsimp only [B]
              field_simp [hnu.ne', hgamma.ne']
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right hcoefficient hB
      _ = B := one_mul B
  calc
    (Annealed.sigmaBar M m : ℝ) ≤
        M.nu * (1 + Disorder.cstarPlus M * (2 * M.nu ^ 2)⁻¹ * M.gamma⁻¹ *
          (1 + 4 * M.gamma) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := hupper
    _ ≤ M.nu * (1 + B) :=
      mul_le_mul_of_nonneg_left (by
        simpa only [add_comm] using add_le_add_left hamplitude 1) hnu.le
    _ = (1 + B) * M.nu := mul_comm _ _
    _ = (1 + (M.nu ^ 2)⁻¹ * Disorder.cstarPlus M * M.gamma⁻¹ *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) * M.nu := by
      rfl

end

end Algsuperdiff.Section3.Provider.Diffusivity
