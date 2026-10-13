/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.AuxiliaryScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.IntrinsicScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.ConfinementScale

/-!
# PthMomentProcessScale

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Confinement-scale comparisons for the displacement minimum

The widened random scale controls every larger triadic scale.  Combined with the intrinsic-scale
identity, this bounds the random displacement scale by the two-branch deterministic minimum used
in the stream-process tail estimate.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section5.Support
open scoped ENNReal

noncomputable section

private theorem one_le_anomalous_intrinsic {nu cstar gamma t : ℝ}
    (hnu : 0 < nu) (hcstar : 0 < cstar) (hgamma : 0 < gamma)
    (hgamma1 : gamma < 1) (hgc : gamma ≤ cstar) (ht : 0 < t) :
    1 ≤ (cstar⁻¹ * gamma) ^ (1 / 2 : ℝ) *
      ((intrinsicScale nu cstar gamma t ^ (2 - gamma) / t) ^ (1 - gamma)⁻¹) := by
  let R := intrinsicScale nu cstar gamma t
  let A := R ^ (2 - gamma) / t
  let B := Real.sqrt (cstar * gamma⁻¹)
  have hR : 0 < R := intrinsicScale_pos hnu hcstar hgamma ht
  have hA : 0 < A := div_pos (Real.rpow_pos_of_pos hR _) ht
  have hB : 0 < B := Real.sqrt_pos.2 (by positivity)
  have hident := intrinsicScale_sq_rpow hnu hcstar hgamma (by linarith only [hgamma1]) ht
  have hterm : cstar * gamma⁻¹ * t ^ (2 : ℕ) ≤
      (R ^ (2 : ℕ)) ^ (2 - gamma) := by
    dsimp only [R] at hident ⊢
    rw [hident]
    exact le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
  have hRpow : (R ^ (2 : ℕ)) ^ (2 - gamma) = (R ^ (2 - gamma)) ^ (2 : ℕ) := by
    calc
      (R ^ (2 : ℕ)) ^ (2 - gamma) = (R ^ (2 : ℝ)) ^ (2 - gamma) := by
        rw [Real.rpow_two]
      _ = R ^ ((2 : ℝ) * (2 - gamma)) := (Real.rpow_mul hR.le _ _).symm
      _ = R ^ ((2 - gamma) * (2 : ℝ)) := by ring_nf
      _ = (R ^ (2 - gamma)) ^ (2 : ℝ) := Real.rpow_mul hR.le _ _
      _ = (R ^ (2 - gamma)) ^ (2 : ℕ) := Real.rpow_natCast _ _
  have hBA : B ≤ A := by
    rw [Real.sqrt_le_iff]
    refine ⟨hA.le, ?_⟩
    dsimp only [A, B]
    rw [div_pow]
    rw [hRpow] at hterm
    exact (le_div_iff₀ (by positivity : 0 < t ^ (2 : ℕ))).2 (by
      simpa only [mul_comm] using hterm)
  have hB1 : 1 ≤ B := by
    rw [Real.one_le_sqrt]
    have hdiv : 1 ≤ cstar / gamma := (le_div_iff₀ hgamma).2 (by simpa using hgc)
    simpa only [div_eq_mul_inv] using hdiv
  have hq : 1 ≤ (1 - gamma)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (by linarith only [hgamma1])]
    linarith only [hgamma]
  have hAq : A ≤ A ^ (1 - gamma)⁻¹ := by
    calc
      A = A ^ (1 : ℝ) := (Real.rpow_one A).symm
      _ ≤ A ^ (1 - gamma)⁻¹ := Real.rpow_le_rpow_of_exponent_le (hB1.trans hBA) hq
  have hcoef : (cstar⁻¹ * gamma) ^ (1 / 2 : ℝ) = B⁻¹ := by
    dsimp only [B]
    rw [← Real.sqrt_eq_rpow]
    have hrec : cstar⁻¹ * gamma = (cstar * gamma⁻¹)⁻¹ := by field_simp
    rw [hrec, Real.sqrt_inv]
  rw [hcoef]
  calc
    1 = B⁻¹ * B := by field_simp
    _ ≤ B⁻¹ * A := mul_le_mul_of_nonneg_left hBA (inv_nonneg.mpr hB.le)
    _ ≤ B⁻¹ * A ^ (1 - gamma)⁻¹ :=
      mul_le_mul_of_nonneg_left hAq (inv_nonneg.mpr hB.le)

theorem sq_div_intrinsicScale_le_displacementMinScale
    {nu cstar gamma t r : ℝ} (hnu : 0 < nu) (hcstar : 0 < cstar)
    (hgamma : 0 < gamma) (hgamma1 : gamma < 1) (hgc : gamma ≤ cstar)
    (ht : 0 < t) (hr : intrinsicScale nu cstar gamma t ≤ r) :
    (r / intrinsicScale nu cstar gamma t) ^ (2 : ℕ) ≤
      min (r ^ (2 : ℕ) / (nu * t))
        ((cstar⁻¹ * gamma) ^ (1 / 2 : ℝ) *
          (r ^ (2 - gamma) / t) ^ (1 - gamma)⁻¹) := by
  let R := intrinsicScale nu cstar gamma t
  have hR : 0 < R := intrinsicScale_pos hnu hcstar hgamma ht
  have hr0 : 0 < r := hR.trans_le hr
  have hdiff := mul_le_intrinsicScale_sq hnu hcstar hgamma (by linarith only [hgamma1]) ht
  apply le_min
  · rw [div_pow]
    rw [div_le_div_iff₀ (by positivity : 0 < R ^ (2 : ℕ)) (by positivity : 0 < nu * t)]
    exact mul_le_mul_of_nonneg_left hdiff (sq_nonneg r)
  · have hbase := one_le_anomalous_intrinsic hnu hcstar hgamma hgamma1 hgc ht
    have hratio : 1 ≤ r / R := (one_le_div hR).2 hr
    have hexp : (2 : ℝ) ≤ (2 - gamma) * (1 - gamma)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by linarith only [hgamma1])]
      linarith only [hgamma]
    have hratioPow : (r / R) ^ (2 : ℕ) ≤
        (r / R) ^ ((2 - gamma) * (1 - gamma)⁻¹) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hratio hexp
    have hfactor : r ^ (2 - gamma) / t =
        (r / R) ^ (2 - gamma) * (R ^ (2 - gamma) / t) := by
      rw [Real.div_rpow hr0.le hR.le]
      field_simp
    have hpowfactor : ((r / R) ^ (2 - gamma) * (R ^ (2 - gamma) / t)) ^
        (1 - gamma)⁻¹ =
        ((r / R) ^ (2 - gamma)) ^ (1 - gamma)⁻¹ *
          (R ^ (2 - gamma) / t) ^ (1 - gamma)⁻¹ :=
      Real.mul_rpow (Real.rpow_nonneg (by positivity) _)
        (div_nonneg (Real.rpow_nonneg hR.le _) ht.le)
    calc
      (r / R) ^ (2 : ℕ) ≤ (r / R) ^ ((2 - gamma) * (1 - gamma)⁻¹) := hratioPow
      _ = ((r / R) ^ (2 - gamma)) ^ (1 - gamma)⁻¹ := by
        rw [← Real.rpow_mul (by positivity)]
      _ ≤ ((r / R) ^ (2 - gamma)) ^ (1 - gamma)⁻¹ *
          ((cstar⁻¹ * gamma) ^ (1 / 2 : ℝ) *
            (R ^ (2 - gamma) / t) ^ (1 - gamma)⁻¹) := by
        nth_rewrite 1 [← mul_one (((r / R) ^ (2 - gamma)) ^ (1 - gamma)⁻¹)]
        exact mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg (by positivity) _)
      _ = (cstar⁻¹ * gamma) ^ (1 / 2 : ℝ) *
          (r ^ (2 - gamma) / t) ^ (1 - gamma)⁻¹ := by
        rw [hfactor, hpowfactor]
        ring

end

end Algsuperdiff.Section5.Provider
