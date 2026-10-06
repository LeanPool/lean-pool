/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianFactorBound

/-!
# Algebra of the Gaussian cutoff errors

The four cutoff errors reduce to a cubic Gaussian tail after the main
Carleman term is absorbed (`eq:bu-gaussian-collar`).
-/

public section


noncomputable section

namespace ESS

/-- The shell, late-time, and initial-time estimates imply a uniform
polynomial multiple of the radial Gaussian tail. -/
theorem buGaussian_error_assembly_bound
    {c₀ k₀ k₁ Cacc a ρ T I E shell0 shell1 SM SG LM IM R F ε : ℝ}
    (hc₀ : 0 ≤ c₀) (hk₀ : 0 ≤ k₀) (hk₁ : 0 ≤ k₁)
    (hCacc : 0 ≤ Cacc) (ha : 0 ≤ a) (hρ : 0 ≤ ρ) (hT : 0 ≤ T)
    (hI : I ≤ 2 * c₀ * E)
    (hE : E = 8 * shell0 ^ 2 * SM + 8 * shell1 ^ 2 * SG +
      4096 * LM + (256 / ε ^ 2) * IM)
    (hshell0 : 0 ≤ shell0) (hshell0le : shell0 ≤ k₀)
    (hshell1 : 0 ≤ shell1) (hshell1le : shell1 ≤ k₁)
    (hSM0 : 0 ≤ SM) (hSG0 : 0 ≤ SG)
    (hSM : SM ≤ 24 * ρ ^ 3 * T)
    (hSG : SG ≤ F * R) (hF : F ≤ Cacc * (1 + a))
    (hR0 : 0 ≤ R) (hR : R ≤ 24 * ρ ^ 3 * T)
    (hLM : LM ≤ 12 * ρ ^ 3 * T)
    (hIM : (256 / ε ^ 2) * IM ≤ T) :
    I ≤ 2 * c₀ * (192 * (k₀ ^ 2 + k₁ ^ 2 * Cacc) + 49153) *
      ((1 + a) * (1 + ρ) ^ 3 * T) := by
  let P : ℝ := (1 + a) * (1 + ρ) ^ 3
  obtain ⟨hPone, hρP, hρP'⟩ := buGaussian_polynomial_domination ha hρ
  have hρPT : ρ ^ 3 * T ≤ P * T :=
    mul_le_mul_of_nonneg_right hρP hT
  have hρPT' : (1 + a) * ρ ^ 3 * T ≤ P * T :=
    mul_le_mul_of_nonneg_right hρP' hT
  have hSG' : SG ≤ Cacc * (1 + a) * (24 * ρ ^ 3 * T) :=
    buGaussian_shell_gradient_integral_bound hSG hF hR0 hR
      (mul_nonneg hCacc (by linarith only [ha] : 0 ≤ 1 + a))
  have hs0sq : shell0 ^ 2 ≤ k₀ ^ 2 :=
    (sq_le_sq₀ hshell0 hk₀).2 hshell0le
  have hs1sq : shell1 ^ 2 ≤ k₁ ^ 2 :=
    (sq_le_sq₀ hshell1 hk₁).2 hshell1le
  have hTerm0 : 8 * shell0 ^ 2 * SM ≤ 192 * k₀ ^ 2 * (P * T) := by
    calc
      _ ≤ 8 * k₀ ^ 2 * SM := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs0sq (by norm_num)) hSM0
      _ ≤ 8 * k₀ ^ 2 * (24 * ρ ^ 3 * T) :=
        mul_le_mul_of_nonneg_left hSM (by positivity)
      _ ≤ 192 * k₀ ^ 2 * (P * T) := by
        have hmul := mul_le_mul_of_nonneg_left hρPT
          (by positivity : 0 ≤ 192 * k₀ ^ 2)
        nlinarith only [hmul]
  have hTerm1 : 8 * shell1 ^ 2 * SG ≤
      192 * k₁ ^ 2 * Cacc * (P * T) := by
    calc
      _ ≤ 8 * k₁ ^ 2 * SG := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs1sq (by norm_num)) hSG0
      _ ≤ 8 * k₁ ^ 2 * (Cacc * (1 + a) * (24 * ρ ^ 3 * T)) :=
        mul_le_mul_of_nonneg_left hSG' (by positivity)
      _ ≤ 192 * k₁ ^ 2 * Cacc * (P * T) := by
        have hmul := mul_le_mul_of_nonneg_left hρPT'
          (by positivity : 0 ≤ 192 * k₁ ^ 2 * Cacc)
        nlinarith only [hmul]
  have hTermLate : 4096 * LM ≤ 49152 * (P * T) := by
    have hmul := mul_le_mul_of_nonneg_left hLM
      (by norm_num : (0 : ℝ) ≤ 4096)
    have hpoly := mul_le_mul_of_nonneg_left hρPT
      (by norm_num : (0 : ℝ) ≤ 49152)
    nlinarith only [hmul, hpoly]
  have hTermInit : (256 / ε ^ 2) * IM ≤ P * T := by
    have hmul := mul_le_mul_of_nonneg_right hPone hT
    exact hIM.trans (by simpa only [one_mul] using hmul)
  have hErr : E ≤ (192 * (k₀ ^ 2 + k₁ ^ 2 * Cacc) + 49153) *
      (P * T) := by
    rw [hE]
    nlinarith only [hTerm0, hTerm1, hTermLate, hTermInit]
  have hcoef : 0 ≤ 2 * c₀ := by positivity
  have hmul := mul_le_mul_of_nonneg_left hErr hcoef
  nlinarith only [hI, hmul]

/-- Removing the fixed lower Gaussian weight from the averaging box. -/
theorem buGaussian_unweight_bound {D I c P T : ℝ}
    (hMass : Real.exp (-(3 / 2 : ℝ)) * D ≤ I)
    (hI : I ≤ 2 * c * P * T) :
    D ≤ (2 * Real.exp (3 / 2) * c * P) * T := by
  have hcancel : Real.exp (3 / 2 : ℝ) * Real.exp (-(3 / 2 : ℝ)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  calc
    D = Real.exp (3 / 2 : ℝ) * (Real.exp (-(3 / 2 : ℝ)) * D) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ Real.exp (3 / 2 : ℝ) * I :=
      mul_le_mul_of_nonneg_left hMass (Real.exp_nonneg _)
    _ ≤ Real.exp (3 / 2 : ℝ) * (2 * c * P * T) :=
      mul_le_mul_of_nonneg_left hI (Real.exp_nonneg _)
    _ = (2 * Real.exp (3 / 2) * c * P) * T := by ring_nf

/-- The polynomial collar loss is absorbed into the radial exponential,
and the scaled distance yields the physical height decay. -/
theorem buGaussian_final_scalar_bound
    {β H c P Ctail Ccore E T ρ a x₃ t D I : ℝ}
    (hβ : 0 < β) (hH : 0 < H) (hρone : 1 ≤ ρ)
    (ha : a = (β / H) * ρ ^ 2)
    (hT : T = E * Real.exp (-2 * β * ρ ^ 2))
    (hCtail : Ctail = 64 * (1 + β / (2 * H)) /
      (β / 2) ^ 2 / Real.sqrt β)
    (hCcore : Ccore = 2 * Real.exp (3 / 2) * c * P * Ctail)
    (hHeight : x₃ ^ 2 / (12 * t) ≤ ρ ^ 2)
    (hMass : Real.exp (-(3 / 2 : ℝ)) * D ≤ I)
    (hI : I ≤ 2 * c * P * ((1 + a) * (1 + ρ) ^ 3 * T))
    (hc : 0 ≤ c) (hP : 0 ≤ P) (hE : 0 ≤ E) :
    D ≤ Ccore * E * Real.exp (-(β * x₃ ^ 2) / (12 * t)) := by
  have htail : (1 + a) * (1 + ρ) ^ 3 *
      Real.exp (-2 * β * ρ ^ 2) ≤
      Ctail * Real.exp (-β * ρ ^ 2) := by
    rw [ha, hCtail]
    exact buGaussian_polynomial_tail_bound_three hβ hH hρone
  have hweighted : ((1 + a) * (1 + ρ) ^ 3 * T) ≤
      Ctail * E * Real.exp (-β * ρ ^ 2) := by
    calc
      _ = E * ((1 + a) * (1 + ρ) ^ 3 *
          Real.exp (-2 * β * ρ ^ 2)) := by rw [hT]; ring_nf
      _ ≤ E * (Ctail * Real.exp (-β * ρ ^ 2)) :=
        mul_le_mul_of_nonneg_left htail hE
      _ = _ := by ring_nf
  have hcoef : 0 ≤ 2 * Real.exp (3 / 2 : ℝ) * c * P := by positivity
  have hD := buGaussian_unweight_bound hMass hI
  have hmul := mul_le_mul_of_nonneg_left hweighted hcoef
  have hDtail : D ≤ Ccore * E * Real.exp (-β * ρ ^ 2) := by
    calc
      D ≤ (2 * Real.exp (3 / 2) * c * P) *
          ((1 + a) * (1 + ρ) ^ 3 * T) := hD
      _ ≤ (2 * Real.exp (3 / 2) * c * P) *
          (Ctail * E * Real.exp (-β * ρ ^ 2)) := hmul
      _ = Ccore * E * Real.exp (-β * ρ ^ 2) := by rw [hCcore]; ring_nf
  have hExp : Real.exp (-β * ρ ^ 2) ≤
      Real.exp (-(β * x₃ ^ 2) / (12 * t)) := by
    apply Real.exp_le_exp.mpr
    have hmulHeight := mul_le_mul_of_nonneg_left hHeight hβ.le
    have hneg := neg_le_neg hmulHeight
    convert hneg using 1 <;> ring_nf
  have hCtailNonneg : 0 ≤ Ctail := by rw [hCtail]; positivity
  have hCcoreNonneg : 0 ≤ Ccore := by
    rw [hCcore]
    positivity
  exact hDtail.trans
    (mul_le_mul_of_nonneg_left hExp (mul_nonneg hCcoreNonneg hE))

end ESS
