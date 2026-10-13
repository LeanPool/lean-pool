/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.Step1Assembly

/-!
# SharpGlobalFrame

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The retained global frame in the upper Step-1 coefficient

The upper potential load contains a product of reciprocal running diffusivities
at the observation index and at the fine cube scale.  Applying the growth
branch of the induction window at both indices retains the factor `3^(-gamma *
(i - j))`.  After the Whitney-scale and observation-endpoint specializations,
this internal frame supplies the global `3^(-gamma * (m - n))` factor printed
in ABK26.  A ratio-only comparison between the two diffusivities loses this
factor.

These are internal coefficient estimates.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open HCPolySupport
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-- The reciprocal running diffusivity bounded from the growth branch of the
induction window at one scale. -/
theorem sigmaBar_inv_le_growth_branch
    (M : ABKModel d) {m₀ : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m₀ E)
    {j : ℤ} (hj : j ≤ m₀) :
    (Annealed.sigmaBar M j : ℝ)⁻¹ ≤
      2 * Real.sqrt ((Disorder.cstar M)⁻¹ * M.gamma) *
        (3 : ℝ) ^ (-(M.gamma * (j : ℝ))) := by
  have hsigma : 0 < (Annealed.sigmaBar M j : ℝ) :=
    (Annealed.sigmaBar M j).2
  have hc : 0 < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hcg : 0 < Disorder.cstar M * M.gamma⁻¹ :=
    mul_pos hc (inv_pos.mpr hg)
  have hpow : 0 < (3 : ℝ) ^ (M.gamma * (j : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hwindow := (hS.1 j hj).1
  have hbranch :
      (1 / 4 : ℝ) *
          (Disorder.cstar M * M.gamma⁻¹ *
            (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) ≤
        (Annealed.sigmaBar M j : ℝ) ^ 2 :=
    (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)).trans hwindow
  let t : ℝ := (1 / 2) * Real.sqrt (Disorder.cstar M * M.gamma⁻¹) *
    (3 : ℝ) ^ (M.gamma * (j : ℝ))
  have ht : 0 < t := by
    dsimp only [t]
    positivity
  have hpowTwo : ((3 : ℝ) ^ (M.gamma * (j : ℝ))) ^ 2 =
      (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) := by
    rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have htTwo : t ^ 2 =
      (1 / 4 : ℝ) *
        (Disorder.cstar M * M.gamma⁻¹ *
          (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) := by
    have hsqrt : Real.sqrt (Disorder.cstar M * M.gamma⁻¹) ^ 2 =
        Disorder.cstar M * M.gamma⁻¹ := Real.sq_sqrt hcg.le
    calc
      t ^ 2 = (1 / 4 : ℝ) *
          (Real.sqrt (Disorder.cstar M * M.gamma⁻¹) ^ 2 *
            ((3 : ℝ) ^ (M.gamma * (j : ℝ))) ^ 2) := by
        dsimp only [t]
        ring
      _ = (1 / 4 : ℝ) *
          (Disorder.cstar M * M.gamma⁻¹ *
            (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) := by
        rw [hsqrt, hpowTwo]
  have htle : t ≤ (Annealed.sigmaBar M j : ℝ) := by
    apply (sq_le_sq₀ ht.le hsigma.le).mp
    rw [htTwo]
    exact hbranch
  have hinv : (Annealed.sigmaBar M j : ℝ)⁻¹ ≤ t⁻¹ :=
    (inv_le_inv₀ hsigma ht).2 htle
  have htInv : t⁻¹ =
      2 * Real.sqrt ((Disorder.cstar M)⁻¹ * M.gamma) *
        (3 : ℝ) ^ (-(M.gamma * (j : ℝ))) := by
    have hsqrtInv :
        (Real.sqrt (Disorder.cstar M * M.gamma⁻¹))⁻¹ =
          Real.sqrt ((Disorder.cstar M)⁻¹ * M.gamma) := by
      rw [← Real.sqrt_inv, mul_inv, inv_inv]
    dsimp only [t]
    rw [mul_inv, mul_inv, hsqrtInv,
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rwa [htInv] at hinv

/-- Applying the preceding growth estimate at both indices retains the global
depth frame on the wave coefficient. -/
theorem sigmaBar_inv_mul_sigmaBar_inv_le_framed_wave_coefficient
    (M : ABKModel d) {m₀ i j : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m₀ E)
    (hji : j ≤ i) (hi : i ≤ m₀) :
    (Annealed.sigmaBar M i : ℝ)⁻¹ *
        (Annealed.sigmaBar M j : ℝ)⁻¹ ≤
      4 * (Disorder.cstar M)⁻¹ * M.gamma *
        (3 : ℝ) ^ (-(2 * M.gamma * (j : ℝ))) *
        (3 : ℝ) ^ (-(M.gamma * ((i - j : ℤ) : ℝ))) := by
  have hiBound := sigmaBar_inv_le_growth_branch M hS hi
  have hjBound := sigmaBar_inv_le_growth_branch M hS (hji.trans hi)
  have hjInv : 0 ≤ (Annealed.sigmaBar M j : ℝ)⁻¹ :=
    (inv_pos.mpr (Annealed.sigmaBar M j).2).le
  have hiRhs : 0 ≤
      2 * Real.sqrt ((Disorder.cstar M)⁻¹ * M.gamma) *
        (3 : ℝ) ^ (-(M.gamma * (i : ℝ))) := by positivity
  have hmul := mul_le_mul hiBound hjBound hjInv hiRhs
  refine hmul.trans (le_of_eq ?_)
  have hsqrt :
      Real.sqrt ((Disorder.cstar M)⁻¹ * M.gamma) *
          Real.sqrt ((Disorder.cstar M)⁻¹ * M.gamma) =
        (Disorder.cstar M)⁻¹ * M.gamma :=
    Real.mul_self_sqrt
      (mul_nonneg
        (inv_nonneg.mpr (Disorder.cstar_characterization M).1.le)
        M.shellPrefix.gamma_pos.le)
  have hexponent :
      -(M.gamma * (i : ℝ)) + -(M.gamma * (j : ℝ)) =
        -(2 * M.gamma * (j : ℝ)) +
          -(M.gamma * ((i - j : ℤ) : ℝ)) := by
    push_cast
    ring
  calc
    (2 * Real.sqrt ((Disorder.cstar M)⁻¹ * M.gamma) *
          (3 : ℝ) ^ (-(M.gamma * (i : ℝ)))) *
        (2 * Real.sqrt ((Disorder.cstar M)⁻¹ * M.gamma) *
          (3 : ℝ) ^ (-(M.gamma * (j : ℝ)))) =
      4 *
        (Real.sqrt ((Disorder.cstar M)⁻¹ * M.gamma) *
          Real.sqrt ((Disorder.cstar M)⁻¹ * M.gamma)) *
        ((3 : ℝ) ^ (-(M.gamma * (i : ℝ))) *
          (3 : ℝ) ^ (-(M.gamma * (j : ℝ)))) := by ring
    _ = 4 * ((Disorder.cstar M)⁻¹ * M.gamma) *
        (3 : ℝ) ^
          (-(M.gamma * (i : ℝ)) + -(M.gamma * (j : ℝ))) := by
      rw [hsqrt, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    _ = (4 * (Disorder.cstar M)⁻¹ * M.gamma) *
        (3 : ℝ) ^
          (-(2 * M.gamma * (j : ℝ)) +
            -(M.gamma * ((i - j : ℤ) : ℝ))) := by
      rw [hexponent]
      ring
    _ = (4 * (Disorder.cstar M)⁻¹ * M.gamma) *
        ((3 : ℝ) ^ (-(2 * M.gamma * (j : ℝ))) *
          (3 : ℝ) ^ (-(M.gamma * ((i - j : ℤ) : ℝ)))) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    _ = 4 * (Disorder.cstar M)⁻¹ * M.gamma *
        (3 : ℝ) ^ (-(2 * M.gamma * (j : ℝ))) *
        (3 : ℝ) ^ (-(M.gamma * ((i - j : ℤ) : ℝ))) := by ring


end

end Algsuperdiff.Section3.Provider.Multiscale
