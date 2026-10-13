/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.SecondTermMoment

/-!
# PerCubeGaugeBounds

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 5's per-cube evaluation: the gauge bounds

## What this module supplies

The proved per-cube moments (`PerCubeFirstThird`, `SecondTermMoment`) carry
SYMBOLIC majorants: products of the Step-4 bullets' own constants, `σ`-gauges
and `3^{γ·}` weights.  Step 5's evaluation needs them read against the anchor's
own scalar, so each symbolic ingredient must be converted into `(dimension,
c⋆)`-constants times powers of `γ`, `s`, `q` and `3^{γ(m−j)}`.  This module
performs exactly those conversions, and nothing else:

1. **The geometric constants, uniformized.**  `fullGradConst` and
   `deepGradConst` both carry the `γ`-dependent factor `(1 − 3^{γ−1})^{-1}`;
   `SecondTermArithmetic.inv_one_sub_rpow_three_gamma_le` prices it at `3`, so
   both become dimensional.
2. **The `λ`-slot majorant, factored.**  `lambdaSlotMajorant` is
   `σ_{j−1}^{-1} · lambdaSlotFactor`, and the factor is bounded by an absolute
   constant on the anchor's own moment range `r ≤ γ^{-1}`: the printed
   `q³ e^{−C^{-1}γ^{-1}}` of bullet (B5)'s moment conversion is `O(1)` there,
   by `SecondTermArithmetic.pow_mul_exp_neg_inv_le`.
3. **The four `σ` gauge facts**, packaged at one constant: bullet (B3) at the
   (B5) index `j−1` and at the index `m`, bullet (B1), and the `σ_{j−2}/σ_{j−1}`
   reconciliation.

## References

* ABK26, `l.bounds.mathcal.E.aL`, Step 4 bullets (B1)/(B3)/(B5)/(B6a).
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section4.Provider.Annular

noncomputable section

variable {d : ℕ}

/-- The prefix spelling `Real.rpow x y` and the notation `x ^ y` are the same
term.  Local re-derivation of `Step5GeometricClosure`'s `private
rpowBridge`. -/
theorem rpowBridgeGauge (x y : ℝ) : Real.rpow x y = x ^ y := rfl

/-! ## 1. The geometric constants, uniformized -/

/-- The dimensional bound on `GradBottomLayer.fullGradConst`. -/
def fullGradBound (d : ℕ) : ℝ := gammaTriangleConst 2 * ((bottomGradConst d + 3) * 3)

/-- The absolute bound on `GradSlotMoment.deepGradConst`. -/
def deepGradBound : ℝ := gammaTriangleConst 2 * 3

theorem fullGradBound_pos (d : ℕ) : 0 < fullGradBound d := by
  have h1 : (0 : ℝ) < gammaTriangleConst 2 := gammaTriangleConst_pos (σ := (2 : ℝ))
  have h2 : (0 : ℝ) ≤ bottomGradConst d := bottomGradConst_nonneg d
  rw [fullGradBound]
  positivity

theorem deepGradBound_pos : (0 : ℝ) < deepGradBound := by
  have h1 : (0 : ℝ) < gammaTriangleConst 2 := gammaTriangleConst_pos (σ := (2 : ℝ))
  rw [deepGradBound]
  positivity

theorem fullGradConst_le (M : ABKModel d) (hgam : M.gamma ≤ 1 / 2) :
    fullGradConst M ≤ fullGradBound d := by
  have h := inv_one_sub_rpow_three_gamma_le (g := M.gamma) hgam
  have hb : (0 : ℝ) ≤ bottomGradConst d + 3 := by
    have := bottomGradConst_nonneg d
    linarith only [this]
  have hct : (0 : ℝ) < gammaTriangleConst 2 := gammaTriangleConst_pos (σ := (2 : ℝ))
  rw [fullGradConst, fullGradBase, fullGradBound]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h hb) hct.le

theorem deepGradConst_le (M : ABKModel d) (hgam : M.gamma ≤ 1 / 2) :
    deepGradConst M ≤ deepGradBound := by
  have h := inv_one_sub_rpow_three_gamma_le (g := M.gamma) hgam
  have hct : (0 : ℝ) < gammaTriangleConst 2 := gammaTriangleConst_pos (σ := (2 : ℝ))
  rw [deepGradConst, deepGradBound]
  exact mul_le_mul_of_nonneg_left h hct.le

/-! ## 2. The `λ`-slot majorant, factored -/

/-- The `σ`-free factor of `lambdaSlotMajorant`. -/
def lambdaSlotFactor (d : ℕ) (M : ABKModel d) (E r : ℝ) : ℝ :=
  lambdaUpscaleConst d * Support.cgEllipLowerConstant d +
    gammaMomentConst (1 / 3) * r ^ ((1 / 3 : ℝ))⁻¹ *
      (lambdaUpscaleConst d * lambdaMaxOrliczConst d * Proportion.cgTailScale M E)

/-- **The `λ`-slot majorant is `σ_{j−1}^{-1}` times a `σ`-free factor.** -/
theorem lambdaSlotMajorant_eq_mul (d : ℕ) (M : ABKModel d) (E : ℝ) (j : ℤ) (r : ℝ) :
    lambdaSlotMajorant d M E j r =
      ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ * lambdaSlotFactor d M E r := by
  rw [lambdaSlotMajorant, gammaMomentBound, lambdaSlotFactor]
  ring

/-- The absolute bound on the `σ`-free factor, at the budget `E`. -/
def lambdaSlotFactorBound (d : ℕ) (E : ℝ) : ℝ :=
  lambdaUpscaleConst d * Support.cgEllipLowerConstant d +
    gammaMomentConst (1 / 3) *
        ((Nat.factorial 3 : ℝ) /
          ((Support.cgEllipLowerConstant d)⁻¹ * (E⁻¹) ^ 2) ^ 3) *
      (lambdaUpscaleConst d * lambdaMaxOrliczConst d)

theorem lambdaSlotFactorBound_pos (d : ℕ) {E : ℝ} (hE : 0 < E) :
    0 < lambdaSlotFactorBound d E := by
  have h1 : (0 : ℝ) < lambdaUpscaleConst d := lambdaUpscaleConst_pos d
  have h2 : (0 : ℝ) < lambdaMaxOrliczConst d := lambdaMaxOrliczConst_pos d
  have h3 : (0 : ℝ) < Support.cgEllipLowerConstant d := Support.cgEllipLowerConstant_pos d
  have h4 : (0 : ℝ) < gammaMomentConst (1 / 3) := gammaMomentConst_pos (by norm_num)
  have h5 : (0 : ℝ) < (Support.cgEllipLowerConstant d)⁻¹ * (E⁻¹) ^ 2 := by positivity
  have h6 : (0 : ℝ) < (Nat.factorial 3 : ℝ) := by norm_num
  rw [lambdaSlotFactorBound]
  positivity

/-- **Bullet (B5)'s `q³ e^{−C^{-1}γ^{-1}}` is `O(1)` on the printed range.**

On the anchor's own moment range `r ≤ γ^{-1}` -- which its `p`-range
`p ≤ C^{-1}γ^{-1}s` delivers -- the `σ`-free factor of the (B5) majorant is at
most an absolute constant.  No `p`-restriction beyond the printed one is used. -/
theorem lambdaSlotFactor_le (d : ℕ) (M : ABKModel d) {E r : ℝ} (hE : 0 < E) (hr : 0 ≤ r)
    (hrg : r ≤ M.gamma⁻¹) : lambdaSlotFactor d M E r ≤ lambdaSlotFactorBound d E := by
  have hg0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hK : (0 : ℝ) < Support.cgEllipLowerConstant d := Support.cgEllipLowerConstant_pos d
  have ha : (0 : ℝ) < (Support.cgEllipLowerConstant d)⁻¹ * (E⁻¹) ^ 2 := by positivity
  have htail : Proportion.cgTailScale M E =
      Real.exp (-((Support.cgEllipLowerConstant d)⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹)) := rfl
  have hrn : r ^ ((1 / 3 : ℝ))⁻¹ = r ^ (3 : ℕ) := by
    rw [show ((1 / 3 : ℝ))⁻¹ = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hbound := pow_mul_exp_neg_inv_le (a := (Support.cgEllipLowerConstant d)⁻¹ * (E⁻¹) ^ 2)
    (g := M.gamma) (y := r) 3 ha hg0 hr hrg
  have hcoef : (0 : ℝ) ≤ gammaMomentConst (1 / 3) *
      (lambdaUpscaleConst d * lambdaMaxOrliczConst d) :=
    mul_nonneg (gammaMomentConst_pos (by norm_num)).le
      (mul_nonneg (lambdaUpscaleConst_pos d).le (lambdaMaxOrliczConst_pos d).le)
  have hstep := mul_le_mul_of_nonneg_left hbound hcoef
  rw [lambdaSlotFactor, lambdaSlotFactorBound, htail, hrn]
  have hL : gammaMomentConst (1 / 3) * r ^ (3 : ℕ) *
      (lambdaUpscaleConst d * lambdaMaxOrliczConst d *
        Real.exp (-((Support.cgEllipLowerConstant d)⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹))) =
      gammaMomentConst (1 / 3) * (lambdaUpscaleConst d * lambdaMaxOrliczConst d) *
        (r ^ (3 : ℕ) *
          Real.exp (-((Support.cgEllipLowerConstant d)⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹))) := by
    ring
  have hR : gammaMomentConst (1 / 3) *
      ((Nat.factorial 3 : ℝ) /
        ((Support.cgEllipLowerConstant d)⁻¹ * (E⁻¹) ^ 2) ^ 3) *
      (lambdaUpscaleConst d * lambdaMaxOrliczConst d) =
      gammaMomentConst (1 / 3) * (lambdaUpscaleConst d * lambdaMaxOrliczConst d) *
        ((Nat.factorial 3 : ℝ) /
          ((Support.cgEllipLowerConstant d)⁻¹ * (E⁻¹) ^ 2) ^ 3) := by
    ring
  linarith only [hstep, hL, hR]

/-! ## 3. The four `σ` gauge facts, packaged -/

/-- **The gauge package.**

At one constant, in the printed regime alone: bullet (B3) at the (B5) index
`j−1` (constant `16`, `SigmaBarLandmark`), bullet (B3) at the index `m`
(constant `4`, `StepFourSigmaBar` read at `m+2`), bullet (B1), and the
`σ_{j−2}/σ_{j−1}` reconciliation. -/
theorem exists_sigmaBar_gaugePackage (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        (∀ j : ℤ, (3 : ℝ) ^ (M.gamma * (j : ℝ)) *
            ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ ≤
              16 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma)) ∧
        (∀ m : ℤ, (3 : ℝ) ^ (M.gamma * (m : ℝ)) * ((Annealed.sigmaBar M m : ℝ))⁻¹ ≤
            4 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma)) ∧
        (∀ m j : ℤ, j - 2 ≤ m →
            ((Annealed.sigmaBar M m : ℝ))⁻¹ * (Annealed.sigmaBar M (j - 2) : ℝ) ≤ 4) ∧
        (∀ j : ℤ, (Annealed.sigmaBar M (j - 2) : ℝ) *
            ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ ≤ 4) := by
  obtain ⟨C1, hC1, hB3one⟩ := exists_rpow_gamma_mul_inv_sigmaBar_sub_one_le d
  obtain ⟨C2, hC2, hB3two⟩ := exists_rpow_gamma_mul_inv_sigmaBar_sub_two_le d
  obtain ⟨C3, hC3, hB1⟩ := exists_inv_sigmaBar_mul_sigmaBar_sub_two_le_four d
  obtain ⟨C4, hC4, hIdx⟩ := exists_inv_sigmaBar_sub_one_le_four_mul_inv_sigmaBar_sub_two d
  refine ⟨max (max C1 C2) (max C3 C4), ?_, ?_⟩
  · exact lt_of_lt_of_le hC1 (le_trans (le_max_left C1 C2) (le_max_left _ _))
  intro M hreg
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have h1 := hB3one M (gamma_regime_mono hC1
    (le_trans (le_max_left C1 C2) (le_max_left _ _)) hcs0.le hreg)
  have h2 := hB3two M (gamma_regime_mono hC2
    (le_trans (le_max_right C1 C2) (le_max_left _ _)) hcs0.le hreg)
  have h3 := hB1 M (gamma_regime_mono hC3
    (le_trans (le_max_left C3 C4) (le_max_right _ _)) hcs0.le hreg)
  have h4 := hIdx M (gamma_regime_mono hC4
    (le_trans (le_max_right C3 C4) (le_max_right _ _)) hcs0.le hreg)
  refine ⟨h1, ?_, h3, ?_⟩
  · intro m
    have hshift : (m + 2 : ℤ) - 2 = m := by ring
    have hm2 := h2 (m + 2)
    rw [hshift] at hm2
    have hmono : (3 : ℝ) ^ (M.gamma * (m : ℝ)) ≤ (3 : ℝ) ^ (M.gamma * ((m + 2 : ℤ) : ℝ)) := by
      refine rpow_three_le_rpow_three ?_
      have hcast : ((m + 2 : ℤ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
      rw [hcast]
      have h := mul_le_mul_of_nonneg_left (by linarith only [] : (m : ℝ) ≤ (m : ℝ) + 2)
        hgam0.le
      linarith only [h]
    have hinv : (0 : ℝ) ≤ ((Annealed.sigmaBar M m : ℝ))⁻¹ :=
      (inv_pos.mpr (Annealed.sigmaBar M m).2).le
    exact le_trans (mul_le_mul_of_nonneg_right hmono hinv) hm2
  · intro j
    have hpos : (0 : ℝ) < (Annealed.sigmaBar M (j - 2) : ℝ) :=
      (Annealed.sigmaBar M (j - 2)).2
    have hstep := mul_le_mul_of_nonneg_left (h4 j) hpos.le
    have hid : (Annealed.sigmaBar M (j - 2) : ℝ) *
        (4 * ((Annealed.sigmaBar M (j - 2) : ℝ))⁻¹) = 4 := by
      field_simp
    have hid2 : (Annealed.sigmaBar M (j - 2) : ℝ) *
        ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ =
        (Annealed.sigmaBar M (j - 2) : ℝ) * ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ := rfl
    linarith only [hstep, hid, hid2]

end

end Algsuperdiff.Section4.Provider.BoundsEaL
