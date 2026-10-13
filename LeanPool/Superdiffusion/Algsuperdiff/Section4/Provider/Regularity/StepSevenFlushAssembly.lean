/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenFlushLegBounds
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccGradient
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccFinalInterior

/-!
# StepSevenFlushAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The two exponent facts -/

/-- `3^{s(n+2)}·3^{(n+3)/4} ≤ 3^{m/2}` at `s = 1/4`, for `n+3 ≤ m` — item 1(b),
proved. -/
theorem flush_exponent_gag {n m : ℤ} (hnm : n + 3 ≤ m) :
    Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) *
        (3 : ℝ) ^ ((((n + 3 : ℤ)) : ℝ) / 4) ≤
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) := by
  have hm : ((n : ℝ) + 3) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hcomb : Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) *
      (3 : ℝ) ^ ((((n + 3 : ℤ)) : ℝ) / 4) =
      Real.rpow (3 : ℝ)
        (stepOneS * (((n + 2 : ℤ)) : ℝ) + (((n + 3 : ℤ)) : ℝ) / 4) :=
    (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
  rw [hcomb]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  rw [show stepOneS = (1 / 4 : ℝ) from rfl]
  push_cast
  linarith only [hm]

/-- `3^{-(n+2)}·3^{(1+s)n}·3^{(n+3)/4} ≤ 3^{m/2}` at `s = 1/4`, for `n+3 ≤ m`. -/
theorem flush_exponent_gag_low {n m : ℤ} (hnm : n + 3 ≤ m) :
    Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
        Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) *
        (3 : ℝ) ^ ((((n + 3 : ℤ)) : ℝ) / 4) ≤
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) := by
  have hm : ((n : ℝ) + 3) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hc1 : Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
      Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) =
      Real.rpow (3 : ℝ)
        (-(((n + 2 : ℤ)) : ℝ) + (1 + stepOneS) * ((n : ℤ) : ℝ)) :=
    (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
  have hc2 : Real.rpow (3 : ℝ)
      (-(((n + 2 : ℤ)) : ℝ) + (1 + stepOneS) * ((n : ℤ) : ℝ)) *
      (3 : ℝ) ^ ((((n + 3 : ℤ)) : ℝ) / 4) =
      Real.rpow (3 : ℝ)
        (-(((n + 2 : ℤ)) : ℝ) + (1 + stepOneS) * ((n : ℤ) : ℝ) +
          (((n + 3 : ℤ)) : ℝ) / 4) :=
    (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
  rw [hc1, hc2]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  rw [show stepOneS = (1 / 4 : ℝ) from rfl]
  push_cast
  linarith only [hm]

/-- `3^{-(n+2)}·3^{n} = 3^{-2} ≤ 1`. -/
theorem flush_exponent_flat {n : ℤ} :
    Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
        Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) ≤ 1 := by
  have hc : Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
      Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) =
      Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ) + ((n : ℤ) : ℝ)) :=
    (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
  have h : Real.rpow (3 : ℝ) (0 : ℝ) = 1 := Real.rpow_zero 3
  rw [hc, ← h]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  push_cast
  linarith

/-- The `rpow → zpow` splitting `3^{-(n+2)} = 3·3^{-(n+3)}`. -/
theorem rpow_neg_succ_eq_three_mul {n : ℤ} :
    Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) = 3 * (3 : ℝ) ^ (-(n + 3)) := by
  have h1 : (-(((n + 2 : ℤ)) : ℝ)) = (((-(n + 2) : ℤ)) : ℝ) := by push_cast; ring
  have h2 : Real.rpow (3 : ℝ) (((-(n + 2) : ℤ)) : ℝ) = (3 : ℝ) ^ (-(n + 2) : ℤ) :=
    Real.rpow_intCast 3 (-(n + 2))
  rw [h1, h2, show (-(n + 2) : ℤ) = -(n + 3) + 1 by ring,
    zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
  ring

/-! ## 2. The flush constant -/

/-- The flush branch's `𝐠`-leg constant. -/
def stepSevenFlushCG (d : ℕ) (K2 : ℝ) : ℝ :=
  (64 + 16384 * K2) * stepFourGagliardoConst d stepOneS

/-- The flush branch's `∇h`-leg constant. -/
def stepSevenFlushCH (d : ℕ) (K2 : ℝ) : ℝ :=
  (16 + 4096 * K2) * stepFourGagliardoConst d stepOneS +
    (16 + 4096 * K2 + K2 * (d : ℝ))

theorem stepSevenFlushCG_nonneg (d : ℕ) {K2 : ℝ} (hK2 : 0 ≤ K2) :
    0 ≤ stepSevenFlushCG d K2 := by
  rw [stepSevenFlushCG]
  have h := stepFourGagliardoConst_nonneg d stepOneS
  have h2 : (0 : ℝ) ≤ 64 + 16384 * K2 := by linarith only [hK2]
  exact mul_nonneg h2 h

theorem stepSevenFlushCH_nonneg (d : ℕ) {K2 : ℝ} (hK2 : 0 ≤ K2) :
    0 ≤ stepSevenFlushCH d K2 := by
  rw [stepSevenFlushCH]
  have h := stepFourGagliardoConst_nonneg d stepOneS
  have h2 : (0 : ℝ) ≤ 16 + 4096 * K2 := by linarith only [hK2]
  have h3 : (0 : ℝ) ≤ K2 * (d : ℝ) := mul_nonneg hK2 (Nat.cast_nonneg d)
  have h4 := mul_nonneg h2 h
  linarith only [h2, h3, h4]

/-- The flush branch's `hgrad`-slot constant. -/
def stepSevenFlushCg (d : ℕ) (K1 K2 Cosc : ℝ) : ℝ :=
  Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) * K1 *
    (3 * (1 + K2) * Cosc + 2 * stepSevenFlushCG d K2 + stepSevenFlushCH d K2)

theorem stepSevenFlushCg_nonneg (d : ℕ) {K1 K2 Cosc : ℝ} (hK1 : 0 ≤ K1)
    (hK2 : 0 ≤ K2) (hCosc : 0 ≤ Cosc) : 0 ≤ stepSevenFlushCg d K1 K2 Cosc := by
  rw [stepSevenFlushCg]
  have h0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) :=
    Real.rpow_nonneg (by norm_num) _
  have h1 : (0 : ℝ) ≤ 3 * (1 + K2) * Cosc :=
    mul_nonneg (by linarith only [hK2]) hCosc
  have h2 := stepSevenFlushCG_nonneg d hK2
  have h3 := stepSevenFlushCH_nonneg d hK2
  exact mul_nonneg (mul_nonneg h0 hK1) (by linarith only [h1, h2, h3])

/-! ## 3. The bracket pricing -/

/-- **The flush bracket, priced onto the display carriers.** -/
theorem flushBracket_le {m n : ℤ} {z : Vec d} {sigma K2 Khol Kh : ℝ}
    (uglob hdat : H1Function (openCubeSet (originCube d m)))
    {gsrc : Vec d → Vec d}
    (hd1 : 1 ≤ d) (hz : z ∈ openCubeSet (originCube d m)) (hnm : n + 3 ≤ m)
    (hsigma : 0 < sigma) (hK2 : 0 ≤ K2) (hKhol : 0 ≤ Khol) (hKh : 0 ≤ Kh)
    (hgHol : Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
      (1 / 2) Khol gsrc)
    (hhHol : Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
      (1 / 2) Kh hdat.grad)
    (hsup : ∀ y ∈ openCubeSet (originCube d m),
      ‖hdat.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) :
    Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
        (eLpNorm (fun y => uglob.toFun y -
            volumeAverage (truncatedWindow z m (n + 3)) uglob.toFun) 2
          (Support.normalizedVolumeMeasureOn (truncatedWindow z m (n + 3)))).toReal +
      Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
        (K2 *
          ((eLpNorm (fun y => uglob.toFun y -
              volumeAverage (truncatedWindow z m (n + 3)) uglob.toFun) 2
            (Support.normalizedVolumeMeasureOn
              (truncatedWindow z m (n + 3)))).toReal +
          (3 : ℝ) ^ n *
            ∑ i' : Fin d,
              (eLpNorm (fun y => hdat.grad y i') 2
                (Support.normalizedVolumeMeasureOn
                  (truncatedWindow z m (n + 3)))).toReal +
          Real.rpow stepOneS (-(6 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
            (eLpNorm hdat.grad 2
              (Support.normalizedVolumeMeasureOn
                (truncatedWindow z m (n + 3)))).toReal +
          Real.rpow stepOneS (-(6 : ℝ)) *
              Real.rpow (3 : ℝ) ((1 + stepOneS) * (n : ℝ)) *
            (Support.normalizedGagliardoESeminormOn (truncatedWindow z m (n + 3))
              stepOneS hdat.grad).toReal +
          Real.rpow stepOneS (-(7 : ℝ)) * sigma⁻¹ *
              Real.rpow (3 : ℝ) ((1 + stepOneS) * (n : ℝ)) *
            (Support.normalizedGagliardoESeminormOn (truncatedWindow z m (n + 3))
              stepOneS gsrc).toReal)) +
      Real.rpow stepOneS (-(3 : ℝ)) * Real.sqrt sigma⁻¹ *
          Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) *
        (Support.normalizedGagliardoESeminormOn (truncatedWindow z m (n + 3))
          stepOneS gsrc).toReal +
      Real.rpow stepOneS (-(2 : ℝ)) * Real.sqrt sigma *
          Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) *
        (Support.normalizedGagliardoESeminormOn (truncatedWindow z m (n + 3))
          stepOneS hdat.grad).toReal +
      Real.rpow stepOneS (-(2 : ℝ)) * Real.sqrt sigma *
        (eLpNorm hdat.grad 2
          (Support.normalizedVolumeMeasureOn
            (truncatedWindow z m (n + 3)))).toReal ≤
    3 * (1 + K2) *
        (Real.sqrt sigma *
          ((3 : ℝ) ^ (-(n + 3)) *
            normalizedL2On (truncatedWindow z m (n + 3))
              (fun y => uglob.toFun y -
                volumeAverage (truncatedWindow z m (n + 3)) uglob.toFun))) +
      stepSevenFlushCG d K2 *
        (Real.sqrt sigma⁻¹ * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol)) +
      stepSevenFlushCH d K2 *
        (Real.sqrt sigma * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) := by
  have hsq0 : (0 : ℝ) ≤ Real.sqrt sigma := Real.sqrt_nonneg _
  have hsqi0 : (0 : ℝ) ≤ Real.sqrt sigma⁻¹ := Real.sqrt_nonneg _
  have hgag0 := stepFourGagliardoConst_nonneg d stepOneS
  have h3m0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  -- the primitive quantities
  set oscE : ℝ := (eLpNorm (fun y => uglob.toFun y -
      volumeAverage (truncatedWindow z m (n + 3)) uglob.toFun) 2
    (Support.normalizedVolumeMeasureOn (truncatedWindow z m (n + 3)))).toReal
    with hoscEdef
  set sumH : ℝ := ∑ i' : Fin d, (eLpNorm (fun y => hdat.grad y i') 2
    (Support.normalizedVolumeMeasureOn (truncatedWindow z m (n + 3)))).toReal
    with hsumHdef
  set flatH : ℝ := (eLpNorm hdat.grad 2
    (Support.normalizedVolumeMeasureOn (truncatedWindow z m (n + 3)))).toReal
    with hflatHdef
  set gagG : ℝ := (Support.normalizedGagliardoESeminormOn
    (truncatedWindow z m (n + 3)) stepOneS gsrc).toReal with hgagGdef
  set gagH : ℝ := (Support.normalizedGagliardoESeminormOn
    (truncatedWindow z m (n + 3)) stepOneS hdat.grad).toReal with hgagHdef
  have hoscE0 : 0 ≤ oscE := ENNReal.toReal_nonneg
  have hsumH0 : 0 ≤ sumH :=
    Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hflatH0 : 0 ≤ flatH := ENNReal.toReal_nonneg
  have hgagG0 : 0 ≤ gagG := ENNReal.toReal_nonneg
  have hgagH0 : 0 ≤ gagH := ENNReal.toReal_nonneg
  -- the primitive bounds
  have hgagGle : gagG ≤ Khol * stepFourGagliardoConst d stepOneS *
      (3 : ℝ) ^ ((((n + 3 : ℤ)) : ℝ) / 4) :=
    gagliardo_window_toReal_le hd1 hz hKhol hgHol
  have hgagHle : gagH ≤ Kh * stepFourGagliardoConst d stepOneS *
      (3 : ℝ) ^ ((((n + 3 : ℤ)) : ℝ) / 4) :=
    gagliardo_window_toReal_le hd1 hz hKh hhHol
  have hflatHle : flatH ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh :=
    eLpNorm_grad_window_le_sup hKh hz hdat hsup
  have hsumHle : sumH ≤ (d : ℝ) * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) :=
    sum_eLpNorm_grad_coord_window_le_sup hKh hz hdat hsup
  -- the oscillation carrier bridge and the scale split
  have hosceq : oscE = normalizedL2On (truncatedWindow z m (n + 3))
      (fun y => uglob.toFun y -
        volumeAverage (truncatedWindow z m (n + 3)) uglob.toFun) := by
    rw [hoscEdef]
    exact oscE_toReal_eq_normalizedL2On hz uglob _
  have hosc0' : 0 ≤ (3 : ℝ) ^ (-(n + 3)) * normalizedL2On
      (truncatedWindow z m (n + 3))
      (fun y => uglob.toFun y -
        volumeAverage (truncatedWindow z m (n + 3)) uglob.toFun) :=
    mul_nonneg (zpow_nonneg (by norm_num) _) (normalizedL2On_nonneg _ _)
  -- T1 and the ℓ1 term: the oscillation legs
  have hT1 : Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) * oscE =
      3 * (Real.sqrt sigma *
        ((3 : ℝ) ^ (-(n + 3)) * normalizedL2On (truncatedWindow z m (n + 3))
          (fun y => uglob.toFun y -
            volumeAverage (truncatedWindow z m (n + 3)) uglob.toFun))) := by
    rw [rpow_neg_succ_eq_three_mul, hosceq]
    ring
  -- the g legs
  have hgagGm : Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) * gagG ≤
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * (Khol * stepFourGagliardoConst d stepOneS) := by
    calc Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) * gagG
        ≤ Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) *
            (Khol * stepFourGagliardoConst d stepOneS *
              (3 : ℝ) ^ ((((n + 3 : ℤ)) : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left hgagGle (Real.rpow_nonneg (by norm_num) _)
      _ = (Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) *
            (3 : ℝ) ^ ((((n + 3 : ℤ)) : ℝ) / 4)) *
            (Khol * stepFourGagliardoConst d stepOneS) := by ring
      _ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) *
            (Khol * stepFourGagliardoConst d stepOneS) :=
          mul_le_mul_of_nonneg_right (flush_exponent_gag hnm)
            (mul_nonneg hKhol hgag0)
  have hgagGlow : Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
      Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) * gagG ≤
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * (Khol * stepFourGagliardoConst d stepOneS) := by
    calc Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
          Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) * gagG
        ≤ Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
            Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) *
            (Khol * stepFourGagliardoConst d stepOneS *
              (3 : ℝ) ^ ((((n + 3 : ℤ)) : ℝ) / 4)) := by
          refine mul_le_mul_of_nonneg_left hgagGle ?_
          exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
            (Real.rpow_nonneg (by norm_num) _)
      _ = (Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
            Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) *
            (3 : ℝ) ^ ((((n + 3 : ℤ)) : ℝ) / 4)) *
            (Khol * stepFourGagliardoConst d stepOneS) := by ring
      _ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) *
            (Khol * stepFourGagliardoConst d stepOneS) :=
          mul_le_mul_of_nonneg_right (flush_exponent_gag_low hnm)
            (mul_nonneg hKhol hgag0)
  have hgagHm : Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) * gagH ≤
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * (Kh * stepFourGagliardoConst d stepOneS) := by
    calc Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) * gagH
        ≤ Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) *
            (Kh * stepFourGagliardoConst d stepOneS *
              (3 : ℝ) ^ ((((n + 3 : ℤ)) : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left hgagHle (Real.rpow_nonneg (by norm_num) _)
      _ = (Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) *
            (3 : ℝ) ^ ((((n + 3 : ℤ)) : ℝ) / 4)) *
            (Kh * stepFourGagliardoConst d stepOneS) := by ring
      _ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) *
            (Kh * stepFourGagliardoConst d stepOneS) :=
          mul_le_mul_of_nonneg_right (flush_exponent_gag hnm)
            (mul_nonneg hKh hgag0)
  have hgagHlow : Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
      Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) * gagH ≤
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * (Kh * stepFourGagliardoConst d stepOneS) := by
    calc Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
          Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) * gagH
        ≤ Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
            Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) *
            (Kh * stepFourGagliardoConst d stepOneS *
              (3 : ℝ) ^ ((((n + 3 : ℤ)) : ℝ) / 4)) := by
          refine mul_le_mul_of_nonneg_left hgagHle ?_
          exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
            (Real.rpow_nonneg (by norm_num) _)
      _ = (Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
            Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) *
            (3 : ℝ) ^ ((((n + 3 : ℤ)) : ℝ) / 4)) *
            (Kh * stepFourGagliardoConst d stepOneS) := by ring
      _ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) *
            (Kh * stepFourGagliardoConst d stepOneS) :=
          mul_le_mul_of_nonneg_right (flush_exponent_gag_low hnm)
            (mul_nonneg hKh hgag0)
  -- the flat legs
  have hflatLow : Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
      Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) * flatH ≤
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh := by
    calc Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
          Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) * flatH
        ≤ 1 * flatH :=
          mul_le_mul_of_nonneg_right flush_exponent_flat hflatH0
      _ = flatH := one_mul _
      _ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh := hflatHle
  have hsumLow : Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
      Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) * sumH ≤
      (d : ℝ) * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) := by
    calc Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
          Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) * sumH
        ≤ 1 * sumH := mul_le_mul_of_nonneg_right flush_exponent_flat hsumH0
      _ = sumH := one_mul _
      _ ≤ (d : ℝ) * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) := hsumHle
  -- the zpow-to-rpow conversion for the ℓ2 leg
  have hzpow : ((3 : ℝ) ^ n : ℝ) = Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) :=
    (Real.rpow_intCast 3 n).symm
  -- the σ-inverse conversion
  have hsigsplit : Real.sqrt sigma * sigma⁻¹ = Real.sqrt sigma⁻¹ :=
    sqrt_mul_inv_eq_sqrt_inv hsigma
  -- the numeric weights
  have hw2 := stepOneS_rpow_neg_two
  have hw3 := stepOneS_rpow_neg_three
  have hw6 := stepOneS_rpow_neg_six
  have hw7 := stepOneS_rpow_neg_seven
  -- assemble
  rw [hw2, hw3, hw6, hw7, hzpow]
  -- After the numeric rewrites, bound each summand and aggregate.
  have hb1 : Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) * oscE ≤
      3 * (Real.sqrt sigma *
        ((3 : ℝ) ^ (-(n + 3)) * normalizedL2On (truncatedWindow z m (n + 3))
          (fun y => uglob.toFun y -
            volumeAverage (truncatedWindow z m (n + 3)) uglob.toFun))) :=
    le_of_eq hT1
  have hb2 : Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
      (K2 * (oscE + Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) * sumH +
        4096 * Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) * flatH +
        4096 * Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) * gagH +
        16384 * sigma⁻¹ * Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) *
          gagG)) ≤
      3 * K2 * (Real.sqrt sigma *
          ((3 : ℝ) ^ (-(n + 3)) * normalizedL2On (truncatedWindow z m (n + 3))
            (fun y => uglob.toFun y -
              volumeAverage (truncatedWindow z m (n + 3)) uglob.toFun))) +
        K2 * (d : ℝ) * (Real.sqrt sigma * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) +
        4096 * K2 * (Real.sqrt sigma * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) +
        4096 * K2 * (Real.sqrt sigma * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) *
          (Kh * stepFourGagliardoConst d stepOneS))) +
        16384 * K2 * (Real.sqrt sigma⁻¹ * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) *
          (Khol * stepFourGagliardoConst d stepOneS))) := by
    have e1 : Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
        (K2 * oscE) = K2 * (Real.sqrt sigma *
          Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) * oscE) := by ring
    have p1 : Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
        (K2 * oscE) ≤ 3 * K2 * (Real.sqrt sigma *
          ((3 : ℝ) ^ (-(n + 3)) * normalizedL2On (truncatedWindow z m (n + 3))
            (fun y => uglob.toFun y -
              volumeAverage (truncatedWindow z m (n + 3)) uglob.toFun))) := by
      refine le_of_eq ?_
      rw [e1, hT1]
      ring
    have p2 : Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
        (K2 * (Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) * sumH)) ≤
        K2 * (d : ℝ) * (Real.sqrt sigma * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) := by
      have e2 : Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
          (K2 * (Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) * sumH)) =
          K2 * Real.sqrt sigma * (Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
            Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) * sumH) := by ring
      rw [e2]
      have h := mul_le_mul_of_nonneg_left hsumLow
        (mul_nonneg hK2 hsq0)
      calc K2 * Real.sqrt sigma * (Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
            Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) * sumH)
          ≤ K2 * Real.sqrt sigma *
              ((d : ℝ) * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) := h
        _ = K2 * (d : ℝ) *
              (Real.sqrt sigma * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) := by ring
    have p3 : Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
        (K2 * (4096 * Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) * flatH)) ≤
        4096 * K2 * (Real.sqrt sigma * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) := by
      have e3 : Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
          (K2 * (4096 * Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) * flatH)) =
          4096 * K2 * Real.sqrt sigma *
            (Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
              Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) * flatH) := by ring
      rw [e3]
      calc 4096 * K2 * Real.sqrt sigma *
            (Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
              Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) * flatH)
          ≤ 4096 * K2 * Real.sqrt sigma *
              (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) := by
            refine mul_le_mul_of_nonneg_left hflatLow ?_
            exact mul_nonneg (by linarith only [hK2]) hsq0
        _ = 4096 * K2 *
              (Real.sqrt sigma * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) := by ring
    have p4 : Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
        (K2 * (4096 * Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) * gagH)) ≤
        4096 * K2 * (Real.sqrt sigma * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) *
          (Kh * stepFourGagliardoConst d stepOneS))) := by
      have e4 : Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
          (K2 * (4096 * Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) * gagH)) =
          4096 * K2 * Real.sqrt sigma *
            (Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
              Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) * gagH) := by ring
      rw [e4]
      calc 4096 * K2 * Real.sqrt sigma *
            (Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
              Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) * gagH)
          ≤ 4096 * K2 * Real.sqrt sigma *
              (Real.rpow (3 : ℝ) ((m : ℝ) / 2) *
                (Kh * stepFourGagliardoConst d stepOneS)) := by
            refine mul_le_mul_of_nonneg_left hgagHlow ?_
            exact mul_nonneg (by linarith only [hK2]) hsq0
        _ = 4096 * K2 * (Real.sqrt sigma * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) *
              (Kh * stepFourGagliardoConst d stepOneS))) := by ring
    have p5 : Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
        (K2 * (16384 * sigma⁻¹ *
          Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) * gagG)) ≤
        16384 * K2 * (Real.sqrt sigma⁻¹ * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) *
          (Khol * stepFourGagliardoConst d stepOneS))) := by
      have e5 : Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
          (K2 * (16384 * sigma⁻¹ *
            Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) * gagG)) =
          16384 * K2 * (Real.sqrt sigma * sigma⁻¹) *
            (Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
              Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) * gagG) := by ring
      rw [e5, hsigsplit]
      calc 16384 * K2 * Real.sqrt sigma⁻¹ *
            (Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
              Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) * gagG)
          ≤ 16384 * K2 * Real.sqrt sigma⁻¹ *
              (Real.rpow (3 : ℝ) ((m : ℝ) / 2) *
                (Khol * stepFourGagliardoConst d stepOneS)) := by
            refine mul_le_mul_of_nonneg_left hgagGlow ?_
            exact mul_nonneg (by linarith only [hK2]) hsqi0
        _ = 16384 * K2 * (Real.sqrt sigma⁻¹ * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) *
              (Khol * stepFourGagliardoConst d stepOneS))) := by ring
    have hdist : Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
        (K2 * (oscE + Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) * sumH +
          4096 * Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) * flatH +
          4096 * Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) * gagH +
          16384 * sigma⁻¹ * Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) *
            gagG)) =
        Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) * (K2 * oscE) +
          Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
            (K2 * (Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) * sumH)) +
          Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
            (K2 * (4096 * Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) * flatH)) +
          Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
            (K2 * (4096 * Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) *
              gagH)) +
          Real.sqrt sigma * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
            (K2 * (16384 * sigma⁻¹ *
              Real.rpow (3 : ℝ) ((1 + stepOneS) * ((n : ℤ) : ℝ)) * gagG)) := by
      ring
    rw [hdist]
    linarith only [p1, p2, p3, p4, p5]
  have hb3 : 64 * Real.sqrt sigma⁻¹ *
      Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) * gagG ≤
      64 * (Real.sqrt sigma⁻¹ * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) *
        (Khol * stepFourGagliardoConst d stepOneS))) := by
    have e : 64 * Real.sqrt sigma⁻¹ *
        Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) * gagG =
        64 * Real.sqrt sigma⁻¹ *
          (Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) * gagG) := by ring
    rw [e]
    calc 64 * Real.sqrt sigma⁻¹ *
          (Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) * gagG)
        ≤ 64 * Real.sqrt sigma⁻¹ *
            (Real.rpow (3 : ℝ) ((m : ℝ) / 2) *
              (Khol * stepFourGagliardoConst d stepOneS)) := by
          refine mul_le_mul_of_nonneg_left hgagGm ?_
          exact mul_nonneg (by norm_num) hsqi0
      _ = 64 * (Real.sqrt sigma⁻¹ * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) *
            (Khol * stepFourGagliardoConst d stepOneS))) := by ring
  have hb4 : 16 * Real.sqrt sigma *
      Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) * gagH ≤
      16 * (Real.sqrt sigma * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) *
        (Kh * stepFourGagliardoConst d stepOneS))) := by
    have e : 16 * Real.sqrt sigma *
        Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) * gagH =
        16 * Real.sqrt sigma *
          (Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) * gagH) := by ring
    rw [e]
    calc 16 * Real.sqrt sigma *
          (Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) * gagH)
        ≤ 16 * Real.sqrt sigma *
            (Real.rpow (3 : ℝ) ((m : ℝ) / 2) *
              (Kh * stepFourGagliardoConst d stepOneS)) := by
          refine mul_le_mul_of_nonneg_left hgagHm ?_
          exact mul_nonneg (by norm_num) hsq0
      _ = 16 * (Real.sqrt sigma * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) *
            (Kh * stepFourGagliardoConst d stepOneS))) := by ring
  have hb5 : 16 * Real.sqrt sigma * flatH ≤
      16 * (Real.sqrt sigma * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) := by
    calc 16 * Real.sqrt sigma * flatH
        ≤ 16 * Real.sqrt sigma * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) := by
          refine mul_le_mul_of_nonneg_left hflatHle ?_
          exact mul_nonneg (by norm_num) hsq0
      _ = 16 * (Real.sqrt sigma * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) := by
          ring
  -- aggregate
  have hfinal := add_le_add (add_le_add (add_le_add (add_le_add hb1 hb2) hb3) hb4) hb5
  refine le_trans hfinal (le_of_eq ?_)
  rw [stepSevenFlushCG, stepSevenFlushCH]
  ring

end

end Algsuperdiff.Section4.Provider.Regularity
