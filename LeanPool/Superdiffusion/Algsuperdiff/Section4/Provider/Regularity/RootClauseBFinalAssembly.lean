/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBFinalFunding
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSixInteriorEndpoint

/-!
# RootClauseBFinalAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. Two missing monotonicity steps in the `C_B` slot -/

/-- `rootClauseBDataMConst` is monotone in its `C_Bc` slot. -/
theorem rootClauseBDataMConst_mono (d : ℕ) {CBc CBc' : ℝ} (h : CBc ≤ CBc') :
    rootClauseBDataMConst d CBc ≤ rootClauseBDataMConst d CBc' := by
  have hF : (0 : ℝ) ≤ stepSevenCaccForcingFactor := stepSevenCaccForcingFactor_nonneg
  have hstep : 4 * stepSevenCaccForcingFactor * (64 / 7 * CBc) ≤
      4 * stepSevenCaccForcingFactor * (64 / 7 * CBc') := by
    refine mul_le_mul_of_nonneg_left (by linarith only [h]) ?_
    linarith only [hF]
  rw [rootClauseBDataMConst, rootClauseBDataMConst]
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hstep)
    (rootClauseBDataBConst_nonneg d)

/-- `rootClauseBCaccUniform` is monotone in its `C_B` slot. -/
theorem rootClauseBCaccUniform_mono (C : ℝ) {CB CB' : ℝ} (hCB : 0 ≤ CB)
    (h : CB ≤ CB') : rootClauseBCaccUniform C CB ≤ rootClauseBCaccUniform C CB' := by
  have hsq : CB ^ (2 : ℕ) ≤ CB' ^ (2 : ℕ) := pow_le_pow_left₀ hCB h 2
  have h1 : (16384 : ℝ) / 441 * CB ^ (2 : ℕ) ≤ 16384 / 441 * CB' ^ (2 : ℕ) := by
    linarith only [hsq]
  have h10 : (0 : ℝ) ≤ 16384 / 441 * CB ^ (2 : ℕ) := by
    have := pow_nonneg hCB 2
    linarith only [this]
  have h2 : (16384 / 441 * CB ^ (2 : ℕ)) ^ (2 : ℕ) ≤
      (16384 / 441 * CB' ^ (2 : ℕ)) ^ (2 : ℕ) := pow_le_pow_left₀ h10 h1 2
  have hcoef : (0 : ℝ) ≤ (2 * max 1 C) ^ (4 : ℕ) * 4 := by
    have hm : (1 : ℝ) ≤ max 1 C := le_max_left _ _
    have : (0 : ℝ) ≤ (2 * max 1 C) ^ (4 : ℕ) := by
      refine pow_nonneg ?_ 4
      linarith only [hm]
    linarith only [this]
  rw [rootClauseBCaccUniform, rootClauseBCaccUniform]
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h2 hcoef)

/-! ## 1b. The Hölder constants are nonnegative -/

/-- **`0 ≤ K` is not a hypothesis, it is a consequence.**

The frozen root prints `HolderSeminormBoundOn (□_m) (1/2) K f` and no sign
condition on `K`; every §4.4 producer nevertheless binds `0 ≤ K`.  The binder
is redundant: the open cube contains `0` and the point `(3^m/4)·𝟙`, whose
distance is positive, so `0 ≤ ‖f y - f 0‖ ≤ K‖y‖^{1/2}` forces `0 ≤ K`. -/
theorem holderHalf_const_nonneg [NeZero d] {m : ℤ} {K : ℝ} {f : Vec d → Vec d}
    (hf : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K f) :
    0 ≤ K := by
  classical
  obtain ⟨i0⟩ : Nonempty (Fin d) :=
    Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne d))
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hymem : (fun _ : Fin d => (3 : ℝ) ^ m / 4) ∈ openCubeSet (originCube d m) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    refine ⟨?_, ?_⟩
    · show (-(1 / 2 : ℝ)) * (3 : ℝ) ^ m < (3 : ℝ) ^ m / 4
      linarith only [h3]
    · show (3 : ℝ) ^ m / 4 < (1 / 2 : ℝ) * (3 : ℝ) ^ m
      linarith only [h3]
  have h0mem : (0 : Vec d) ∈ openCubeSet (originCube d m) :=
    zero_mem_openCubeSet_originCube d m
  have hbound := hf _ hymem 0 h0mem
  have hnormpos : (0 : ℝ) < ‖(fun _ : Fin d => (3 : ℝ) ^ m / 4) - (0 : Vec d)‖ := by
    have hi : ‖((fun _ : Fin d => (3 : ℝ) ^ m / 4) - (0 : Vec d)) i0‖ ≤
        ‖(fun _ : Fin d => (3 : ℝ) ^ m / 4) - (0 : Vec d)‖ := norm_le_pi_norm _ i0
    have hval : ‖((fun _ : Fin d => (3 : ℝ) ^ m / 4) - (0 : Vec d)) i0‖ =
        (3 : ℝ) ^ m / 4 := by
      change ‖(3 : ℝ) ^ m / 4 - 0‖ = (3 : ℝ) ^ m / 4
      rw [sub_zero, Real.norm_eq_abs, abs_of_pos (by linarith only [h3])]
    rw [hval] at hi
    linarith only [hi, h3]
  have hp : (0 : ℝ) <
      ‖(fun _ : Fin d => (3 : ℝ) ^ m / 4) - (0 : Vec d)‖ ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hnormpos _
  by_contra hK
  push Not at hK
  have hneg : K * ‖(fun _ : Fin d => (3 : ℝ) ^ m / 4) - (0 : Vec d)‖ ^ (1 / 2 : ℝ) < 0 :=
    mul_neg_of_neg_of_pos hK hp
  have hnn : (0 : ℝ) ≤ ‖f (fun _ : Fin d => (3 : ℝ) ^ m / 4) - f 0‖ := norm_nonneg _
  linarith only [hbound, hneg, hnn]

end

end Algsuperdiff.Section4.Provider.Regularity
