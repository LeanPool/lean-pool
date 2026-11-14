/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseAEndpointC1Floor
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseAEndpointC1
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBBoundaryOscFloor
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBCloseAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBCloseChain
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBFinalArith
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBGateBoundaryC1
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBGateGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenLambdaChain

/-!
# RootClauseABoundaryShellEndpoint

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. `C₁` hits every sufficiently large target exactly -/

/-- **The Step-1 constant is onto, above its two `C_edos`-free floors.**

For every `V` clearing `max(2, 2d+2)`, the `C_iter` slot `4C_iter(k+1)/log 3`
and the floor `δ₀(C_fl,1,k)⁻¹`, there is a `C_edos ≥ C_fl` with `stepOne d
C_edos 1 C_iter k = V`.  The witness is `C_edos = √V/(4·3^{k/4})`, at which the
third slot of the `max` equals `V` and dominates the other two.  This is what
lets two lanes with different pinned `(C_iter, k)` read one and the same
`RootWindowPayload`. -/
theorem exists_cedos_stepOneC1_eq (d : ℕ) (Citer : ℝ) (k : ℕ) {Cfl V : ℝ}
    (hCfl : 1 ≤ Cfl) (hbase : max 2 (2 * (d : ℝ) + 2) ≤ V)
    (hiter : 4 * Citer * ((k : ℝ) + 1) / Real.log 3 ≤ V)
    (hdelta0 : stepOneC1Delta0 Cfl 1 k ≤ V) :
    ∃ Cedos : ℝ, Cfl ≤ Cedos ∧ stepOneC1 d Cedos 1 Citer k = V := by
  have hT : (0 : ℝ) < stepOneThreePow k := stepOneThreePow_pos k
  have hTne : stepOneThreePow k ≠ 0 := ne_of_gt hT
  have h4T : (0 : ℝ) < 4 * stepOneThreePow k := by linarith only [hT]
  have hV2 : (2 : ℝ) ≤ V := le_trans (le_max_left _ _) hbase
  have hV0 : (0 : ℝ) ≤ V := by linarith only [hV2]
  have hs : stepOneS = 1 / 4 := by rw [stepOneS]
  have hsq : Real.sqrt V ^ (2 : ℕ) = V := Real.sq_sqrt hV0
  have hCflpos : (0 : ℝ) < Cfl := lt_of_lt_of_le one_pos hCfl
  have hfl2 : (4 * Cfl * stepOneThreePow k) ^ (2 : ℕ) ≤ V := by
    have h := hdelta0
    rw [stepOneC1Delta0_eq hCflpos one_pos k, hs] at h
    have hid : (2 * Cfl * 1 * stepOneThreePow k) ^ (2 : ℕ) / (1 / 4 : ℝ) =
        (4 * Cfl * stepOneThreePow k) ^ (2 : ℕ) := by ring
    rwa [hid] at h
  have hfl0 : (0 : ℝ) ≤ 4 * Cfl * stepOneThreePow k :=
    mul_nonneg (by linarith only [hCflpos]) hT.le
  have hflsqrt : 4 * Cfl * stepOneThreePow k ≤ Real.sqrt V := by
    have h := Real.sqrt_le_sqrt hfl2
    rwa [Real.sqrt_sq hfl0] at h
  refine ⟨Real.sqrt V / (4 * stepOneThreePow k), ?_, ?_⟩
  · rw [le_div_iff₀ h4T]
    linarith only [hflsqrt]
  · have hCedospos : (0 : ℝ) < Real.sqrt V / (4 * stepOneThreePow k) :=
      div_pos (Real.sqrt_pos.mpr (by linarith only [hV2])) h4T
    have hval : stepOneC1Delta0 (Real.sqrt V / (4 * stepOneThreePow k)) 1 k = V := by
      rw [stepOneC1Delta0_eq hCedospos one_pos k, hs]
      have he : 2 * (Real.sqrt V / (4 * stepOneThreePow k)) * 1 * stepOneThreePow k =
          Real.sqrt V / 2 := by
        field_simp
        ring
      rw [he, div_pow, hsq]
      ring
    rw [stepOneC1, hval, max_eq_right hiter, max_eq_right hbase]

end

end Algsuperdiff.Section4.Provider.Regularity
