/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! # An integrating factor for a nonlinear differential inequality -/

@[expose] public section

namespace NairTenenbaum

open Real

theorem hasDerivAt_exp_mul_rpow {L R : ℝ → ℝ} {s L' P a h : ℝ}
    (hL : HasDerivAt L L' s) (hR : HasDerivAt R (-P) s) (hpos : 0 < L s) :
    HasDerivAt (fun x => Real.exp (-a * h * R x) * L x ^ h)
      (Real.exp (-a * h * R s) * (a * h * P * L s ^ h + h * L s ^ (h - 1) * L')) s := by
  convert ((hR.const_mul (-a * h)).exp).mul (hL.rpow_const (Or.inl hpos.ne')) using 1
  ring

theorem neg_deriv_exp_mul_rpow_le {L R : ℝ → ℝ} {s L' P B a h : ℝ}
    (hL : HasDerivAt L L' s) (hR : HasDerivAt R (-P) s) (hpos : 0 < L s)
    (hh : 0 ≤ h) (hineq : -L' ≤ a * P * L s + B * L s ^ (1 - h)) :
    -deriv (fun x => Real.exp (-a * h * R x) * L x ^ h) s ≤
      h * Real.exp (-a * h * R s) * B := by
  have hone : L s ^ (h - 1) * L s = L s ^ h := by
    simpa only [sub_add_cancel, Real.rpow_one] using (Real.rpow_add hpos (h - 1) 1).symm
  have hcancel : L s ^ (h - 1) * L s ^ (1 - h) = 1 := by
    rw [← Real.rpow_add hpos, show h - 1 + (1 - h) = 0 by ring, Real.rpow_zero]
  rw [(hasDerivAt_exp_mul_rpow hL hR hpos).deriv]
  calc
    _ = (h * Real.exp (-a * h * R s) * L s ^ (h - 1)) * (-L' - a * P * L s) := by
      rw [← hone]
      ring
    _ ≤ (h * Real.exp (-a * h * R s) * L s ^ (h - 1)) * (B * L s ^ (1 - h)) :=
      mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg (mul_nonneg hh (Real.exp_nonneg _)) (Real.rpow_nonneg hpos.le _))
    _ = (h * Real.exp (-a * h * R s) * B) * (L s ^ (h - 1) * L s ^ (1 - h)) := by ring
    _ = _ := by rw [hcancel, mul_one]

end NairTenenbaum
