/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.Main
public import LeanPool.Bruck.StatementChecks

/-!
# Brück's conjecture for entire functions

Source: url:https://hexagonmath.org/2611.00826v1
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
Status: verified
Main declarations: `Bruck.bruck_conjecture`, `Bruck.sharesCM_iff_iteratedDeriv_vanishing`,
  `Bruck.hyperOrder_eq_limsup_circleAverage_posLog`
Tags: entire-functions, value-distribution, differential-equations
MSC: 30D35, 30D15, 34M10
-/

public section

open scoped ENNReal

namespace Bruck

/-- Brück's conjecture for entire functions sharing a value with their first derivative. -/
theorem bruck_conjecture {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnon : ¬ ∀ z, f z = f 0) (a : ℂ) (hshare : SharesCM f (deriv f) a)
    (hfinite : hyperOrder f < ⊤)
    (hnotint : ∀ n : ℕ, 0 < n → hyperOrder f ≠ (n : ℝ≥0∞)) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z, deriv f z - a = c * (f z - a) :=
  bruck hf hnon a hshare hfinite hnotint

end Bruck
