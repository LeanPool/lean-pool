/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Linear

/-!
# Genuine exponential difference quotients for quantum uncertainty

The real-parameter derivative of three actual complex exponentials gives
the finite-difference limit used for Weyl Gram matrices. Positive times
will be inserted as squared displacement amplitudes, avoiding any assumed
differentiability of unbounded quadrature generators.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Filter
open scoped Topology

theorem hasDerivAt_complex_exp_real_mul (a : ℂ) :
    HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * a)) a 0 := by
  have hc : HasDerivAt (fun s : ℝ => (s : ℂ) * a) a 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const a
  simpa using hc.cexp

/-- Gaussian gram difference given by `Complex.exp ((s : ℂ) * a) - Complex.exp ((s : ℂ) * b) -
Complex.exp ((s : ℂ) * c) + 1`. -/
def gaussianGramDifference (a b c : ℂ) (s : ℝ) : ℂ :=
  Complex.exp ((s : ℂ) * a) - Complex.exp ((s : ℂ) * b) -
    Complex.exp ((s : ℂ) * c) + 1

@[simp] theorem gaussianGramDifference_zero (a b c : ℂ) : gaussianGramDifference a b c 0 = 0 := by
  simp [gaussianGramDifference]

theorem hasDerivAt_gaussianGramDifference (a b c : ℂ) :
    HasDerivAt (gaussianGramDifference a b c) (a - b - c) 0 :=
  (((hasDerivAt_complex_exp_real_mul a).sub (hasDerivAt_complex_exp_real_mul b)).sub
    (hasDerivAt_complex_exp_real_mul c)).add_const 1

theorem tendsto_gaussianGramDifference_quotient (a b c : ℂ) :
    Tendsto (fun s : ℝ => s⁻¹ • gaussianGramDifference a b c s)
      (𝓝[>] (0 : ℝ)) (𝓝 (a - b - c)) := by
  simpa only [zero_add, gaussianGramDifference_zero, sub_zero] using
    (hasDerivAt_gaussianGramDifference a b c).tendsto_slope_zero_right

end VacuumBellSeparation.Gaussian
