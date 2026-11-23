/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction

/-!
# Brück's conjecture

The characteristic is the Nevanlinna characteristic at infinity.
For an entire function it is the circle average of the positive logarithm
of the norm. Positive integer hyper-orders and infinite hyper-order are excluded.
-/

@[expose] public section

open Filter
open scoped ENNReal

namespace Bruck

/-- Two functions share a value with multiplicities when the shifted functions
are nontrivial and their local analytic orders agree everywhere. -/
def SharesCM (f g : ℂ → ℂ) (a : ℂ) : Prop :=
  f ≠ (fun _z => a) ∧ g ≠ (fun _z => a) ∧
    ∀ z, analyticOrderAt (fun w => f w - a) z = analyticOrderAt (fun w => g w - a) z

/-- The limsup of the logarithmic growth exponent. -/
noncomputable def logOrder (F : ℝ → ℝ) : ℝ≥0∞ :=
  limsup (fun r => ENNReal.ofReal (Real.log (F r) / Real.log r)) atTop

/-- The limsup of the double logarithm of the characteristic divided by `log r`. -/
noncomputable def hyperOrder (f : ℂ → ℂ) : ℝ≥0∞ :=
  logOrder (fun r => Real.log (ValueDistribution.characteristic f ⊤ r))

end Bruck
