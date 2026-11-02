/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.InnerProductSpace.NormPow

/-!
# Real-power calculus for the majorants

The majorant proofs use the exported derivative interface. The private implementation
import keeps complex-power calculus and inner-product norm calculus out of their environments.
-/

namespace Majorants

/-- Real-power differentiation without exposing the implementation imports. -/
public theorem hasDerivAt_realPower {x p : ℝ} (h : x ≠ 0 ∨ 1 ≤ p) :
    HasDerivAt (fun x : ℝ => x ^ p) (p * x ^ (p - 1)) x :=
  Real.hasDerivAt_rpow_const h

/-- The absolute-power derivative, keeping norm calculus behind this interface. -/
public theorem hasDerivAt_absolutePower (x : ℝ) {p : ℝ} (hp : 1 < p) :
    HasDerivAt (fun x : ℝ => |x| ^ p) (p * |x| ^ (p - 2) * x) x :=
  hasDerivAt_abs_rpow x hp

end Majorants

namespace HasDerivAt

/-- Differentiate a real power through the majorants' calculus interface. -/
public theorem burkholderRealPower {f : ℝ → ℝ} {f' p x : ℝ}
    (hf : HasDerivAt f f' x) (h : f x ≠ 0 ∨ 1 ≤ p) :
    HasDerivAt (fun y => f y ^ p) (f' * p * f x ^ (p - 1)) x :=
  hf.rpow_const h

end HasDerivAt

namespace DifferentiableAt

/-- Preserve differentiability through the majorants' real-power interface. -/
public theorem burkholderRealPower {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {p : ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (h : f x ≠ 0 ∨ 1 ≤ p) : DifferentiableAt ℝ (fun y => f y ^ p) x :=
  hf.rpow_const h

end DifferentiableAt
