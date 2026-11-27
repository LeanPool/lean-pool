/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Burkholder's function on normed groups -/

@[expose] public section

namespace BanachProbability

/-- **Burkholder's function** (Burkholder 1988, (1.6)):
`u_p (x, y) = α_p (|y| − (p* − 1) |x|) (|x| + |y|)^{p−1}`, `α_p = p (1 − 1/p*)^{p−1}`,
`p* = max (p, p / (p − 1))`; `x` is the position of the dominating martingale and `y` that of the
subordinate one. -/
noncomputable def Burkholder.burkholderFun {H : Type*} [NormedAddCommGroup H] (p : ℝ) (x y : H) :
    ℝ :=
  p * (1 - 1 / max p (p / (p - 1))) ^ (p - 1) * (‖y‖ - (max p (p / (p - 1)) - 1) * ‖x‖) *
    (‖x‖ + ‖y‖) ^ (p - 1)

end BanachProbability
