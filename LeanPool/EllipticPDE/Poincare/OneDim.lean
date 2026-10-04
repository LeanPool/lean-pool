/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Analysis.PoincareInequality


/-!
# One-dimensional Poincaré inequality

Upstreamed to Mathlib as
`EllipticPdes.Analysis.PoincareInequality`.

This file re-exports the Mathlib declarations under the
`EllipticPdes.Poincare` namespace for backward compatibility.

* `intervalIntegral_mul_sq_le`: Cauchy-Schwarz for `∫ f g`.
* `sq_intervalIntegral_le`: the `g = 1` special case.
* `poincare_oneDim`: the one-dimensional Poincaré inequality.
-/

@[expose] public section

namespace EllipticPdes.Poincare

alias intervalIntegral_mul_sq_le := MeasureTheory.intervalIntegral_mul_sq_le
alias sq_intervalIntegral_le     := MeasureTheory.sq_intervalIntegral_le
alias poincare_oneDim            := MeasureTheory.poincare_1d

end EllipticPdes.Poincare
