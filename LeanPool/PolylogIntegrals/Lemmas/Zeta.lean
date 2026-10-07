/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.PolylogIntegrals.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Apéry's constant and Mathlib's Riemann zeta function

This bridge lets the integral identities stated using the real series `LeanPolyLog.zeta3`
be used with Mathlib's complex `riemannZeta`.
-/

namespace LeanPolyLog

/-- The series definition of Apéry's constant agrees with Mathlib's Riemann zeta function. -/
public theorem ofReal_zeta3_eq_riemannZeta_three : (zeta3 : ℂ) = riemannZeta 3 := by
  rw [zeta3, Complex.ofReal_tsum,
    zeta_eq_tsum_one_div_nat_add_one_cpow (by norm_num : 1 < (3 : ℂ).re)]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.cpow_ofNat]

end LeanPolyLog
