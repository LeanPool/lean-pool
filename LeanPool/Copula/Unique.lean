/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
module

public import LeanPool.Copula.Independence
public import LeanPool.Copula.Comonotonic
import LeanPool.Copula.CDF.Extensionality

/-! # Uniqueness in dimensions zero and one -/

public section

open scoped unitInterval

namespace ProbabilityTheory.Copula

instance : Subsingleton (Copula 0) where
  allEq C D := ext_cdf (by intro u; simp)

@[simp]
theorem cdf_dim_one (C : Copula 1) (u : Fin 1 → I) : C.cdf u = (u 0 : ℝ) := by
  have hu : u = Function.update (fun _ => 1) 0 (u 0) := by
    funext i
    fin_cases i
    simp
  calc
    C.cdf u = C.cdf (Function.update (fun _ => 1) 0 (u 0)) := congrArg C.cdf hu
    _ = (u 0 : ℝ) := C.cdf_update_one 0 (u 0)

instance : Subsingleton (Copula 1) where
  allEq C D := ext_cdf (by intro u; simp)

theorem eq_independence_dim_one (C : Copula 1) : C = independence 1 := Subsingleton.elim _ _

theorem independence_eq_comonotonic_dim_one : independence 1 = comonotonic 1 :=
  Subsingleton.elim _ _

end ProbabilityTheory.Copula
