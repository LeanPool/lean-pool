/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# Statement seed extracted from Polynomial/Selector

Literal declarations are unchanged; theorem conclusions remain in the implementation module.
-/

@[expose] public section

open Polynomial

namespace VacuumBellSeparation

/-- The polynomial selector `poly_N(z) = (1 - z)^N Σ_{k<N} C(N+k-1, k) z^k` of (7.4). -/
noncomputable def selector (N : ℕ) : ℝ[X] :=
  (1 - X) ^ N * ∑ k ∈ Finset.range N, C (((N + k - 1).choose k : ℕ) : ℝ) * X ^ k


/-- The sum of the absolute values of the coefficients of a real polynomial,
`Σ_{i ≤ deg p} |p_i|` (the `ℓ¹` norm of its coefficient vector). -/
noncomputable def coeffAbsSum (p : ℝ[X]) : ℝ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|


end VacuumBellSeparation
