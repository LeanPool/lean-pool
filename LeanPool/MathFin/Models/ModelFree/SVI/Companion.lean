/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.Denominators
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Trace.Defs

/-! # The companion matrix is multiplication by the root

Part of the SVI polynomial-sign certificate (#174).

For `f ≠ 0`, `companion f f.natDegree` is the matrix of multiplication by the class of `X` in
`ℝ[X]/(f)`, in the power basis, with no irreducibility or squarefreeness assumed. Its
characteristic polynomial is `f` made monic, and traces of its powers are algebra traces.

## Main results

* `companion_eq_leftMulMatrix`: for `f ≠ 0`, `companion f f.natDegree` is the matrix of
  multiplication by `AdjoinRoot.root f` in the power basis of `AdjoinRoot f`.
* `companion_charpoly`: its characteristic polynomial is `f * C f.leadingCoeff⁻¹`.
* `trace_companion_pow_eq_algebraTrace`: the trace of its `r`-th power is the algebra trace of
  `(AdjoinRoot.root f)^r`.

## Tags

companion matrix, characteristic polynomial, trace of powers, quotient algebra, SVI, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Polynomial

/-- The concrete companion matrix really is multiplication by the residue
class of X in the full quotient algebra. No irreducibility or squarefreeness
is imposed. -/
theorem companion_eq_leftMulMatrix (f : ℝ[X]) (hf : f ≠ 0) :
    companion f f.natDegree =
      Algebra.leftMulMatrix (AdjoinRoot.powerBasis hf).basis (AdjoinRoot.root f) := by
  have hl : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  rw [show AdjoinRoot.root f = (AdjoinRoot.powerBasis hf).gen from rfl,
    (AdjoinRoot.powerBasis hf).leftMulMatrix]
  ext i j
  simp only [companion, scaledCompanion, Matrix.smul_apply, smul_eq_mul,
    PowerBasis.minpolyGen_eq, AdjoinRoot.minpoly_powerBasis_gen,
    coeff_mul_C, AdjoinRoot.powerBasis_dim]
  change _ = if (j : ℕ) + 1 = f.natDegree then _ else _
  split_ifs <;> simp [hl, mul_comm]

theorem companion_charpoly (f : ℝ[X]) (hf : f ≠ 0) :
    (companion f f.natDegree).charpoly = f * C f.leadingCoeff⁻¹ := by
  rw [companion_eq_leftMulMatrix f hf]
  exact (charpoly_leftMulMatrix (AdjoinRoot.powerBasis hf)).trans
    (AdjoinRoot.minpoly_powerBasis_gen hf)

/-- Every matrix power computes the trace of the corresponding quotient
algebra element, including nilpotent directions at multiple roots. -/
theorem trace_companion_pow_eq_algebraTrace (f : ℝ[X]) (hf : f ≠ 0) (r : ℕ) :
    Matrix.trace ((companion f f.natDegree)^r) =
      Algebra.trace ℝ (AdjoinRoot f) ((AdjoinRoot.root f)^r) := by
  rw [companion_eq_leftMulMatrix f hf]
  change Matrix.trace (((Algebra.leftMulMatrix (AdjoinRoot.powerBasis hf).basis)
    (AdjoinRoot.root f))^r) = _
  rw [← map_pow]
  exact (Algebra.trace_eq_matrix_trace (AdjoinRoot.powerBasis hf).basis _).symm

end SVI
end MathFin
