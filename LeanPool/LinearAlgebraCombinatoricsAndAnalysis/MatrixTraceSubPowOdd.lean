/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Tactic.Abel

/-!
# The trace of an odd power of a difference of two idempotent matrices

For idempotent square matrices `P`, `Q` over a commutative ring,
`tr ((P - Q) ^ (2k + 1)) = tr P - tr Q`, with no hypothesis on `2`.

## Main statements

* `IsIdempotentElem.sub_sq_commute_left`, `IsIdempotentElem.sub_sq_commute_right`: in any ring,
  `(P - Q)²` commutes with the idempotents `P` and `Q`.
* `IsIdempotentElem.sub_mul_sub_sq`: `(P - Q) (P - Q)² = (P - Q) - (P Q P - Q P Q)`.
* `Matrix.trace_mul_mul_mul_eq_of_isIdempotentElem`: `tr (D P Q P) = tr (D Q P Q)` when `D`
  commutes with `P` and `Q`.
* `Matrix.trace_sub_pow_odd_of_isIdempotentElem`: `tr ((P - Q) ^ (2k + 1)) = tr P - tr Q`.
-/

public section

namespace IsIdempotentElem

variable {R : Type*} [Ring R] {P Q : R}

/-- `(P - Q)²` commutes with `P` when `P` and `Q` are idempotent: both products equal
`P - P Q P`. -/
theorem sub_sq_commute_left (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) :
    Commute ((P - Q) ^ 2) P := by
  unfold Commute SemiconjBy
  simp only [sq, sub_mul, mul_sub, mul_assoc, hP.eq, hQ.eq]
  simp only [← mul_assoc, hP.eq]
  abel

/-- `(P - Q)²` commutes with `Q` when `P` and `Q` are idempotent. -/
theorem sub_sq_commute_right (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) :
    Commute ((P - Q) ^ 2) Q := by
  simpa only [← neg_sub P Q, neg_sq] using sub_sq_commute_left hQ hP

/-- `(P - Q) (P - Q)² = (P - Q) - (P Q P - Q P Q)` when `P` and `Q` are idempotent. -/
theorem sub_mul_sub_sq (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) :
    (P - Q) * (P - Q) ^ 2 = (P - Q) - (P * Q * P - Q * P * Q) := by
  simp only [sq, sub_mul, mul_sub, mul_assoc, hP.eq, hQ.eq]
  simp only [← mul_assoc, hP.eq, hQ.eq]
  abel

end IsIdempotentElem

namespace Matrix

variable {n R : Type*} [Fintype n] [CommRing R]

/-- If `D` commutes with the idempotents `P` and `Q`, then `tr (D P Q P) = tr (D Q P Q)`: both
equal `tr (D P Q)`, by cyclicity of the trace. -/
theorem trace_mul_mul_mul_eq_of_isIdempotentElem {P Q D : Matrix n n R}
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) (hDP : Commute D P)
    (hDQ : Commute D Q) : trace (D * P * Q * P) = trace (D * Q * P * Q) := by
  have e1 : trace (D * P * Q * P) = trace (D * P * Q) := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hDP.eq, Matrix.mul_assoc D,
      hP.eq]
  have e2 : trace (D * Q * P * Q) = trace (D * Q * P) := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hDQ.eq, Matrix.mul_assoc D,
      hQ.eq]
  have e3 : trace (D * Q * P) = trace (D * P * Q) := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, ← hDP.eq]
  rw [e1, e2, e3]

variable [DecidableEq n]

/-- For idempotent square matrices `P` and `Q` over a commutative ring, the trace of every odd
power of `P - Q` is `tr P - tr Q`. No hypothesis on the characteristic. -/
theorem trace_sub_pow_odd_of_isIdempotentElem {P Q : Matrix n n R} (hP : IsIdempotentElem P)
    (hQ : IsIdempotentElem Q) (k : ℕ) :
    trace ((P - Q) ^ (2 * k + 1)) = trace P - trace Q := by
  have hpow : ∀ k : ℕ, (P - Q) ^ (2 * k + 1) = ((P - Q) ^ 2) ^ k * (P - Q) := fun k => by
    rw [pow_succ, pow_mul]
  induction k with
  | zero => simp [trace_sub]
  | succ k ih =>
    set C := (P - Q) ^ 2
    have hCP : Commute (C ^ k) P := (hP.sub_sq_commute_left hQ).pow_left k
    have hCQ : Commute (C ^ k) Q := (hP.sub_sq_commute_right hQ).pow_left k
    have step : (P - Q) ^ (2 * (k + 1) + 1)
        = (P - Q) ^ (2 * k + 1) - (C ^ k * P * Q * P - C ^ k * Q * P * Q) := by
      have hc : C * (P - Q) = (P - Q) * C := (Commute.pow_self (P - Q) 2).eq
      rw [hpow, hpow, pow_succ, Matrix.mul_assoc, hc, hP.sub_mul_sub_sq hQ]
      simp only [mul_sub, Matrix.mul_assoc]
    rw [step, trace_sub, ih, trace_sub,
      trace_mul_mul_mul_eq_of_isIdempotentElem hP hQ hCP hCQ, sub_self, sub_zero]

end Matrix
