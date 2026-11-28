/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.RealRootTrace
public import LeanPool.MathFin.Models.ModelFree.SVI.RankOneSignature
public import LeanPool.MathFin.Models.ModelFree.SVI.TraceForm

/-! # A repeated real root contributes one sign

Part of the SVI polynomial-sign certificate (#174).

On `ℝ[X]/((X − c)ʳ)` the weighted trace form has signature `sign (q c)`, whatever the
multiplicity `r`.

## Main results

* `realRootEval_aeval`: for `r > 0`, `realRootEval c r hr` sends the class of `q` in
  `AdjoinRoot ((X - C c)^r)` to `q.eval c`.
* `weightedTraceForm_realRoot_signature`: for `r > 0`, the weighted trace form of `(X - C c)^r`
  with weight `q` has signature `sign (q.eval c)`, whatever `r` is.

## Tags

repeated real root, trace form signature, multiplicity, SVI, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Polynomial

theorem realRootEval_aeval (c : ℝ) (r : ℕ) (hr : 0 < r) (q : ℝ[X]) :
    realRootEval c r hr (aeval (AdjoinRoot.root ((X-C c)^r)) q) = q.eval c := by
  rw [AdjoinRoot.aeval_eq, realRootEval_mk]

/-- A repeated real root contributes exactly sign(q(c)), not multiplicity
 times that sign, to the weighted trace-form signature. -/
theorem weightedTraceForm_realRoot_signature (c : ℝ) (r : ℕ) (hr : 0 < r) (q : ℝ[X]) :
    formSignature (weightedTraceForm ((X-C c)^r) q).toQuadraticMap = sign (q.eval c) := by
  have hf : (X-C c)^r ≠ (0 : ℝ[X]) := pow_ne_zero _ (X_sub_C_ne_zero c)
  let pb := AdjoinRoot.powerBasis hf
  let : FiniteDimensional ℝ (AdjoinRoot ((X-C c)^r)) := Module.Finite.of_basis pb.basis
  have hQ (x : AdjoinRoot ((X-C c)^r)) :
      (weightedTraceForm ((X-C c)^r) q).toQuadraticMap x =
        ((r : ℝ)*q.eval c) * (realRootEval c r hr x)^2 := by
    rw [LinearMap.BilinMap.toQuadraticMap_apply, weightedTraceForm_apply,
      trace_realRoot_component c r hr]
    simp only [map_mul, realRootEval_aeval]
    ring
  have hh := formSignature_rankOne (weightedTraceForm ((X-C c)^r) q).toQuadraticMap
    (realRootEval c r hr).toLinearMap 1 (by simp) ((r : ℝ)*q.eval c) hQ
  rw [hh]
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  rcases lt_trichotomy (q.eval c) 0 with h | h | h
  · simp [sign, h, not_lt_of_ge h.le, mul_neg_of_pos_of_neg hrr h,
      not_lt_of_ge (mul_neg_of_pos_of_neg hrr h).le]
  · simp [h, sign]
  · simp [sign, h, mul_pos hrr h]

end SVI
end MathFin
