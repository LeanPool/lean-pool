/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.ProductSignature
public import LeanPool.MathFin.Models.ModelFree.SVI.TraceForm
public import Mathlib.RingTheory.Trace.Basic

/-! # Weighted trace forms of associated polynomials

Part of the SVI polynomial-sign certificate (#174).

Replacing the defining polynomial by an associate gives an equivalent weighted trace form, hence
the same signature.

## Main results

* `weightedTraceForm_associated_equivalent`: if `f` and `g` are associated, the weighted trace forms
  of `f` and `g` against `q` are equivalent quadratic maps.
* `weightedTraceForm_associated_signature`: they have the same signature.

## Tags

Hermite trace form, associated polynomial, signature, SVI, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Polynomial

/-- Changing the defining polynomial by a unit preserves the weighted trace
form, including its degenerate directions. -/
theorem weightedTraceForm_associated_equivalent (f g q : ℝ[X])
    (h : Associated f g) :
    QuadraticMap.Equivalent (weightedTraceForm f q).toQuadraticMap
      (weightedTraceForm g q).toQuadraticMap := by
  let e := AdjoinRoot.algEquivOfAssociated ℝ f g h
  refine ⟨{ e.toLinearEquiv with map_app' := ?_ }⟩
  intro x
  simp only [LinearMap.BilinMap.toQuadraticMap_apply, weightedTraceForm_apply]
  rw [← Algebra.trace_eq_of_algEquiv e]
  simp only [map_mul, ← aeval_algHom_apply]
  simp only [e, AdjoinRoot.algEquivOfAssociated_root]
  rfl

theorem weightedTraceForm_associated_signature (f g q : ℝ[X])
    (h : Associated f g) :
    formSignature (weightedTraceForm f q).toQuadraticMap =
      formSignature (weightedTraceForm g q).toQuadraticMap :=
  formSignature_eq_of_equivalent (weightedTraceForm_associated_equivalent f g q h)

end SVI
end MathFin
