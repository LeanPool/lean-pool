/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.TraceForm
public import LeanPool.MathFin.Models.ModelFree.SVI.RankOneSignature

/-! # A square root of −1 forces zero signature

Part of the SVI polynomial-sign certificate (#174).

A quadratic form equivalent to its negative has signature zero, so a quotient component
containing a square root of `−1` contributes nothing to the trace-form signature.

## Main definitions

* `imaginaryMulEquiv`: multiplication by `u` with `u² = -1`, as a real-linear equivalence of `A`.

## Main results

* `formSignature_eq_zero_of_equivalent_neg`: a real quadratic form equivalent to its negative has
  signature `0`.
* `weightedTraceForm_signature_zero_of_imaginary`: if `AdjoinRoot f` contains `u` with
  `u² = -1`, the signature of `weightedTraceForm f q` is `0`.

## Tags

trace form signature, complex roots, hyperbolic quadratic form, SVI, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI

/-- Multiplication by a square root of -1 is an invertible real-linear map. -/
noncomputable def imaginaryMulEquiv {A : Type*} [CommRing A] [Algebra ℝ A]
    (u : A) (hu : u ^ 2 = -1) : A ≃ₗ[ℝ] A :=
  { Algebra.lmul ℝ A u with
    invFun := fun x ↦ -u*x
    left_inv := by
      intro x
      change -u*(u*x) = x
      calc
        -u*(u*x) = -(u^2)*x := by ring
        _ = x := by rw [hu]; ring
    right_inv := by
      intro x
      change u*(-u*x) = x
      calc
        u*(-u*x) = -(u^2)*x := by ring
        _ = x := by rw [hu]; ring }

theorem formSignature_eq_zero_of_equivalent_neg {V : Type*}
    [AddCommGroup V] [Module ℝ V] (Q : QuadraticForm ℝ V)
    (h : QuadraticMap.Equivalent Q (-Q)) : formSignature Q = 0 := by
  have hh := h.sigPos_eq
  rw [sigPos_neg] at hh
  unfold formSignature
  exact sub_eq_zero.mpr (congrArg (fun n : ℕ ↦ (n : ℤ)) hh)

/-- Any quotient component containing a square root of -1 has zero trace-form
signature. Multiplication by that root exchanges positive and negative
subspaces, including when nilpotents make the form degenerate. -/
theorem weightedTraceForm_signature_zero_of_imaginary (f q : Polynomial ℝ)
    (u : AdjoinRoot f) (hu : u ^ 2 = -1) :
    formSignature (weightedTraceForm f q).toQuadraticMap = 0 := by
  apply formSignature_eq_zero_of_equivalent_neg
  refine ⟨{ imaginaryMulEquiv u hu with map_app' := ?_ }⟩
  intro x
  change -((weightedTraceForm f q).toQuadraticMap (u*x)) =
    (weightedTraceForm f q).toQuadraticMap x
  simp only [LinearMap.BilinMap.toQuadraticMap_apply, weightedTraceForm_apply]
  have he : (Polynomial.aeval (AdjoinRoot.root f) q)*(u*x)*(u*x) =
      -((Polynomial.aeval (AdjoinRoot.root f) q)*x*x) := by
    calc
      _ = u^2*((Polynomial.aeval (AdjoinRoot.root f) q)*x*x) := by ring
      _ = _ := by rw [hu]; ring
  rw [he, map_neg, neg_neg]

end SVI
end MathFin
