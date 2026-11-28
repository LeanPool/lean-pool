/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.TraceForm
public import LeanPool.MathFin.Models.ModelFree.SVI.ClearedSignature
public import LeanPool.MathFin.Models.ModelFree.SVI.RankOneSignature

/-! # The Hermite matrix and the trace form have the same signature

Part of the SVI polynomial-sign certificate (#174).

Taking the matrix of a form in any basis preserves its signature, so the Hermite matrix test
reduces to the trace form on the quotient.

## Main results

* `matrixSignature_toMatrix`: the matrix of a bilinear form in any basis `Fin n → V` has
  `matrixSignature` equal to the `formSignature` of the form's quadratic map.
* `hermite_signature_eq_trace_signature`: for `f ≠ 0`, `signatureTest (hermite f q f.natDegree)`
  equals the signature of `weightedTraceForm f q`.

## Tags

Hermite matrix, trace form, signature invariance, change of basis, SVI, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Matrix

/-- Taking a matrix in any basis preserves the quadratic-form signature. -/
theorem matrixSignature_toMatrix {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℝ V) (B : LinearMap.BilinForm ℝ V) :
    matrixSignature (B.toMatrix b) = formSignature B.toQuadraticMap := by
  have hQ : (B.toMatrix b).toQuadraticForm' = B.toQuadraticMap.basisRepr b := by
    ext x
    simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply']
    rw [B.dotProduct_toMatrix_mulVec b]
    rfl
  have he : QuadraticMap.Equivalent B.toQuadraticMap (B.toMatrix b).toQuadraticForm' := by
    rw [hQ]
    exact ⟨B.toQuadraticMap.isometryEquivBasisRepr b⟩
  unfold matrixSignature formSignature
  rw [← he.sigPos_eq, ← he.sigNeg_eq]

/-- The remaining Hermite--Tarski theorem can be proved on the quotient
trace form; every matrix and signature conversion is already checked. -/
theorem hermite_signature_eq_trace_signature (f q : Polynomial ℝ) (hf : f ≠ 0) :
    signatureTest (hermite f q f.natDegree) =
      formSignature (weightedTraceForm f q).toQuadraticMap := by
  rw [signatureTest_eq_matrixSignature _ (hermite_symmetric f q f.natDegree),
    hermite_eq_traceForm_matrix f q hf]
  exact matrixSignature_toMatrix (AdjoinRoot.powerBasis hf).basis (weightedTraceForm f q)

end SVI
end MathFin
