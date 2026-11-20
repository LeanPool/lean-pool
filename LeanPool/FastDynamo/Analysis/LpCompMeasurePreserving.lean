/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.LiteralThreeTorus

/-!
# Composition with a measure-preserving self-map, as a continuous linear map

`MeasureTheory.Lp.compMeasurePreservingₗᵢ` is a *linear isometry*; the transport operator of
`FastDynamo/Dynamics/Ideal/CauchyOperator.lean` composes it with a multiplication operator and
therefore works with its `ContinuousLinearMap` coercion.  The two facts below are
`Lp.coeFn_compMeasurePreserving` and `Lp.norm_compMeasurePreserving` restated in that spelling,
which is what lets `filter_upwards` match them syntactically.

They are stated for `LiteralC3L2 = L²(T³; ℂ³)`, the only space the development composes on, and
refer to no velocity, flow or parameter; the companion multiplication operator lives in
`FastDynamo/Analysis/BoundedOperatorMultiplier.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-! ## Composition with a measure-preserving self-map of the literal three-torus -/

/-- The almost everywhere representative of composition with a measure-preserving self-map of
`Torus 3`, in the continuous-linear-map form that `idealTransport` is built from.  This is
`MeasureTheory.Lp.coeFn_compMeasurePreserving` read through
`LinearIsometry.toContinuousLinearMap`; stating it separately avoids the syntactic mismatch
between the two spellings inside `filter_upwards`. -/
theorem coeFn_compMeasurePreservingCLM {F : Torus 3 → Torus 3}
    (hF : MeasurePreserving F (volume : Measure (Torus 3)) volume) (B : LiteralC3L2) :
    (((Lp.compMeasurePreservingₗᵢ ℂ F hF).toContinuousLinearMap B : LiteralC3L2) :
      Torus 3 → C3) =ᵐ[volume] fun x ↦ (B : Torus 3 → C3) (F x) :=
  Lp.coeFn_compMeasurePreserving B hF

/-- Composition with a measure-preserving self-map of `Torus 3` is an isometry of
`LiteralC3L2`, in the continuous-linear-map form that `idealTransport` is built from. -/
theorem norm_compMeasurePreservingCLM {F : Torus 3 → Torus 3}
    (hF : MeasurePreserving F (volume : Measure (Torus 3)) volume) (B : LiteralC3L2) :
    ‖(Lp.compMeasurePreservingₗᵢ ℂ F hF).toContinuousLinearMap B‖ = ‖B‖ :=
  Lp.norm_compMeasurePreserving B hF

end

end FastDynamo
