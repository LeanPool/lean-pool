/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Topology.LocallyConstant.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-! # Scalar constancy from a zero intrinsic differential -/

@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- A differentiable scalar function with zero intrinsic differential is locally constant. -/
theorem isLocallyConstant_of_mvfderiv_eq_zero
    {f : M → ℝ} (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (hzero : ∀ x, mvfderiv I f x = 0) : IsLocallyConstant f :=
  hf.isLocallyConstant_of_mfderiv_eq_zero
    (fun x => TauCeti.mvfderiv_eq_zero_iff.mp (hzero x))

/-- On a connected manifold, zero intrinsic differential forces global constancy. -/
theorem eq_of_mvfderiv_eq_zero [PreconnectedSpace M]
    {f : M → ℝ} (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (hzero : ∀ x, mvfderiv I f x = 0) (x y : M) : f x = f y :=
  (isLocallyConstant_of_mvfderiv_eq_zero hf hzero).apply_eq_of_preconnectedSpace x y

end CutoffRigidity
