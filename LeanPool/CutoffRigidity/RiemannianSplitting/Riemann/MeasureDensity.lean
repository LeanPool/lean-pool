/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianChartDensity
public import Mathlib.Analysis.InnerProductSpace.NormDet

/-! # Gram density and the norm determinant -/

@[expose] public section

open Bundle
open scoped Manifold

namespace CutCur

theorem gramDens_eq_normDet {F W : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] (L : F →ₗ[ℝ] W) :
    gramDens L = L.normDet := by
  have h := L.normDet_sq_eq_det_gram (stdOrthonormalBasis ℝ F)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h
  rw [gramDens, ← h, Real.sqrt_sq L.normDet_nonneg]

end CutCur
