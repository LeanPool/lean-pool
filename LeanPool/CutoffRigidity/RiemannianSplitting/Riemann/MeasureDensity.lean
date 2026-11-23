/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Statements
public import Mathlib.Analysis.InnerProductSpace.NormDet

/-! # Gram density and the Jacobian of an inverse chart -/

@[expose] public section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace CutCur

section Linear

variable {F W : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- `√det` of the Gram matrix of the image of the standard orthonormal basis. -/
noncomputable def gramDens (L : F →ₗ[ℝ] W) : ℝ :=
  Real.sqrt (Matrix.det (Matrix.of fun i j =>
    inner ℝ (L (stdOrthonormalBasis ℝ F i)) (L (stdOrthonormalBasis ℝ F j))))

theorem gramDens_eq_normDet (L : F →ₗ[ℝ] W) : gramDens L = L.normDet := by
  have h := L.normDet_sq_eq_det_gram (stdOrthonormalBasis ℝ F)
  unfold gramDens
  have h' : (Matrix.of fun i j =>
      inner ℝ (L (stdOrthonormalBasis ℝ F i)) (L (stdOrthonormalBasis ℝ F j))) =
      Matrix.gram ℝ (fun x => L (stdOrthonormalBasis ℝ F x)) := by
    ext i j; simp [Matrix.gram]
  rw [h']
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h
  rw [← h, Real.sqrt_sq L.normDet_nonneg]

end Linear

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

/-- The Riemannian volume density of an arbitrary chart `Ξ`, at the chart point `w`. -/
noncomputable def chartDensity (Ξ : OpenPartialHomeomorph M F) (w : F) : ℝ :=
  gramDens (show F →ₗ[ℝ] TangentSpace 𝓘(ℝ, F) (Ξ.symm w) from
    (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) Ξ.symm w).toLinearMap)

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [IsManifold 𝓘(ℝ, F) ∞ M] in
theorem chartVolumeDensity_eq_chartDensity (x₀ : M) (z : F) :
    chartVolumeDensity F x₀ z = chartDensity (chartAt F x₀) z := by
  unfold chartVolumeDensity chartDensity gramDens
  rfl

end CutCur
