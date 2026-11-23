/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.MeasureDensity
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import TauCeti.Analysis.InnerProductSpace.NormDet

/-! # Gram determinant of an orthogonal sum

If `X₁..X_k` are orthonormal vectors orthogonal to the range of `u : G → W`, then
`(a, c) ↦ ∑ aᵢ Xᵢ + u c`, precomposed with a linear isometry `F ≃ ℝ^k ⊕₂ G`, has the same
Gram density as `u`.
-/

@[expose] public section

open Bundle MeasureTheory Module Set
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace CutCur

section

variable {k : ℕ} {G W F : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Extend a finite Euclidean frame linearly. -/
noncomputable def frameLinearMap (X : Fin k → W) : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] W :=
  (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.constr ℝ X

private theorem frameLinearMap_apply (X : Fin k → W) (v : EuclideanSpace ℝ (Fin k)) :
    frameLinearMap X v = ∑ i, v i • X i := by
  unfold frameLinearMap
  rw [Basis.constr_apply_fintype]
  rfl

/-- The map `(a, c) ↦ ∑ aᵢ Xᵢ + u c`. -/
noncomputable def sumMap (X : Fin k → W) (u : G →ₗ[ℝ] W) :
    WithLp 2 (EuclideanSpace ℝ (Fin k) × G) →ₗ[ℝ] W :=
  (frameLinearMap X).coprod u ∘ₗ
    (WithLp.linearEquiv 2 ℝ (EuclideanSpace ℝ (Fin k) × G)).toLinearMap

omit [FiniteDimensional ℝ G] in
theorem sumMap_apply (X : Fin k → W) (u : G →ₗ[ℝ] W)
    (p : WithLp 2 (EuclideanSpace ℝ (Fin k) × G)) :
    sumMap X u p = (∑ i, (WithLp.ofLp p).1 i • X i) + u (WithLp.ofLp p).2 := by
  change frameLinearMap X (WithLp.ofLp p).1 + u (WithLp.ofLp p).2 = _
  rw [frameLinearMap_apply]

private theorem frameLinearMap_normDet (X : Fin k → W)
    (hX : ∀ i j, inner ℝ (X i) (X j) = if i = j then (1 : ℝ) else 0) :
    (frameLinearMap X).normDet = 1 := by
  let basis := EuclideanSpace.basisFun (Fin k) ℝ
  have hframe : frameLinearMap X ∘ basis.toBasis = X := by
    funext i
    exact basis.toBasis.constr_basis ℝ X i
  have horthonormal : Orthonormal ℝ (frameLinearMap X ∘ basis.toBasis) := by
    rw [hframe]
    exact (orthonormal_iff_ite (𝕜 := ℝ)).2 hX
  let isometry : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] W :=
    (frameLinearMap X).isometryOfOrthonormal (v := basis.toBasis) basis.orthonormal horthonormal
  have hmap : isometry.toLinearMap = frameLinearMap X :=
    LinearMap.isometryOfOrthonormal_toLinearMap _ basis.orthonormal horthonormal
  rw [← hmap]
  exact isometry.normDet_eq_one

private theorem normDet_sumMap (X : Fin k → W)
    (hX : ∀ i j, inner ℝ (X i) (X j) = if i = j then (1 : ℝ) else 0)
    (u : G →ₗ[ℝ] W) (hu : ∀ i c, inner ℝ (X i) (u c) = 0) :
    (sumMap X u).normDet = u.normDet := by
  have horthogonal (v : EuclideanSpace ℝ (Fin k)) (w : G) :
      inner ℝ (frameLinearMap X v) (u w) = 0 := by
    simp only [frameLinearMap_apply, sum_inner, real_inner_smul_left, hu, mul_zero,
      Finset.sum_const_zero]
  rw [sumMap, LinearMap.normDet_coprod_of_orthogonal _ _ horthogonal,
    frameLinearMap_normDet X hX, one_mul]

theorem gramDens_sumMap (X : Fin k → W) (hX : ∀ i j, inner ℝ (X i) (X j) = if i = j then (1 : ℝ)
    else 0)
    (u : G →ₗ[ℝ] W) (hu : ∀ i c, inner ℝ (X i) (u c) = 0)
    (J : WithLp 2 (EuclideanSpace ℝ (Fin k) × G) ≃ₗᵢ[ℝ] F) :
    gramDens ((sumMap X u) ∘ₗ J.symm.toLinearEquiv.toLinearMap) = gramDens u := by
  have hfr : Module.finrank ℝ F = Module.finrank ℝ (WithLp 2 (EuclideanSpace ℝ (Fin k) × G)) :=
    J.finrank_eq.symm
  rw [gramDens_eq_normDet, gramDens_eq_normDet, LinearMap.normDet_comp_of_finrank_eq _ _ hfr,
    show J.symm.toLinearEquiv.toLinearMap.normDet = 1 from J.symm.toLinearIsometry.normDet_eq_one,
    mul_one]
  exact normDet_sumMap X hX u hu

end

end CutCur
