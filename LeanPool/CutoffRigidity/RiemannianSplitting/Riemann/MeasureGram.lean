/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.MeasureDensity
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Gram determinant of an orthogonal sum

If `X₁..X_k` are orthonormal vectors orthogonal to the range of `u : G → W`, then
`(a, c) ↦ ∑ aᵢ Xᵢ + u c`, precomposed with a linear isometry `F ≃ ℝ^k ⊕₂ G`, has the same
Gram density as `u`.
-/

@[expose] public section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace CutCur

section

variable {k : ℕ} {G W F : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The map `(a, c) ↦ ∑ aᵢ Xᵢ + u c`. -/
noncomputable def sumMap (X : Fin k → W) (u : G →ₗ[ℝ] W) :
    WithLp 2 (EuclideanSpace ℝ (Fin k) × G) →ₗ[ℝ] W where
  toFun p := ∑ i, (WithLp.ofLp p).1 i • X i + u (WithLp.ofLp p).2
  map_add' p q := by
    simp only [WithLp.ofLp_add, Prod.fst_add, Prod.snd_add, PiLp.add_apply, add_smul,
      Finset.sum_add_distrib, map_add]
    abel
  map_smul' c p := by
    simp only [WithLp.ofLp_smul, Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul,
      RingHom.id_apply, map_smul, Finset.smul_sum, smul_add, mul_smul]

theorem gramDens_sumMap (X : Fin k → W) (hX : ∀ i j, inner ℝ (X i) (X j) = if i = j then (1 : ℝ)
    else 0)
    (u : G →ₗ[ℝ] W) (hu : ∀ i c, inner ℝ (X i) (u c) = 0)
    (J : WithLp 2 (EuclideanSpace ℝ (Fin k) × G) ≃ₗᵢ[ℝ] F) :
    gramDens ((sumMap X u) ∘ₗ J.symm.toLinearEquiv.toLinearMap) = gramDens u := by
  have hfr : Module.finrank ℝ F = Module.finrank ℝ (WithLp 2 (EuclideanSpace ℝ (Fin k) × G)) :=
    J.finrank_eq.symm
  rw [gramDens_eq_normDet, gramDens_eq_normDet,
    LinearMap.normDet_comp_of_finrank_eq _ _ hfr]
  have h1 : (J.symm.toLinearEquiv.toLinearMap).normDet = 1 :=
    J.symm.toLinearIsometry.normDet_eq_one
  rw [h1, mul_one]
  -- Gram matrix of `sumMap` on the product basis
  set b := (EuclideanSpace.basisFun (Fin k) ℝ).prod (stdOrthonormalBasis ℝ G) with hb
  have h2 := (sumMap X u).normDet_sq_eq_det_gram b
  have hl : ∀ i, (sumMap X u) (b (Sum.inl i)) = X i := by
    intro i
    simp only [hb, OrthonormalBasis.prod_apply, Sum.elim_inl, Function.comp_apply, sumMap,
      LinearMap.coe_mk, AddHom.coe_mk]
    simp [EuclideanSpace.basisFun_apply]
  have hr : ∀ j, (sumMap X u) (b (Sum.inr j)) = u (stdOrthonormalBasis ℝ G j) := by
    intro j
    simp [hb, OrthonormalBasis.prod_apply, sumMap]
  have hQ : (Matrix.gram ℝ fun x => (sumMap X u) (b x)) =
      Matrix.fromBlocks 1 0 0 (Matrix.of fun i j =>
        inner ℝ (u (stdOrthonormalBasis ℝ G i)) (u (stdOrthonormalBasis ℝ G j))) := by
    ext (i | i) (j | j)
    · simp only [Matrix.gram, Matrix.of_apply, hl, hX, Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
    · simp only [Matrix.gram, Matrix.of_apply, hl, hr, hu, Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply]
    · simp only [Matrix.gram, Matrix.of_apply, hl, hr, Matrix.fromBlocks_apply₂₁,
        Matrix.zero_apply]
      rw [real_inner_comm]; exact hu j _
    · simp only [Matrix.gram, Matrix.of_apply, hr, Matrix.fromBlocks_apply₂₂]
  rw [hQ, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul] at h2
  have h3 := u.normDet_sq_eq_det_gram (stdOrthonormalBasis ℝ G)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h2 h3
  have h4 : (Matrix.gram ℝ fun x => u (stdOrthonormalBasis ℝ G x)) = Matrix.of fun i j =>
        inner ℝ (u (stdOrthonormalBasis ℝ G i)) (u (stdOrthonormalBasis ℝ G j)) := by
    ext i j; simp [Matrix.gram]
  rw [h4] at h3
  exact (pow_left_inj₀ (LinearMap.normDet_nonneg _) (LinearMap.normDet_nonneg _) two_ne_zero).1
    (h2.trans h3.symm)

end

end CutCur
