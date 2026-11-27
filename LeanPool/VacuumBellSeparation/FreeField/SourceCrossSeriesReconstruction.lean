/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ProductSourceNuclearSeries
public import LeanPool.VacuumBellSeparation.Gaussian.CrossRankOneMatrixElements

/-!
# Reconstructing the original source covariance operator from test moments

Norm summability first constructs a bounded cross operator. The scalar
series on the literal dense real source tests identifies its full complex
extension with the already defined product-source Gram difference.
The vector-representation and scalar-kernel identities are explicit here;
the latter is supplied by the actual localized moment calculation.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation

open Gaussian Gaussian.HilbertComplexification

variable {m : ℝ} (hm : 0 < m) (U W : Set (EuclideanSpace ℝ (Fin 3)))
  {ι : Type*}

/-- Product source real test defined as `WithLp.toLp 2 ((x.1 : SourceHilbert hm U), (x.2 :
SourceHilbert hm W))`. -/
def productSourceRealTest (x : SourceTestSpace hm U × SourceTestSpace hm W) :
    WithLp 2 (SourceHilbert hm U × SourceHilbert hm W) :=
  WithLp.toLp 2 ((x.1 : SourceHilbert hm U), (x.2 : SourceHilbert hm W))

theorem denseRange_productSourceRealTest : DenseRange (productSourceRealTest hm U W) := by
  have hd := (UniformSpace.Completion.denseRange_coe (α := SourceTestSpace hm U)).prodMap
    (UniformSpace.Completion.denseRange_coe (α := SourceTestSpace hm W))
  exact (WithLp.homeomorphProd 2 (SourceHilbert hm U)
    (SourceHilbert hm W)).symm.surjective.denseRange.comp
    hd (WithLp.homeomorphProd 2 (SourceHilbert hm U) (SourceHilbert hm W)).symm.continuous

theorem hasSum_productSource_cross_of_test_moments
    (u : ι → ComplexSourceHilbert hm U) (v : ι → ComplexSourceHilbert hm W)
    (L : ι → SourceTestSpace hm U → ℝ) (M : ι → SourceTestSpace hm W → ℝ)
    (hs : Summable fun i => ‖u i‖ * ‖v i‖)
    (hu : ∀ i (x : SourceTestSpace hm U),
      inner ℂ (ofReal (x : SourceHilbert hm U)) (u i) = (L i x : ℂ))
    (hv : ∀ i (y : SourceTestSpace hm W),
      inner ℂ (ofReal (y : SourceHilbert hm W)) (v i) = (M i y : ℂ))
    (hkernel : ∀ x y, HasSum (fun i => L i x * M i y)
      (inner ℝ (sourceEmbedding hm U (x : SourceHilbert hm U))
        (sourceEmbedding hm W (y : SourceHilbert hm W)))) :
    HasSum (fun i => crossRankOne (u i) (v i))
      ((productSourceComplexEquiv hm U W).conjStarAlgEquiv
        (complexify (productSourceCovariancePerturbation hm U W))) := by
  let e := productSourceComplexEquiv hm U W
  let X := ∑' i, crossRankOne (u i) (v i)
  have hX : HasSum (fun i => crossRankOne (u i) (v i)) X :=
    (summable_norm_crossRankOne hs).of_norm.hasSum
  have heq : e.symm.conjStarAlgEquiv X =
      complexify (productSourceCovariancePerturbation hm U W) := by
    apply complexification_operator_ext_dense_real
      (denseRange_productSourceRealTest hm U W) (denseRange_productSourceRealTest hm U W)
    intro x y
    let tx := e (ofReal (productSourceRealTest hm U W x))
    let ty := e (ofReal (productSourceRealTest hm U W y))
    have hi := (hX.mapL (ContinuousLinearMap.apply ℂ
      (WithLp 2 (ComplexSourceHilbert hm U × ComplexSourceHilbert hm W)) tx)).mapL (innerSL ℂ ty)
    have hk := ((hkernel y.1 x.2).add (hkernel x.1 y.2)).mapL Complex.ofRealCLM
    have ht (i : ι) : inner ℂ ty (crossRankOne (u i) (v i) tx) =
        ((L i y.1 * M i x.2 + L i x.1 * M i y.2 : ℝ) : ℂ) := by
      change inner ℂ (WithLp.toLp 2 (ofReal (y.1 : SourceHilbert hm U),
          ofReal (y.2 : SourceHilbert hm W)))
        (crossRankOne (u i) (v i) (WithLp.toLp 2 (ofReal (x.1 : SourceHilbert hm U),
          ofReal (x.2 : SourceHilbert hm W)))) = _
      rw [inner_crossRankOne_real_moments _ _ _ _ _ _ _ _ _ _
        (hu i y.1) (hu i x.1) (hv i y.2) (hv i x.2)]
      congr 1
      ring
    have hscl := (hi.congr_fun (fun i => (ht i).symm)).unique hk
    calc
      _ = inner ℂ ty (X tx) := by
        rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
        rw [← e.inner_map_map]
        simp only [LinearIsometryEquiv.apply_symm_apply]
        rfl
      _ = ((inner ℝ (sourceEmbedding hm U (y.1 : SourceHilbert hm U))
          (sourceEmbedding hm W (x.2 : SourceHilbert hm W)) +
        inner ℝ (sourceEmbedding hm U (x.1 : SourceHilbert hm U))
          (sourceEmbedding hm W (y.2 : SourceHilbert hm W)) : ℝ) : ℂ) := hscl
      _ = _ := by
        rw [complexify_ofReal, inner_complexification_ofReal,
          inner_productSourceCovariancePerturbation]
        congr 1
        change _ = inner ℝ (sourceEmbedding hm U (y.1 : SourceHilbert hm U))
          (sourceEmbedding hm W (x.2 : SourceHilbert hm W)) +
          inner ℝ (sourceEmbedding hm W (y.2 : SourceHilbert hm W))
            (sourceEmbedding hm U (x.1 : SourceHilbert hm U))
        rw [real_inner_comm (sourceEmbedding hm W (y.2 : SourceHilbert hm W))]
  have hfinal : e.conjStarAlgEquiv (complexify (productSourceCovariancePerturbation hm U W)) = X
    := by
    rw [← heq, ← LinearIsometryEquiv.symm_conjStarAlgEquiv, StarAlgEquiv.apply_symm_apply]
  rwa [← hfinal] at hX

end VacuumBellSeparation
