/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewAnnealed
public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseAdjointAnnealed

/-!
# High-contrast homogenization: Provider.Response.ConstantSkewAdjoint

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Constant-skew covariance for the adjoint response

Transposition reverses the sign of a skew recentering.  The adjoint optimizer
therefore has the opposite load correction and flux shift from the primal
optimizer, while its centered response is again unchanged.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped Matrix

noncomputable section

variable {d : ℕ}

private theorem matVecMul_neg_const (g : Mat d) (x : Vec d) :
    matVecMul (-g) x = -matVecMul g x := by
  funext i
  simp [matVecMul]

/-- The averaged adjoint optimizer gradient is unchanged after applying the
oppositely signed load correction. -/
theorem averageGradient_centeredAdjointOptimizer_subSkew
    (U : Domain d) (a : CoeffSpace d) (g : Mat d) (hg : IsSkewMat g)
    (p q : Vec d) :
    averageGradient U ((a.subSkew g hg).transpose.coeffOn U)
        (centeredAdjointOptimizer U (a.subSkew g hg) p q) =
      averageGradient U (a.transpose.coeffOn U)
        (centeredAdjointOptimizer U a p (q + matVecMul g p)) := by
  unfold centeredAdjointOptimizer
  rw [CoeffSpace.transpose_subSkew]
  have h := averageGradient_centeredResponseOptimizer_subSkew U a.transpose
    (-g) (isSkewMat_neg hg) p q
  have hload : q - matVecMul (-g) p = q + matVecMul g p := by
    rw [matVecMul_neg_const, sub_neg_eq_add]
  rw [hload] at h
  exact h

/-- The averaged adjoint optimizer flux gains the skew matrix applied to the
averaged adjoint optimizer gradient. -/
theorem averageFlux_centeredAdjointOptimizer_subSkew
    (U : Domain d) (a : CoeffSpace d) (g : Mat d) (hg : IsSkewMat g)
    (p q : Vec d) :
    averageFlux U ((a.subSkew g hg).transpose.coeffOn U)
        (centeredAdjointOptimizer U (a.subSkew g hg) p q) =
      averageFlux U (a.transpose.coeffOn U)
          (centeredAdjointOptimizer U a p (q + matVecMul g p)) +
        matVecMul g
          (averageGradient U (a.transpose.coeffOn U)
            (centeredAdjointOptimizer U a p (q + matVecMul g p))) := by
  unfold centeredAdjointOptimizer
  rw [CoeffSpace.transpose_subSkew]
  have h := averageFlux_centeredResponseOptimizer_subSkew U a.transpose
    (-g) (isSkewMat_neg hg) p q
  have hload : q - matVecMul (-g) p = q + matVecMul g p := by
    rw [matVecMul_neg_const, sub_neg_eq_add]
  rw [hload, matVecMul_neg_const, sub_neg_eq_add] at h
  exact h

private theorem integrable_adjoint_optimizer_gradient_apply
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (U : Domain d) (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    (p q : Vec d) (i : Fin d) :
    Integrable (fun a ↦ averageGradient U (a.transpose.coeffOn U)
      (centeredAdjointOptimizer U a p q) i) P := by
  let X : BlockVec d := (-p, q)
  have hbase :=
    (integrable_adjoint_coarseBlock_mulVec_apply U hint X (Sum.inr i)).add
      (integrable_const (X.1 i))
  refine hbase.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  have h := blockAverage_eq (a.transpose.coeffOn U)
    (centeredAdjointOptimizer_isMaximizer U a p q)
  rw [← coarseBlock_eq_coarseBlockMatrix a.transpose U] at h
  have hi := congrArg (fun Y : BlockVec d ↦ Y.1 i) h
  simpa only [blockMatVecMul_blockR, Prod.fst_add, Pi.add_apply,
    toFullBlockVec, X] using hi.symm

private theorem integrable_adjoint_optimizer_flux_apply
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (U : Domain d) (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    (p q : Vec d) (i : Fin d) :
    Integrable (fun a ↦ averageFlux U (a.transpose.coeffOn U)
      (centeredAdjointOptimizer U a p q) i) P := by
  let X : BlockVec d := (-p, q)
  have hbase :=
    (integrable_adjoint_coarseBlock_mulVec_apply U hint X (Sum.inl i)).add
      (integrable_const (X.2 i))
  refine hbase.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  have h := blockAverage_eq (a.transpose.coeffOn U)
    (centeredAdjointOptimizer_isMaximizer U a p q)
  rw [← coarseBlock_eq_coarseBlockMatrix a.transpose U] at h
  have hi := congrArg (fun Y : BlockVec d ↦ Y.2 i) h
  simpa only [blockMatVecMul_blockR, Prod.snd_add, Pi.add_apply,
    toFullBlockVec, X] using hi.symm

/-- The separately annealed adjoint optimizer gradient has the positive load
correction associated with coefficient transposition. -/
theorem annealedAdjointOptimizerGradient_subSkew
    {P : Measure (CoeffSpace d)} (U : Domain d)
    (g : Mat d) (hg : IsSkewMat g) (p q : Vec d) :
    (fun i ↦ ∫ a, averageGradient U ((a.subSkew g hg).transpose.coeffOn U)
      (centeredAdjointOptimizer U (a.subSkew g hg) p q) i ∂P) =
      annealedAdjointOptimizerGradient P U p (q + matVecMul g p) := by
  funext i
  exact integral_congr_ae (_root_.Filter.Eventually.of_forall fun a ↦ congrFun
    (averageGradient_centeredAdjointOptimizer_subSkew U a g hg p q) i)

/-- The separately annealed adjoint optimizer flux gains the skew matrix
applied to the annealed adjoint optimizer gradient. -/
theorem annealedAdjointOptimizerFlux_subSkew
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (U : Domain d) (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    (g : Mat d) (hg : IsSkewMat g) (p q : Vec d) :
    (fun i ↦ ∫ a, averageFlux U ((a.subSkew g hg).transpose.coeffOn U)
      (centeredAdjointOptimizer U (a.subSkew g hg) p q) i ∂P) =
      annealedAdjointOptimizerFlux P U p (q + matVecMul g p) +
        matVecMul g
          (annealedAdjointOptimizerGradient P U p (q + matVecMul g p)) := by
  let q₀ := q + matVecMul g p
  funext i
  have hgradInt : ∀ j : Fin d, Integrable (fun a ↦
      averageGradient U (a.transpose.coeffOn U)
        (centeredAdjointOptimizer U a p q₀) j) P :=
    fun j ↦ integrable_adjoint_optimizer_gradient_apply U hint p q₀ j
  have hfluxInt : Integrable (fun a ↦ averageFlux U (a.transpose.coeffOn U)
      (centeredAdjointOptimizer U a p q₀) i) P :=
    integrable_adjoint_optimizer_flux_apply U hint p q₀ i
  have hmatInt : Integrable (fun a ↦ matVecMul g
      (averageGradient U (a.transpose.coeffOn U)
        (centeredAdjointOptimizer U a p q₀)) i) P := by
    simpa only [matVecMul] using integrable_finsetSum Finset.univ
      (fun j _ ↦ (hgradInt j).const_mul (g i j))
  have hmatIntegral :
      (∫ a, matVecMul g (averageGradient U (a.transpose.coeffOn U)
        (centeredAdjointOptimizer U a p q₀)) i ∂P) =
        matVecMul g (annealedAdjointOptimizerGradient P U p q₀) i := by
    simp only [matVecMul]
    rw [integral_finsetSum Finset.univ
      (fun j _ ↦ (hgradInt j).const_mul (g i j))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul]
    rfl
  change (∫ a, averageFlux U ((a.subSkew g hg).transpose.coeffOn U)
      (centeredAdjointOptimizer U (a.subSkew g hg) p q) i ∂P) = _
  calc
    _ = ∫ a, averageFlux U (a.transpose.coeffOn U)
          (centeredAdjointOptimizer U a p q₀) i +
        matVecMul g (averageGradient U (a.transpose.coeffOn U)
          (centeredAdjointOptimizer U a p q₀)) i ∂P := by
      refine integral_congr_ae (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
      exact congrFun
        (averageFlux_centeredAdjointOptimizer_subSkew U a g hg p q) i
    _ = (∫ a, averageFlux U (a.transpose.coeffOn U)
          (centeredAdjointOptimizer U a p q₀) i ∂P) +
        ∫ a, matVecMul g (averageGradient U (a.transpose.coeffOn U)
          (centeredAdjointOptimizer U a p q₀)) i ∂P := by
      rw [integral_add hfluxInt hmatInt]
    _ = _ := by
      rw [hmatIntegral]
      rfl

/-- A constant-skew recentering preserves the centered adjoint response after
the oppositely signed load correction. -/
theorem centeredAdjointResponse_subSkew
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (U : Domain d) (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    (g : Mat d) (hg : IsSkewMat g) (p q : Vec d) :
    (∫ a, responseJ U ((a.subSkew g hg).transpose.coeffOn U) p q ∂P) -
        (1 / 2 : ℝ) *
          vecDot
            (fun i ↦ ∫ a, averageGradient U
              ((a.subSkew g hg).transpose.coeffOn U)
              (centeredAdjointOptimizer U (a.subSkew g hg) p q) i ∂P)
            (fun i ↦ ∫ a, averageFlux U
              ((a.subSkew g hg).transpose.coeffOn U)
              (centeredAdjointOptimizer U (a.subSkew g hg) p q) i ∂P) =
      centeredAdjointResponse P U p (q + matVecMul g p) := by
  let q₀ := q + matVecMul g p
  have hresponse :
      (∫ a, responseJ U ((a.subSkew g hg).transpose.coeffOn U) p q ∂P) =
        ∫ a, responseJ U (a.transpose.coeffOn U) p q₀ ∂P := by
    refine integral_congr_ae (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
    change responseJ U ((a.subSkew g hg).transpose.coeffOn U) p q =
      responseJ U (a.transpose.coeffOn U) p q₀
    rw [CoeffSpace.transpose_subSkew]
    have h := responseJ_subSkew U a.transpose (-g) (isSkewMat_neg hg) p q
    have hload : q - matVecMul (-g) p = q₀ := by
      rw [matVecMul_neg_const, sub_neg_eq_add]
    rw [hload] at h
    exact h
  have hgradient :=
    annealedAdjointOptimizerGradient_subSkew (P := P) U g hg p q
  have hflux := annealedAdjointOptimizerFlux_subSkew U hint g hg p q
  let G := annealedAdjointOptimizerGradient P U p q₀
  let F := annealedAdjointOptimizerFlux P U p q₀
  have hgstar : Matrix.conjTranspose g = -g := by
    rwa [conjTranspose_eq_transpose']
  have hzero : vecDot G (matVecMul g G) = 0 := by
    simpa [vecDot, matVecMul] using! dotProduct_mulVec_of_skew hgstar G
  have hdot : vecDot G (F + matVecMul g G) = vecDot G F := by
    calc
      _ = vecDot G F + vecDot G (matVecMul g G) := by
        simp only [vecDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      _ = _ := by rw [hzero, add_zero]
  unfold centeredAdjointResponse
  rw [hresponse, hgradient, hflux]
  exact congrArg (fun z ↦ (∫ a, responseJ U (a.transpose.coeffOn U) p q₀ ∂P) -
    (1 / 2 : ℝ) * z) hdot

end

end HCPolySupport.HighContrast.Response
