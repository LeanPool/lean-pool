/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewCentered

/-!
# High-contrast homogenization: Provider.Response.ConstantSkewAnnealed

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Constant-skew covariance after annealing

The samplewise gradient and flux transformations commute with expectation
under coarse-block integrability.  Consequently the centered response is
unchanged after correcting the second load.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped Matrix

noncomputable section

variable {d : ℕ}

private theorem integrable_optimizer_gradient_apply
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (U : Domain d) (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    (p q : Vec d) (i : Fin d) :
    Integrable (fun a ↦ averageGradient U (a.coeffOn U)
      (centeredResponseOptimizer U a p q) i) P := by
  let X : BlockVec d := (-p, q)
  have hbase :=
    (integrable_coarseBlock_mulVec_apply hint X (Sum.inr i)).add
      (integrable_const (X.1 i))
  refine hbase.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  have h := blockAverage_eq (a.coeffOn U)
    (centeredResponseOptimizer_isMaximizer U a p q)
  rw [← coarseBlock_eq_coarseBlockMatrix a U] at h
  have hi := congrArg (fun Y : BlockVec d ↦ Y.1 i) h
  simpa only [blockMatVecMul_blockR, Prod.fst_add, Pi.add_apply,
    toFullBlockVec, X] using hi.symm

private theorem integrable_optimizer_flux_apply
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (U : Domain d) (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    (p q : Vec d) (i : Fin d) :
    Integrable (fun a ↦ averageFlux U (a.coeffOn U)
      (centeredResponseOptimizer U a p q) i) P := by
  let X : BlockVec d := (-p, q)
  have hbase :=
    (integrable_coarseBlock_mulVec_apply hint X (Sum.inl i)).add
      (integrable_const (X.2 i))
  refine hbase.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  have h := blockAverage_eq (a.coeffOn U)
    (centeredResponseOptimizer_isMaximizer U a p q)
  rw [← coarseBlock_eq_coarseBlockMatrix a U] at h
  have hi := congrArg (fun Y : BlockVec d ↦ Y.2 i) h
  simpa only [blockMatVecMul_blockR, Prod.snd_add, Pi.add_apply,
    toFullBlockVec, X] using hi.symm

/-- The separately annealed optimizer gradient is unchanged by recentering
after the load correction. -/
theorem annealedOptimizerGradient_subSkew
    {P : Measure (CoeffSpace d)} (U : Domain d)
    (g : Mat d) (hg : IsSkewMat g) (p q : Vec d) :
    (fun i ↦ ∫ a, averageGradient U ((a.subSkew g hg).coeffOn U)
      (centeredResponseOptimizer U (a.subSkew g hg) p q) i ∂P) =
      annealedOptimizerGradient P U p (q - matVecMul g p) := by
  funext i
  exact integral_congr_ae (_root_.Filter.Eventually.of_forall fun a ↦
    congrFun (averageGradient_centeredResponseOptimizer_subSkew U a g hg p q) i)

/-- The separately annealed optimizer flux is shifted by the constant skew
matrix applied to the annealed optimizer gradient. -/
theorem annealedOptimizerFlux_subSkew
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (U : Domain d) (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    (g : Mat d) (hg : IsSkewMat g) (p q : Vec d) :
    (fun i ↦ ∫ a, averageFlux U ((a.subSkew g hg).coeffOn U)
      (centeredResponseOptimizer U (a.subSkew g hg) p q) i ∂P) =
      annealedOptimizerFlux P U p (q - matVecMul g p) -
        matVecMul g
          (annealedOptimizerGradient P U p (q - matVecMul g p)) := by
  let q₀ := q - matVecMul g p
  funext i
  have hgradInt : ∀ j : Fin d, Integrable (fun a ↦
      averageGradient U (a.coeffOn U)
        (centeredResponseOptimizer U a p q₀) j) P :=
    fun j ↦ integrable_optimizer_gradient_apply U hint p q₀ j
  have hfluxInt : Integrable (fun a ↦ averageFlux U (a.coeffOn U)
      (centeredResponseOptimizer U a p q₀) i) P :=
    integrable_optimizer_flux_apply U hint p q₀ i
  have hmatInt : Integrable (fun a ↦ matVecMul g
      (averageGradient U (a.coeffOn U)
        (centeredResponseOptimizer U a p q₀)) i) P := by
    simpa only [matVecMul] using integrable_finsetSum Finset.univ
      (fun j _ ↦ (hgradInt j).const_mul (g i j))
  have hmatIntegral :
      (∫ a, matVecMul g (averageGradient U (a.coeffOn U)
        (centeredResponseOptimizer U a p q₀)) i ∂P) =
        matVecMul g (annealedOptimizerGradient P U p q₀) i := by
    simp only [matVecMul]
    rw [integral_finsetSum Finset.univ
      (fun j _ ↦ (hgradInt j).const_mul (g i j))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul]
    rfl
  change (∫ a, averageFlux U ((a.subSkew g hg).coeffOn U)
      (centeredResponseOptimizer U (a.subSkew g hg) p q) i ∂P) = _
  calc
    _ = ∫ a, averageFlux U (a.coeffOn U)
          (centeredResponseOptimizer U a p q₀) i -
        matVecMul g (averageGradient U (a.coeffOn U)
          (centeredResponseOptimizer U a p q₀)) i ∂P := by
      refine integral_congr_ae (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
      exact congrFun
        (averageFlux_centeredResponseOptimizer_subSkew U a g hg p q) i
    _ = (∫ a, averageFlux U (a.coeffOn U)
          (centeredResponseOptimizer U a p q₀) i ∂P) -
        ∫ a, matVecMul g (averageGradient U (a.coeffOn U)
          (centeredResponseOptimizer U a p q₀)) i ∂P := by
      rw [integral_sub hfluxInt hmatInt]
    _ = _ := by
      rw [hmatIntegral]
      rfl

/-- A constant-skew recentering preserves the centered response after the
second load is corrected.  Both annealed optimizer means are transformed
before their scalar product is simplified. -/
theorem centeredResponse_subSkew
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (U : Domain d) (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    (g : Mat d) (hg : IsSkewMat g) (p q : Vec d) :
    (∫ a, responseJ U ((a.subSkew g hg).coeffOn U) p q ∂P) -
        (1 / 2 : ℝ) *
          vecDot
            (fun i ↦ ∫ a, averageGradient U ((a.subSkew g hg).coeffOn U)
              (centeredResponseOptimizer U (a.subSkew g hg) p q) i ∂P)
            (fun i ↦ ∫ a, averageFlux U ((a.subSkew g hg).coeffOn U)
              (centeredResponseOptimizer U (a.subSkew g hg) p q) i ∂P) =
      centeredResponse P U p (q - matVecMul g p) := by
  let q₀ := q - matVecMul g p
  have hresponse :
      (∫ a, responseJ U ((a.subSkew g hg).coeffOn U) p q ∂P) =
        ∫ a, responseJ U (a.coeffOn U) p q₀ ∂P := by
    exact integral_congr_ae (_root_.Filter.Eventually.of_forall fun a ↦
      responseJ_subSkew U a g hg p q)
  have hgradient := annealedOptimizerGradient_subSkew (P := P) U g hg p q
  have hflux := annealedOptimizerFlux_subSkew U hint g hg p q
  let G := annealedOptimizerGradient P U p q₀
  let F := annealedOptimizerFlux P U p q₀
  have hgstar : Matrix.conjTranspose g = -g := by
    rwa [conjTranspose_eq_transpose']
  have hzero : vecDot G (matVecMul g G) = 0 := by
    simpa [vecDot, matVecMul] using! dotProduct_mulVec_of_skew hgstar G
  have hdot : vecDot G (F - matVecMul g G) = vecDot G F := by
    calc
      _ = vecDot G F - vecDot G (matVecMul g G) := by
        simp only [vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      _ = _ := by rw [hzero, sub_zero]
  unfold centeredResponse
  rw [hresponse, hgradient, hflux]
  exact congrArg (fun z ↦ (∫ a, responseJ U (a.coeffOn U) p q₀ ∂P) -
    (1 / 2 : ℝ) * z) hdot

end

end HCPolySupport.HighContrast.Response
