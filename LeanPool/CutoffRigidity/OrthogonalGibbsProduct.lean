/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.CutoffRigidity.PotentialSplitting
public import LeanPool.CutoffRigidity.ProductProbabilityNormalization

/-! # Full orthogonal product factorization of a separated Gibbs potential

The volume-preserving orthogonal affine coordinates turn the actual Gibbs
density into a product. Probability normalization identifies this product
with the product of its actual marginal probability measures.
-/
public section
namespace CutoffRigidity
open MeasureTheory Set
open scoped ENNReal
variable {E U F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- The product independence is derived from the actual potential split and
Gibbs normalization. Neither a marginal law nor factorization is a premise. -/
theorem normalized_separated_gibbs_map_product_marginals
    (A : E ≃ₗᵢ[ℝ] WithLp 2 (U × F)) (V : E → ℝ)
    (m : E) (Q : U → ℝ) (hQ : Measurable Q) (W : F → ℝ) (hW : Measurable W)
    (hsplit : ∀ u w, V (A.symm (WithLp.toLp 2 (u, w)) + m) = Q u + W w)
    (hp : IsProbabilityMeasure ((volume : Measure E).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-V x))))) :
    let μ := ((volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))).map
      (fun x => (A (x-m)).ofLp)
    μ= (μ.map Prod.fst).prod (μ.map Prod.snd) := by
  let μ := ((volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))).map
      (fun x => (A (x-m)).ofLp)
  have heq := separated_gibbs_map_orthogonal_product A V m Q hQ W hW hsplit
  have hprob : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr hp
  have hprodProb : IsProbabilityMeasure
      (((volume : Measure U).withDensity (fun u => ENNReal.ofReal (Real.exp (-Q u)))).prod
        ((volume : Measure F).withDensity (fun w => ENNReal.ofReal (Real.exp (-W w))))) := by
    rw [← heq]
    exact hprob
  have h := probability_product_eq_product_marginals
    ((volume : Measure U).withDensity (fun u => ENNReal.ofReal (Real.exp (-Q u))))
    ((volume : Measure F).withDensity (fun w => ENNReal.ofReal (Real.exp (-W w)))) hprodProb
  simpa only [← heq] using h

end CutoffRigidity
