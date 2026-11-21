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

theorem orthogonalProductCoordinates_measurePreserving
    (A : E ≃ₗᵢ[ℝ] WithLp 2 (U × F)) :
    MeasurePreserving (fun x => (A x).ofLp) (volume : Measure E) ((volume : Measure U).prod volume)
      :=
  (WithLp.volume_preserving_ofLp U F).comp (LinearIsometryEquiv.measurePreserving A)

theorem separated_gibbs_map_orthogonal_product
    (A : E ≃ₗᵢ[ℝ] WithLp 2 (U × F)) (V : E → ℝ) (_hV : Measurable V)
    (m : E) (Q : U → ℝ) (hQ : Measurable Q) (W : F → ℝ) (hW : Measurable W)
    (hsplit : ∀ u w, V (A.symm (WithLp.toLp 2 (u, w)) + m) = Q u + W w) :
    ((volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))).map
      (fun x => (A (x-m)).ofLp) =
        ((volume : Measure U).withDensity (fun u => ENNReal.ofReal (Real.exp (-Q u)))).prod
          ((volume : Measure F).withDensity (fun w => ENNReal.ofReal (Real.exp (-W w)))) := by
  let g := fun z : U × F => ENNReal.ofReal (Real.exp (-(Q z.1+W z.2)))
  have hg : Measurable g := by fun_prop
  have hf : Measurable (fun x : E => (A x).ofLp) := by fun_prop
  have hsplit' (y : E) : ENNReal.ofReal (Real.exp (-V (y+m)))=g (A y).ofLp := by
    have hh := hsplit (A y).ofLp.1 (A y).ofLp.2
    have he : WithLp.toLp 2 ((A y).ofLp.1,(A y).ofLp.2)=A y := rfl
    rw [he,A.symm_apply_apply] at hh
    rw [hh]
  have htrans : ((volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))).map
      (fun x => x-m) = (volume : Measure E).withDensity (fun y => g (A y).ofLp) := by
    have hh := map_withDensity_comp (volume : Measure E) (fun x => x+(-m))
      (fun y => g (A y).ofLp) (by fun_prop) (hg.comp hf)
    rw [(measurePreserving_add_right (volume : Measure E) (-m)).map_eq] at hh
    have hdensity : (fun x : E => ENNReal.ofReal (Real.exp (-V x))) =
        fun x => g (A (x+(-m))).ofLp := by
      funext x
      rw [← hsplit']
      simp
    rw [← hdensity] at hh
    simpa only [sub_eq_add_neg] using hh
  calc
    _ = (((volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))).map
        (fun x => x-m)).map (fun y => (A y).ofLp) := by
      rw [Measure.map_map hf (by fun_prop)]
      rfl
    _ = ((volume : Measure E).withDensity (fun y => g (A y).ofLp)).map (fun y => (A y).ofLp)
      := by rw [htrans]
    _ = ((volume : Measure E).map (fun y => (A y).ofLp)).withDensity g
      := map_withDensity_comp _ _ _ hf hg
    _ = ((volume : Measure U).prod (volume : Measure F)).withDensity g := by
      rw [(orthogonalProductCoordinates_measurePreserving A).map_eq]
    _ = _ := by
      rw [prod_withDensity (by fun_prop : Measurable (fun u => ENNReal.ofReal (Real.exp (-Q u))))
        (by fun_prop : Measurable (fun w => ENNReal.ofReal (Real.exp (-W w))))]
      congr 1
      funext z
      dsimp only [g]
      rw [neg_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)]

/-- The product independence is derived from the actual potential split and
Gibbs normalization. Neither a marginal law nor factorization is a premise. -/
theorem normalized_separated_gibbs_map_product_marginals
    (A : E ≃ₗᵢ[ℝ] WithLp 2 (U × F)) (V : E → ℝ) (hV : Measurable V)
    (m : E) (Q : U → ℝ) (hQ : Measurable Q) (W : F → ℝ) (hW : Measurable W)
    (hsplit : ∀ u w, V (A.symm (WithLp.toLp 2 (u, w)) + m) = Q u + W w)
    (hp : IsProbabilityMeasure ((volume : Measure E).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-V x))))) :
    let μ := ((volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))).map
      (fun x => (A (x-m)).ofLp)
    μ= (μ.map Prod.fst).prod (μ.map Prod.snd) := by
  let μ := ((volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))).map
      (fun x => (A (x-m)).ofLp)
  have heq := separated_gibbs_map_orthogonal_product A V hV m Q hQ W hW hsplit
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
