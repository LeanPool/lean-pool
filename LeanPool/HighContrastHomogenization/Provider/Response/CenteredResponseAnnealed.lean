/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseCarriers

/-!
# High-contrast homogenization: Provider.Response.CenteredResponseAnnealed

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Annealed response energy and optimizer means

The scalar response and the two spatial averages of its canonical optimizer are
quadratic and linear readings of the same coarse block.  Entrywise
integrability of that block therefore identifies their annealed values with the
corresponding readings of the annealed block.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The response value is the coarse-block quadratic form at the signed load. -/
theorem responseJ_eq_coarseBlock (U : Domain d) (a : CoeffSpace d)
    (p q : Vec d) :
    responseJ U (a.coeffOn U) p q =
      (1 / 2 : ℝ) * blockVecDot ((-p, q) : BlockVec d)
        (blockMatVecMul (coarseBlock (U : Set (Vec d)) a)
          ((-p, q) : BlockVec d)) - vecDot p q := by
  have h := Internal.Ch02.BookCh02.responseJ_eq_block_quadratic
    U (a.coeffOn U) p q
  rwa [← coarseBlock_eq_coarseBlockMatrix a U] at h

/-- Each coordinate of a coarse block applied to a fixed doubled vector is
integrable under an integrable coefficient law. -/
theorem integrable_coarseBlock_mulVec_apply
    {P : Measure (CoeffSpace d)} {U : Set (Vec d)}
    (hint : HasIntegrableCoarseBlock P U) (X : BlockVec d)
    (α : BlockCoord d) :
    Integrable (fun a =>
      toFullBlockVec (blockMatVecMul (coarseBlock U a) X) α) P := by
  have hsum : Integrable (fun a =>
      ∑ β : BlockCoord d,
        blockMatEntry (coarseBlock U a) α β * toFullBlockVec X β) P :=
    integrable_finsetSum _ fun β _ => (hint α β).mul_const _
  simpa only [toFullBlockVec_blockMatVecMul, Matrix.mulVec,
    toFullBlockMat_eq_blockMatEntry] using! hsum

/-- The quadratic form of the random coarse block is integrable. -/
theorem integrable_coarseBlock_quadratic
    {P : Measure (CoeffSpace d)} {U : Set (Vec d)}
    (hint : HasIntegrableCoarseBlock P U) (X : BlockVec d) :
    Integrable (fun a => blockVecDot X
      (blockMatVecMul (coarseBlock U a) X)) P := by
  have hrow : ∀ α : BlockCoord d, Integrable (fun a =>
      toFullBlockVec X α *
        toFullBlockVec (blockMatVecMul (coarseBlock U a) X) α) P :=
    fun α => (integrable_coarseBlock_mulVec_apply hint X α).const_mul _
  have hsum := integrable_finsetSum (μ := P) Finset.univ
    fun α (_ : α ∈ (Finset.univ : Finset (BlockCoord d))) => hrow α
  refine hsum.congr (_root_.Filter.Eventually.of_forall fun a => ?_)
  simpa only [dotProduct] using
    (dotProduct_toFullBlockVec X (blockMatVecMul (coarseBlock U a) X))

/-- Integration commutes with applying the coarse block to a deterministic
doubled vector. -/
theorem integral_coarseBlock_mulVec
    {P : Measure (CoeffSpace d)} {U : Set (Vec d)}
    (hint : HasIntegrableCoarseBlock P U) (X : BlockVec d) :
    (fun α => ∫ a,
      toFullBlockVec (blockMatVecMul (coarseBlock U a) X) α ∂P) =
      toFullBlockVec (blockMatVecMul (annealedBlock P U) X) := by
  funext α
  simp only [toFullBlockVec_blockMatVecMul, Matrix.mulVec, dotProduct,
    toFullBlockMat_eq_blockMatEntry]
  rw [integral_finsetSum _ fun β _ => (hint α β).mul_const _]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [integral_mul_const, ← blockMatEntry_annealedBlock]

/-- The annealed response energy is the annealed-block quadratic form. -/
theorem annealed_responseJ_eq {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d))) (p q : Vec d) :
    (∫ a, responseJ U (a.coeffOn U) p q ∂P) =
      (1 / 2 : ℝ) * blockVecDot ((-p, q) : BlockVec d)
        (blockMatVecMul (annealedBlock P (U : Set (Vec d)))
          ((-p, q) : BlockVec d)) - vecDot p q := by
  let X : BlockVec d := (-p, q)
  have hquad := integrable_coarseBlock_quadratic hint X
  calc
    (∫ a, responseJ U (a.coeffOn U) p q ∂P) =
        ∫ a, (1 / 2 : ℝ) * blockVecDot X
          (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) X) -
            vecDot p q ∂P := by
      refine integral_congr_ae (_root_.Filter.Eventually.of_forall fun a => ?_)
      exact responseJ_eq_coarseBlock U a p q
    _ = (1 / 2 : ℝ) *
          (∫ a, blockVecDot X
            (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) X) ∂P) -
          vecDot p q := by
      rw [integral_sub (hquad.const_mul _) (integrable_const _),
        integral_const_mul]
      simp
    _ = (1 / 2 : ℝ) * blockVecDot X
          (blockMatVecMul (annealedBlock P (U : Set (Vec d))) X) -
            vecDot p q := by
      rw [blockVecDot_blockMatVecMul_annealedBlock hint]

/-- The two separately annealed optimizer averages are the two rows of
`(R E + I)(-p,q)`. -/
theorem annealed_optimizer_average_eq {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d))) (p q : Vec d) :
    ((annealedOptimizerGradient P U p q,
        annealedOptimizerFlux P U p q) : BlockVec d) =
      blockMatVecMul (blockR d)
          (blockMatVecMul (annealedBlock P (U : Set (Vec d)))
            ((-p, q) : BlockVec d)) +
        ((-p, q) : BlockVec d) := by
  let X : BlockVec d := (-p, q)
  have hintMul := integral_coarseBlock_mulVec hint X
  apply Prod.ext
  · funext i
    have hpoint : ∀ a : CoeffSpace d,
        averageGradient U (a.coeffOn U)
            (centeredResponseOptimizer U a p q) i =
          toFullBlockVec
              (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) X)
              (Sum.inr i) + X.1 i := by
      intro a
      have h := blockAverage_eq (a.coeffOn U)
        (centeredResponseOptimizer_isMaximizer U a p q)
      rw [← coarseBlock_eq_coarseBlockMatrix a U] at h
      have hi := congrArg (fun Y : BlockVec d => Y.1 i) h
      simpa only [blockMatVecMul_blockR, Prod.fst_add, Pi.add_apply,
        toFullBlockVec, X] using hi
    change (∫ a, averageGradient U (a.coeffOn U)
      (centeredResponseOptimizer U a p q) i ∂P) = _
    calc
      (∫ a, averageGradient U (a.coeffOn U)
          (centeredResponseOptimizer U a p q) i ∂P) =
          ∫ a, toFullBlockVec
              (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) X)
              (Sum.inr i) + X.1 i ∂P := by
        refine integral_congr_ae (_root_.Filter.Eventually.of_forall fun a => ?_)
        exact hpoint a
      _ = (∫ a, toFullBlockVec
              (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) X)
              (Sum.inr i) ∂P) + X.1 i := by
        rw [integral_add (integrable_coarseBlock_mulVec_apply hint X (Sum.inr i))
          (integrable_const _)]
        simp
      _ = toFullBlockVec
              (blockMatVecMul (annealedBlock P (U : Set (Vec d))) X)
              (Sum.inr i) + X.1 i := by
        rw [congrFun hintMul (Sum.inr i)]
      _ = (blockMatVecMul (blockR d)
            (blockMatVecMul (annealedBlock P (U : Set (Vec d))) X) + X).1 i := by
        rw [blockMatVecMul_blockR]
        rfl
  · funext i
    have hpoint : ∀ a : CoeffSpace d,
        averageFlux U (a.coeffOn U)
            (centeredResponseOptimizer U a p q) i =
          toFullBlockVec
              (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) X)
              (Sum.inl i) + X.2 i := by
      intro a
      have h := blockAverage_eq (a.coeffOn U)
        (centeredResponseOptimizer_isMaximizer U a p q)
      rw [← coarseBlock_eq_coarseBlockMatrix a U] at h
      have hi := congrArg (fun Y : BlockVec d => Y.2 i) h
      simpa only [blockMatVecMul_blockR, Prod.snd_add, Pi.add_apply,
        toFullBlockVec, X] using hi
    change (∫ a, averageFlux U (a.coeffOn U)
      (centeredResponseOptimizer U a p q) i ∂P) = _
    calc
      (∫ a, averageFlux U (a.coeffOn U)
          (centeredResponseOptimizer U a p q) i ∂P) =
          ∫ a, toFullBlockVec
              (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) X)
              (Sum.inl i) + X.2 i ∂P := by
        refine integral_congr_ae (_root_.Filter.Eventually.of_forall fun a => ?_)
        exact hpoint a
      _ = (∫ a, toFullBlockVec
              (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) X)
              (Sum.inl i) ∂P) + X.2 i := by
        rw [integral_add (integrable_coarseBlock_mulVec_apply hint X (Sum.inl i))
          (integrable_const _)]
        simp
      _ = toFullBlockVec
              (blockMatVecMul (annealedBlock P (U : Set (Vec d))) X)
              (Sum.inl i) + X.2 i := by
        rw [congrFun hintMul (Sum.inl i)]
      _ = (blockMatVecMul (blockR d)
            (blockMatVecMul (annealedBlock P (U : Set (Vec d))) X) + X).2 i := by
        rw [blockMatVecMul_blockR]
        rfl

end

end HCPolySupport.HighContrast.Response
