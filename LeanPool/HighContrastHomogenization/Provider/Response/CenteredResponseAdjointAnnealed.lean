/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseAnnealed

/-!
# High-contrast homogenization: Provider.Response.CenteredResponseAdjointAnnealed

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Annealed adjoint response identities

Coefficient transposition conjugates every coarse block by the diagonal sign
matrix.  Integrating that pointwise congruence identifies the adjoint response
energy and both adjoint optimizer means with the same congruence of the
annealed primal block.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Applying an adjoint coarse block is the signed transport of applying the
original coarse block. -/
theorem adjoint_coarseBlock_mulVec_eq (U : Domain d) (a : CoeffSpace d)
    (X : BlockVec d) :
    blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X =
      blockMatVecMul (blockDiag 1 (-1))
        (blockMatVecMul (coarseBlock (U : Set (Vec d)) a)
          (blockMatVecMul (blockDiag 1 (-1)) X)) := by
  rw [coarseBlock_transpose a U, blockMatVecMul_adjointSign_congr]

/-- Each coordinate of an adjoint coarse block applied to a fixed vector is
integrable under integrability of the primal coarse block. -/
theorem integrable_adjoint_coarseBlock_mulVec_apply
    {P : Measure (CoeffSpace d)} (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    (X : BlockVec d) (α : BlockCoord d) :
    Integrable (fun a =>
      toFullBlockVec
        (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X) α) P := by
  let DX := blockMatVecMul (blockDiag (1 : Mat d) (-1)) X
  cases α with
  | inl i =>
      have hbase := integrable_coarseBlock_mulVec_apply hint DX (Sum.inl i)
      refine hbase.congr (Filter.Eventually.of_forall fun a => ?_)
      change toFullBlockVec
          (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) DX) (Sum.inl i) =
        toFullBlockVec
          (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X) (Sum.inl i)
      rw [adjoint_coarseBlock_mulVec_eq, adjointSign_mulVec]
      rfl
  | inr i =>
      have hbase :=
        (integrable_coarseBlock_mulVec_apply hint DX (Sum.inr i)).neg
      refine hbase.congr (Filter.Eventually.of_forall fun a => ?_)
      change -toFullBlockVec
          (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) DX) (Sum.inr i) =
        toFullBlockVec
          (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X) (Sum.inr i)
      rw [adjoint_coarseBlock_mulVec_eq, adjointSign_mulVec]
      rfl

/-- Integration commutes with applying the adjoint coarse block; the result is
the sign congruence of the annealed primal block. -/
theorem integral_adjoint_coarseBlock_mulVec
    {P : Measure (CoeffSpace d)} (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    (X : BlockVec d) :
    (fun α => ∫ a,
      toFullBlockVec
        (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X) α ∂P) =
      toFullBlockVec
        (blockMatVecMul
          (blockMatMul (blockDiag 1 (-1))
            (blockMatMul (annealedBlock P (U : Set (Vec d)))
              (blockDiag 1 (-1)))) X) := by
  let DX := blockMatVecMul (blockDiag (1 : Mat d) (-1)) X
  have hintMul := integral_coarseBlock_mulVec hint DX
  funext α
  cases α with
  | inl i =>
      calc
        (∫ a, toFullBlockVec
            (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X)
              (Sum.inl i) ∂P) =
            ∫ a, toFullBlockVec
              (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) DX)
                (Sum.inl i) ∂P := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
          change toFullBlockVec
              (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X)
                (Sum.inl i) =
            toFullBlockVec
              (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) DX)
                (Sum.inl i)
          rw [adjoint_coarseBlock_mulVec_eq, adjointSign_mulVec]
          rfl
        _ = toFullBlockVec
              (blockMatVecMul (annealedBlock P (U : Set (Vec d))) DX)
                (Sum.inl i) := congrFun hintMul (Sum.inl i)
        _ = toFullBlockVec
              (blockMatVecMul
                (blockMatMul (blockDiag 1 (-1))
                  (blockMatMul (annealedBlock P (U : Set (Vec d)))
                    (blockDiag 1 (-1)))) X) (Sum.inl i) := by
          rw [blockMatVecMul_adjointSign_congr, adjointSign_mulVec]
          rfl
  | inr i =>
      calc
        (∫ a, toFullBlockVec
            (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X)
              (Sum.inr i) ∂P) =
            ∫ a, -toFullBlockVec
              (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) DX)
                (Sum.inr i) ∂P := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
          change toFullBlockVec
              (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X)
                (Sum.inr i) =
            -toFullBlockVec
              (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) DX)
                (Sum.inr i)
          rw [adjoint_coarseBlock_mulVec_eq, adjointSign_mulVec]
          rfl
        _ = -(∫ a, toFullBlockVec
              (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) DX)
                (Sum.inr i) ∂P) := by
          rw [integral_neg]
        _ = -toFullBlockVec
              (blockMatVecMul (annealedBlock P (U : Set (Vec d))) DX)
                (Sum.inr i) := by
          rw [congrFun hintMul (Sum.inr i)]
        _ = toFullBlockVec
              (blockMatVecMul
                (blockMatMul (blockDiag 1 (-1))
                  (blockMatMul (annealedBlock P (U : Set (Vec d)))
                    (blockDiag 1 (-1)))) X) (Sum.inr i) := by
          rw [blockMatVecMul_adjointSign_congr, adjointSign_mulVec]
          rfl

/-- The expected adjoint quadratic form is the quadratic form of the signed
congruence of the annealed block. -/
theorem integral_adjoint_coarseBlock_quadratic
    {P : Measure (CoeffSpace d)} (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    (X : BlockVec d) :
    (∫ a, blockVecDot X
      (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X) ∂P) =
      blockVecDot X
        (blockMatVecMul
          (blockMatMul (blockDiag 1 (-1))
            (blockMatMul (annealedBlock P (U : Set (Vec d)))
              (blockDiag 1 (-1)))) X) := by
  let DX := blockMatVecMul (blockDiag (1 : Mat d) (-1)) X
  calc
    (∫ a, blockVecDot X
        (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X) ∂P) =
        ∫ a, blockVecDot DX
          (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) DX) ∂P := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      change blockVecDot X
          (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X) =
        blockVecDot DX
          (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) DX)
      rw [coarseBlock_transpose a U, blockQuadratic_adjointSign_congr]
    _ = blockVecDot DX
          (blockMatVecMul (annealedBlock P (U : Set (Vec d))) DX) := by
      rw [blockVecDot_blockMatVecMul_annealedBlock hint]
    _ = blockVecDot X
          (blockMatVecMul
            (blockMatMul (blockDiag 1 (-1))
              (blockMatMul (annealedBlock P (U : Set (Vec d)))
                (blockDiag 1 (-1)))) X) := by
      rw [blockQuadratic_adjointSign_congr]

/-- The annealed adjoint response energy is the quadratic form of the signed
annealed block. -/
theorem annealed_adjoint_responseJ_eq {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d))) (p q : Vec d) :
    (∫ a, responseJ U (a.transpose.coeffOn U) p q ∂P) =
      (1 / 2 : ℝ) * blockVecDot ((-p, q) : BlockVec d)
        (blockMatVecMul
          (blockMatMul (blockDiag 1 (-1))
            (blockMatMul (annealedBlock P (U : Set (Vec d)))
              (blockDiag 1 (-1)))) ((-p, q) : BlockVec d)) - vecDot p q := by
  let X : BlockVec d := (-p, q)
  have hquad : Integrable (fun a => blockVecDot X
      (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X)) P := by
    let DX := blockMatVecMul (blockDiag (1 : Mat d) (-1)) X
    have hbase := integrable_coarseBlock_quadratic hint DX
    refine hbase.congr (Filter.Eventually.of_forall fun a => ?_)
    change blockVecDot DX
        (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) DX) =
      blockVecDot X
        (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X)
    rw [coarseBlock_transpose a U, blockQuadratic_adjointSign_congr]
  calc
    (∫ a, responseJ U (a.transpose.coeffOn U) p q ∂P) =
        ∫ a, (1 / 2 : ℝ) * blockVecDot X
          (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X) -
            vecDot p q ∂P := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      exact responseJ_eq_coarseBlock U a.transpose p q
    _ = (1 / 2 : ℝ) *
          (∫ a, blockVecDot X
            (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X) ∂P) -
          vecDot p q := by
      rw [integral_sub (hquad.const_mul _) (integrable_const _),
        integral_const_mul]
      simp
    _ = (1 / 2 : ℝ) * blockVecDot X
          (blockMatVecMul
            (blockMatMul (blockDiag 1 (-1))
              (blockMatMul (annealedBlock P (U : Set (Vec d)))
                (blockDiag 1 (-1)))) X) - vecDot p q := by
      rw [integral_adjoint_coarseBlock_quadratic U hint X]

/-- The separately annealed adjoint optimizer averages are read from the two
rows of the signed annealed block. -/
theorem annealed_adjoint_optimizer_average_eq
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d))) (p q : Vec d) :
    ((annealedAdjointOptimizerGradient P U p q,
        annealedAdjointOptimizerFlux P U p q) : BlockVec d) =
      blockMatVecMul (blockR d)
          (blockMatVecMul
            (blockMatMul (blockDiag 1 (-1))
              (blockMatMul (annealedBlock P (U : Set (Vec d)))
                (blockDiag 1 (-1)))) ((-p, q) : BlockVec d)) +
        ((-p, q) : BlockVec d) := by
  let X : BlockVec d := (-p, q)
  have hintMul := integral_adjoint_coarseBlock_mulVec U hint X
  apply Prod.ext
  · funext i
    have hpoint : ∀ a : CoeffSpace d,
        averageGradient U (a.transpose.coeffOn U)
            (centeredAdjointOptimizer U a p q) i =
          toFullBlockVec
              (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X)
              (Sum.inr i) + X.1 i := by
      intro a
      have h := blockAverage_eq (a.transpose.coeffOn U)
        (centeredAdjointOptimizer_isMaximizer U a p q)
      rw [← coarseBlock_eq_coarseBlockMatrix a.transpose U] at h
      have hi := congrArg (fun Y : BlockVec d => Y.1 i) h
      simpa only [blockMatVecMul_blockR, Prod.fst_add, Pi.add_apply,
        toFullBlockVec, X] using hi
    change (∫ a, averageGradient U (a.transpose.coeffOn U)
      (centeredAdjointOptimizer U a p q) i ∂P) = _
    calc
      (∫ a, averageGradient U (a.transpose.coeffOn U)
          (centeredAdjointOptimizer U a p q) i ∂P) =
          ∫ a, toFullBlockVec
              (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X)
              (Sum.inr i) + X.1 i ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        exact hpoint a
      _ = (∫ a, toFullBlockVec
              (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X)
              (Sum.inr i) ∂P) + X.1 i := by
        rw [integral_add
          (integrable_adjoint_coarseBlock_mulVec_apply U hint X (Sum.inr i))
          (integrable_const _)]
        simp
      _ = toFullBlockVec
              (blockMatVecMul
                (blockMatMul (blockDiag 1 (-1))
                  (blockMatMul (annealedBlock P (U : Set (Vec d)))
                    (blockDiag 1 (-1)))) X) (Sum.inr i) + X.1 i := by
        rw [congrFun hintMul (Sum.inr i)]
      _ = (blockMatVecMul (blockR d)
            (blockMatVecMul
              (blockMatMul (blockDiag 1 (-1))
                (blockMatMul (annealedBlock P (U : Set (Vec d)))
                  (blockDiag 1 (-1)))) X) + X).1 i := by
        rw [blockMatVecMul_blockR]
        rfl
  · funext i
    have hpoint : ∀ a : CoeffSpace d,
        averageFlux U (a.transpose.coeffOn U)
            (centeredAdjointOptimizer U a p q) i =
          toFullBlockVec
              (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X)
              (Sum.inl i) + X.2 i := by
      intro a
      have h := blockAverage_eq (a.transpose.coeffOn U)
        (centeredAdjointOptimizer_isMaximizer U a p q)
      rw [← coarseBlock_eq_coarseBlockMatrix a.transpose U] at h
      have hi := congrArg (fun Y : BlockVec d => Y.2 i) h
      simpa only [blockMatVecMul_blockR, Prod.snd_add, Pi.add_apply,
        toFullBlockVec, X] using hi
    change (∫ a, averageFlux U (a.transpose.coeffOn U)
      (centeredAdjointOptimizer U a p q) i ∂P) = _
    calc
      (∫ a, averageFlux U (a.transpose.coeffOn U)
          (centeredAdjointOptimizer U a p q) i ∂P) =
          ∫ a, toFullBlockVec
              (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X)
              (Sum.inl i) + X.2 i ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        exact hpoint a
      _ = (∫ a, toFullBlockVec
              (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X)
              (Sum.inl i) ∂P) + X.2 i := by
        rw [integral_add
          (integrable_adjoint_coarseBlock_mulVec_apply U hint X (Sum.inl i))
          (integrable_const _)]
        simp
      _ = toFullBlockVec
              (blockMatVecMul
                (blockMatMul (blockDiag 1 (-1))
                  (blockMatMul (annealedBlock P (U : Set (Vec d)))
                    (blockDiag 1 (-1)))) X) (Sum.inl i) + X.2 i := by
        rw [congrFun hintMul (Sum.inl i)]
      _ = (blockMatVecMul (blockR d)
            (blockMatVecMul
              (blockMatMul (blockDiag 1 (-1))
                (blockMatMul (annealedBlock P (U : Set (Vec d)))
                  (blockDiag 1 (-1)))) X) + X).2 i := by
        rw [blockMatVecMul_blockR]
        rfl

end

end HCPolySupport.HighContrast.Response
