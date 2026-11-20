/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.BoundedOperatorMultiplier
public import LeanPool.FastDynamo.Analysis.WholePlaneExteriorCutoff
public import LeanPool.FastDynamo.Operator.FixedSector

/-!
# Supported periodic coefficient multipliers

The transverse layer sees the velocity only through essentially bounded
operator-valued multipliers on the normalized transverse torus.  This file
records that multiplier core: the coefficient type
`TransverseC3OperatorLInf`, the fact that a coefficient supported in a
measurable set only sees the restricted input, the literal matrix field
`b ↦ (b⋅∇⊥)u` of the reduced stretching term with its identification with
`reducedInductionStretching`, and the Hermitian symmetric gradient with its
pointwise quadratic form and its support.

Everything here is `L∞`-coefficient algebra with support restriction; the
`L⁴ → L²` restriction estimates that consume it live in
`FastDynamo.Global.TorusLocalCoreMeasurability`, which imports this file.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

/-! ## Supported periodic operator coefficients -/

/-- Essentially bounded operator-valued coefficients on the transverse torus. -/
abbrev TransverseC3OperatorLInf :=
  Lp (C3 →L[ℂ] C3) ∞ transverseMeasure

/-! ## The exact stretching and symmetric-gradient coefficients -/

/-- The `j`th column of the transverse velocity gradient, interpreted as the
rank-one operator `b ↦ b_j ∂_j u`. -/
def transverseStretchingCoefficientTerm
    (u : TransverseRealW1Inf) (j : Fin 2) :
    TransverseC3OperatorLInf :=
  ((ContinuousLinearMap.smulRightL ℂ C3 C3
      (EuclideanSpace.proj j.castSucc)).compLpL ∞ transverseMeasure)
    (transverseW1InfComplexDerivLInf j u)

/-- The literal matrix field `b ↦ (b⋅∇⊥)u` occurring in the reduced
stretching term.  Its third column is zero because the velocity is independent
of the axial variable. -/
def transverseStretchingCoefficient
    (u : TransverseRealW1Inf) : TransverseC3OperatorLInf :=
  ∑ j : Fin 2, transverseStretchingCoefficientTerm u j

/-- Pointwise representative of the `j`th gradient column. -/
theorem transverseStretchingCoefficientTerm_coe_ae
    (u : TransverseRealW1Inf) (j : Fin 2) :
    (transverseStretchingCoefficientTerm u j :
        TransverseTorus → (C3 →L[ℂ] C3)) =ᵐ[transverseMeasure]
      fun x ↦ (EuclideanSpace.proj j.castSucc).smulRight
        ((transverseW1InfComplexDerivLInf j u) x) := by
  exact (ContinuousLinearMap.smulRightL ℂ C3 C3
    (EuclideanSpace.proj j.castSucc)).coeFn_compLpL
      (transverseW1InfComplexDerivLInf j u)

/-- Pointwise matrix formula for the full transverse gradient. -/
theorem transverseStretchingCoefficient_coe_ae
    (u : TransverseRealW1Inf) :
    (transverseStretchingCoefficient u :
        TransverseTorus → (C3 →L[ℂ] C3)) =ᵐ[transverseMeasure]
      fun x ↦ ∑ j : Fin 2,
        (EuclideanSpace.proj j.castSucc).smulRight
          ((transverseW1InfComplexDerivLInf j u) x) := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun j : Fin 2 ↦ transverseStretchingCoefficientTerm u j),
    ae_all_iff.2 (fun j ↦ transverseStretchingCoefficientTerm_coe_ae u j)]
      with x hsum hterm
  rw [transverseStretchingCoefficient, hsum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  exact hterm j

/-- The operator multiplier of the displayed gradient matrix is exactly the
repository's reduced stretching term. -/
theorem operatorMul_transverseStretchingCoefficient_eq
    (u : TransverseRealW1Inf) (b : TransverseC3H2) :
    operatorMulL2 transverseMeasure (transverseStretchingCoefficient u)
        (transverseH2Embedding b) =
      reducedInductionStretching u b := by
  rw [reducedInductionStretching_apply]
  apply Lp.ext
  have hright := Lp.coeFn_finsetSum Finset.univ
    (fun j : Fin 2 ↦ vectorScalarMulTransverse
      (transverseW1InfComplexDerivLInf j u)
        (transverseCoordL2 j.castSucc (transverseH2Embedding b)))
  have hmul := operatorMulL2_coe_ae transverseMeasure
    (transverseStretchingCoefficient u) (transverseH2Embedding b)
  have hcoef := transverseStretchingCoefficient_coe_ae u
  have hterms : ∀ j : Fin 2, ∀ᵐ x ∂transverseMeasure,
      (vectorScalarMulTransverse
          (transverseW1InfComplexDerivLInf j u)
            (transverseCoordL2 j.castSucc (transverseH2Embedding b)) :
        TransverseTorus → C3) x =
      ((transverseH2Embedding b : TransverseTorus → C3) x j.castSucc) •
        (transverseW1InfComplexDerivLInf j u : TransverseTorus → C3) x := by
    intro j
    filter_upwards [vectorScalarMulTransverse_coe_ae
        (transverseW1InfComplexDerivLInf j u)
          (transverseCoordL2 j.castSucc (transverseH2Embedding b)),
      (EuclideanSpace.proj (𝕜 := ℂ) j.castSucc).coeFn_compLpL
        (transverseH2Embedding b)] with x hx hcoord
    have hcoord' :
        ((transverseCoordL2 j.castSucc (transverseH2Embedding b) :
            TransverseScalarL2) : TransverseTorus → ℂ) x =
          (transverseH2Embedding b : TransverseTorus → C3) x j.castSucc := by
      change
        ((((EuclideanSpace.proj (𝕜 := ℂ) j.castSucc).compLpL 2
          transverseMeasure) (transverseH2Embedding b) :
            TransverseScalarL2) : TransverseTorus → ℂ) x = _
      exact hcoord
    rw [hx, hcoord']
  filter_upwards [hmul, hcoef, hright, ae_all_iff.2 hterms]
      with x hmulx hcoefx hrightx htermsx
  rw [hmulx, hcoefx, hrightx]
  simp only [Finset.sum_apply, sum_apply,
    ContinuousLinearMap.smulRight_apply]
  apply Finset.sum_congr rfl
  intro j hj
  exact (htermsx j).symm

end

end FastDynamo
