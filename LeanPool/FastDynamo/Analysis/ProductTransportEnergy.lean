/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WeakLeibnizAxial
public import LeanPool.FastDynamo.Analysis.WeakLeibnizVelocity
public import LeanPool.FastDynamo.Analysis.ProductDivergenceEnergy

/-!
# Skew energy of divergence-free transport on the product torus

This module proves the transport-energy cancellation used in the auxiliary solenoidality argument
of `FastDynamo.Finish.RealSolution`, a result of the formalisation with no counterpart in the
paper, which recovers the axial component directly in `lem:axial-recovery` (Lemma 8.1).
The velocity is the real, `x₃`-independent `W^{1,∞}` field
of the construction and the transported scalar belongs to the product Fourier `H¹` space.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-- Fourier integration by parts in one transverse direction: pairing an `H¹` test element `d`
with the `j`-th derivative coefficients of the `i`-th coordinate of `V` equals minus the physical
`L²` pairing of `∂ⱼd` with that coordinate. -/
private theorem productWeakTransverseComponent_pair
    (j : Fin 2) (i : Fin 3) (V : ProductC3L2)
    (d : ProductScalarH1) :
    inner ℂ d
        (productScalarH1TransverseDerivCoeffMap j
          (productCoordFourierAnalysis i V)) =
      -inner ℂ (productScalarTransverseDerivFromH1 j d)
        (productCoordL2 i V) := by
  rw [← productScalarFourierAnalysisNested.inner_map_map]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  rw [← tsum_neg]
  apply tsum_congr
  intro k
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  rw [← tsum_neg]
  apply tsum_congr
  intro n
  rw [productScalarH1TransverseDerivCoeffMap_apply,
    productCoordFourierAnalysis_apply,
    productScalarFourierAnalysisNested_transverseDerivFromH1,
    productScalarFourierAnalysisNested_productScalarH1Embedding,
    productScalarFourierAnalysisNested_coord_eq_productCoeffCLM]
  simp only [RCLike.inner_apply]
  rw [productH1TransverseDerivFourierMultiplier,
    productH1ValueFourierMultiplier]
  have hw : (productH1Weight n k : ℂ) ≠ 0 := by
    exact_mod_cast (productH1Weight_pos n k).ne'
  simp [map_mul]
  field_simp [hw]
  rw [map_ofNat]
  ring

/-- Fourier integration by parts in the axial direction: pairing an `H¹` test element `d` with
the axial derivative coefficients of the `i`-th coordinate of `V` equals minus the physical `L²`
pairing of `∂₃d` with that coordinate. -/
private theorem productWeakAxialComponent_pair
    (i : Fin 3) (V : ProductC3L2) (d : ProductScalarH1) :
    inner ℂ d
        (productScalarH1AxialDerivCoeffMap
          (productCoordFourierAnalysis i V)) =
      -inner ℂ (productScalarAxialDerivFromH1 d)
        (productCoordL2 i V) := by
  rw [← productScalarFourierAnalysisNested.inner_map_map]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  rw [← tsum_neg]
  apply tsum_congr
  intro k
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  rw [← tsum_neg]
  apply tsum_congr
  intro n
  rw [productScalarH1AxialDerivCoeffMap_apply,
    productCoordFourierAnalysis_apply,
    productScalarFourierAnalysisNested_axialDerivFromH1,
    productScalarFourierAnalysisNested_productScalarH1Embedding,
    productScalarFourierAnalysisNested_coord_eq_productCoeffCLM]
  simp only [RCLike.inner_apply]
  rw [productH1AxialDerivFourierMultiplier,
    productH1ValueFourierMultiplier]
  have hw : (productH1Weight n k : ℂ) ≠ 0 := by
    exact_mod_cast (productH1Weight_pos n k).ne'
  simp [map_mul]
  field_simp [hw]
  rw [map_ofNat]
  ring

/-! ## Fourier integration by parts -/

/-- Distributional divergence paired with an `H¹` test field is minus the
sum of the physical `L²` pairings with the three weak derivatives. -/
theorem productWeakDivergence_pair_eq_neg_derivatives
    (V : ProductC3L2) (d : ProductScalarH1) :
    productWeakDivergence V d =
      -((∑ j : Fin 2,
          inner ℂ (productScalarTransverseDerivFromH1 j d)
            (productCoordL2 j.castSucc V)) +
        inner ℂ (productScalarAxialDerivFromH1 d)
          (productCoordL2 (2 : Fin 3) V)) := by
  rw [productWeakDivergence_pair]
  change inner ℂ d
      ((∑ j : Fin 2,
        productScalarH1TransverseDerivCoeffMap j
          (productCoordFourierAnalysis j.castSucc V)) +
        productScalarH1AxialDerivCoeffMap
          (productCoordFourierAnalysis (2 : Fin 3) V)) = _
  rw [inner_add_right, inner_sum]
  simp_rw [productWeakTransverseComponent_pair]
  rw [productWeakAxialComponent_pair]
  simp only [Finset.sum_neg_distrib]
  ring

/-! ## Real multiplication -/

/-- An essentially bounded product-torus scalar coefficient is real-valued
when complex conjugation fixes one (hence every) representative almost
everywhere. -/
def IsRealProductScalarCoefficient (a : ProductScalarLInf) : Prop :=
  ∀ᵐ x ∂productMeasure, starRingEnd ℂ (a x) = a x

/-- Multiplication by a real `L∞` coefficient is self-adjoint on scalar
`L²`, in Mathlib's conjugate-linear-first inner-product convention. -/
theorem inner_scalarMulProduct_real_selfAdjoint
    {a : ProductScalarLInf} (ha : IsRealProductScalarCoefficient a)
    (f g : ProductScalarL2) :
    inner ℂ f (scalarMulProduct a g) =
      inner ℂ (scalarMulProduct a f) g := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarMulProduct_coe_ae a g,
    scalarMulProduct_coe_ae a f, ha] with x hg hf hreal
  rw [hg, hf]
  simp only [RCLike.inner_apply, map_mul, hreal]
  ring

/-! ## The real transverse velocity -/

/-- Every pulled-back scalar coordinate of the real velocity is real-valued. -/
theorem productVelocityCoord_isReal
    (u : TransverseRealW1Inf) (i : Fin 3) :
    IsRealProductScalarCoefficient
      (pullTransverseScalarLInf
        (transverseW1InfComplexValueCoordLInf i u)) := by
  have hpull := pullTransverseScalarLInf_coe_ae
    (transverseW1InfComplexValueCoordLInf i u)
  have hcoord := (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
    (transverseW1InfComplexValueLInf u)
  have hvalue := transverseW1InfComplexValueLInf_coe_ae u
  have hcoordprod :=
    (measurePreserving_fst (μ := transverseMeasure) (ν := axialMeasure))
      |>.quasiMeasurePreserving |>.ae_eq_comp hcoord
  have hvalueprod :=
    (measurePreserving_fst (μ := transverseMeasure) (ν := axialMeasure))
      |>.quasiMeasurePreserving |>.ae_eq_comp hvalue
  filter_upwards [hpull, hcoordprod, hvalueprod] with x hp hc hv
  change
    ((transverseW1InfComplexValueCoordLInf i u : TransverseScalarLInf) x.1) =
      (transverseW1InfComplexValueLInf u x.1) i at hc
  change (transverseW1InfComplexValueLInf u x.1) =
      complexifyR3 ((transverseW1InfValue u) x.1) at hv
  rw [hp, hc, hv]
  change starRingEnd ℂ
      (((transverseW1InfValue u) x.1 i : ℝ) : ℂ) =
    (((transverseW1InfValue u) x.1 i : ℝ) : ℂ)
  simp

/-- Each real velocity coordinate acts by a self-adjoint multiplication
operator on product scalar `L²`. -/
theorem inner_productVelocityCoordMul_selfAdjoint
    (u : TransverseRealW1Inf) (i : Fin 3)
    (f g : ProductScalarL2) :
    inner ℂ f
        (scalarMulProduct
          (pullTransverseScalarLInf
            (transverseW1InfComplexValueCoordLInf i u)) g) =
      inner ℂ
        (scalarMulProduct
          (pullTransverseScalarLInf
            (transverseW1InfComplexValueCoordLInf i u)) f) g :=
  inner_scalarMulProduct_real_selfAdjoint
    (productVelocityCoord_isReal u i) f g

/-! ## Transport cancellation -/

/-- Weak Leibniz rule plus self-adjointness of multiplication by the real coefficient `uᵢ`:
twice the real part of `⟪∂ⱼd, uᵢ d⟫` equals minus the real part of `⟪d, (∂ⱼuᵢ) d⟫`. -/
private theorem two_mul_re_inner_transverse_velocity
    (u : TransverseRealW1Inf) (j : Fin 2) (i : Fin 3)
    (d : ProductScalarH1) :
    2 * (inner ℂ (productScalarTransverseDerivFromH1 j d)
        (scalarMulProduct
          (pullTransverseScalarLInf
            (transverseW1InfComplexValueCoordLInf i u))
          (productScalarH1Embedding d))).re =
      -(inner ℂ (productScalarH1Embedding d)
        (scalarMulProduct
          (pullTransverseScalarLInf
            (transverseW1InfComplexDerivCoordLInf j i u))
          (productScalarH1Embedding d))).re := by
  have hibp :=
    (productScalarH1_hasFlatTransverseDerivative j d).integrationByParts
      (productScalarH1_velocityCoord_weakLeibniz u j i d)
  have hre := congrArg Complex.re hibp
  rw [inner_add_right, Complex.add_re, Complex.neg_re] at hre
  rw [inner_productVelocityCoordMul_selfAdjoint] at hre
  have hsym :
      (inner ℂ
        (scalarMulProduct
          (pullTransverseScalarLInf
            (transverseW1InfComplexValueCoordLInf i u))
          (productScalarH1Embedding d))
        (productScalarTransverseDerivFromH1 j d)).re =
      (inner ℂ (productScalarTransverseDerivFromH1 j d)
        (scalarMulProduct
          (pullTransverseScalarLInf
            (transverseW1InfComplexValueCoordLInf i u))
          (productScalarH1Embedding d))).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  linarith [hsym]

/-- The axial transport pairing `⟪∂₃d, u₃ d⟫` has vanishing real part, because `u₃` is real and
independent of `x₃`, so it carries no axial derivative term. -/
theorem re_inner_axial_velocity_eq_zero
    (u : TransverseRealW1Inf) (d : ProductScalarH1) :
    (inner ℂ (productScalarAxialDerivFromH1 d)
      (scalarMulProduct
        (pullTransverseScalarLInf
          (transverseW1InfComplexValueCoordLInf (2 : Fin 3) u))
        (productScalarH1Embedding d))).re = 0 := by
  have hibp :=
    (productScalarH1_hasFlatAxialDerivative d).integrationByParts
      (productScalarH1_velocityAxial_weakLeibniz u d)
  have hre := congrArg Complex.re hibp
  rw [Complex.neg_re] at hre
  rw [inner_productVelocityCoordMul_selfAdjoint] at hre
  have hsym :
      (inner ℂ
        (scalarMulProduct
          (pullTransverseScalarLInf
            (transverseW1InfComplexValueCoordLInf (2 : Fin 3) u))
          (productScalarH1Embedding d))
        (productScalarAxialDerivFromH1 d)).re =
      (inner ℂ (productScalarAxialDerivFromH1 d)
        (scalarMulProduct
          (pullTransverseScalarLInf
            (transverseW1InfComplexValueCoordLInf (2 : Fin 3) u))
          (productScalarH1Embedding d))).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  linarith [hsym]

/-- For a divergence-free transverse velocity the two diagonal derivative coefficients `∂₀u₀` and
`∂₁u₁` cancel, so multiplying any field by their sum gives zero. -/
private theorem transverse_divergence_multiplier_eq_zero
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (d : ProductScalarH1) :
    scalarMulProduct
        (pullTransverseScalarLInf
          (transverseW1InfComplexDerivCoordLInf
            (0 : Fin 2) (0 : Fin 3) u))
        (productScalarH1Embedding d) +
      scalarMulProduct
        (pullTransverseScalarLInf
          (transverseW1InfComplexDerivCoordLInf
            (1 : Fin 2) (1 : Fin 3) u))
        (productScalarH1Embedding d) = 0 := by
  let a := transverseW1InfComplexDerivCoordLInf
    (0 : Fin 2) (0 : Fin 3) u
  let b := transverseW1InfComplexDerivCoordLInf
    (1 : Fin 2) (1 : Fin 3) u
  let pa := pullTransverseScalarLInf a
  let pb := pullTransverseScalarLInf b
  let f := productScalarH1Embedding d
  have houter := congrArg
    (fun T : ProductScalarL2 →L[ℂ] ProductScalarL2 ↦ T f)
    (map_add scalarMulProduct pa pb)
  simp only [add_apply] at houter
  have hpull : pa + pb = pullTransverseScalarLInf (a + b) :=
    (map_add pullTransverseScalarLInf a b).symm
  calc
    scalarMulProduct pa f + scalarMulProduct pb f =
        scalarMulProduct (pa + pb) f := houter.symm
    _ = scalarMulProduct (pullTransverseScalarLInf (a + b)) f := by rw [hpull]
    _ = 0 := by
      have hab : a + b = 0 := hu
      rw [hab, map_zero, map_zero]
      rfl

/-- The two transverse transport pairings have zero total real part when
the real velocity is weakly divergence-free. -/
theorem re_sum_transverse_velocity_transport_eq_zero
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (d : ProductScalarH1) :
    ((∑ j : Fin 2,
      inner ℂ (productScalarTransverseDerivFromH1 j d)
        (scalarMulProduct
          (pullTransverseScalarLInf
            (transverseW1InfComplexValueCoordLInf j.castSucc u))
          (productScalarH1Embedding d)))).re = 0 := by
  have hzero := transverse_divergence_multiplier_eq_zero u hu d
  have hdivPair := congrArg
    (fun f : ProductScalarL2 ↦
      (inner ℂ (productScalarH1Embedding d) f).re) hzero
  simp only [inner_add_right, Complex.add_re, inner_zero_right,
    Complex.zero_re] at hdivPair
  have h0 := two_mul_re_inner_transverse_velocity u
    (0 : Fin 2) (0 : Fin 3) d
  have h1 := two_mul_re_inner_transverse_velocity u
    (1 : Fin 2) (1 : Fin 3) d
  simp only [Fin.sum_univ_two, Complex.add_re]
  change
    (inner ℂ (productScalarTransverseDerivFromH1 (0 : Fin 2) d)
        (scalarMulProduct
          (pullTransverseScalarLInf
            (transverseW1InfComplexValueCoordLInf (0 : Fin 3) u))
          (productScalarH1Embedding d))).re +
      (inner ℂ (productScalarTransverseDerivFromH1 (1 : Fin 2) d)
        (scalarMulProduct
          (pullTransverseScalarLInf
            (transverseW1InfComplexValueCoordLInf (1 : Fin 3) u))
          (productScalarH1Embedding d))).re = 0
  linarith

/-- **Transport skewness.**  For the real, `x₃`-independent weakly
divergence-free velocity, distributional divergence of `u d` has zero real
quadratic pairing with every product Fourier `H¹` scalar `d`.

The sign convention is the one forced by Mathlib's conjugate-linear first
inner-product slot:
`<div V,d> = - Σⱼ <∂ⱼ d,Vⱼ>`. -/
theorem productWeakDivergence_velocityTimesScalar_pair_re_eq_zero
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (d : ProductScalarH1) :
    (productWeakDivergence
      (productVelocityTimesScalar u (productScalarH1Embedding d)) d).re = 0 := by
  rw [productWeakDivergence_pair_eq_neg_derivatives]
  simp_rw [productCoordL2_productVelocityTimesScalar]
  rw [Complex.neg_re, Complex.add_re,
    re_sum_transverse_velocity_transport_eq_zero u hu d,
    re_inner_axial_velocity_eq_zero u d]
  simp

end

end FastDynamo
