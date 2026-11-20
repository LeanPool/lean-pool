/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.Realification
public import LeanPool.FastDynamo.Operator.Compatibility

/-!
# Compatibility of the induction operator with realification

The velocity in the paper is real-valued.  This module proves that the
complex auxiliary induction action consequently commutes with physical-space
complex conjugation and with the associated real-part projection.  It also
records that realification preserves the divergence-free constraint, so the
auxiliary-to-physical operator bridge applies to the
realified trajectory.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-! ## Conjugation and multiplication by real coefficients -/

/-- A product-torus `C3`-valued coefficient is real-valued almost everywhere. -/
def IsRealProductVectorLInf (a : ProductC3LInf) : Prop :=
  ∀ᵐ x ∂productMeasure, conjC3 (a x) = a x

/-- Conjugation commutes with scalar-vector multiplication when the scalar
coefficient is real-valued. -/
theorem productConjL2_scalarVectorMulProduct_of_real
    (a : ProductScalarLInf) (ha : IsRealProductScalarLInf a)
    (V : ProductC3L2) :
    productConjL2 (scalarVectorMulProduct a V) =
      scalarVectorMulProduct a (productConjL2 V) := by
  apply Lp.ext
  filter_upwards [
    productConjL2_coe_ae (scalarVectorMulProduct a V),
    scalarVectorMulProduct_coe_ae a V,
    scalarVectorMulProduct_coe_ae a (productConjL2 V),
    productConjL2_coe_ae V, ha] with x hout hin hr hconj hreal
  rw [hout, hin, hr, hconj]
  apply PiLp.ext
  intro i
  change starRingEnd ℂ (a x * V x i) =
    a x * starRingEnd ℂ (V x i)
  rw [map_mul, hreal]

/-- Conjugation commutes with vector-scalar multiplication when the vector
coefficient is real-valued. -/
theorem productConjL2_vectorScalarMulProduct_of_real
    (a : ProductC3LInf) (ha : IsRealProductVectorLInf a)
    (f : ProductScalarL2) :
    productConjL2 (vectorScalarMulProduct a f) =
      vectorScalarMulProduct a (productScalarConjL2 f) := by
  apply Lp.ext
  filter_upwards [
    productConjL2_coe_ae (vectorScalarMulProduct a f),
    vectorScalarMulProduct_coe_ae a f,
    vectorScalarMulProduct_coe_ae a (productScalarConjL2 f),
    productScalarConjL2_coe_ae f, ha] with x hout hin hr hconj hreal
  rw [hout, hin, hr, hconj]
  apply PiLp.ext
  intro i
  have hreal_i := congrArg (fun z : C3 ↦ z i) hreal
  change starRingEnd ℂ (f x * a x i) =
    starRingEnd ℂ (f x) * a x i
  change starRingEnd ℂ (a x i) = a x i at hreal_i
  rw [map_mul, hreal_i]

/-- The pulled-back complexification of a real velocity derivative is fixed
by coordinatewise conjugation. -/
theorem pull_velocityDeriv_isReal
    (u : TransverseRealW1Inf) (j : Fin 2) :
    IsRealProductVectorLInf
      (pullTransverseVectorLInf
        (transverseW1InfComplexDerivLInf j u)) := by
  have hpull := pullTransverseVectorLInf_coe_ae
    (transverseW1InfComplexDerivLInf j u)
  have hderiv := transverseW1InfComplexDerivLInf_coe_ae j u
  have hderivProduct :=
    (measurePreserving_fst (μ := transverseMeasure) (ν := axialMeasure))
      |>.quasiMeasurePreserving |>.ae_eq_comp hderiv
  filter_upwards [hpull, hderivProduct] with x hp hd
  rw [hp]
  change
    ((transverseW1InfComplexDerivLInf j u : TransverseC3LInf) :
        TransverseTorus → C3) x.1 =
      complexifyR3 ((transverseW1InfDeriv j u) x.1) at hd
  rw [hd]
  apply PiLp.ext
  intro i
  simp [conjC3_apply]

/-! ## Conjugation and weak derivatives -/

/--
The product frequency energy is invariant under simultaneous negation of the transverse and axial
frequencies; this is the symmetry that lets complex conjugation act on the `H²` graph.
-/
private theorem productFrequencyEnergy_neg
    (n : TransverseFrequency) (k : ℤ) :
    productFrequencyEnergy (-n) (-k) = productFrequencyEnergy n k := by
  simp [productFrequencyEnergy]

/-- Product conjugation commutes with each transverse weak derivative. -/
theorem productConjL2_productTransverseDerivFromH2
    (j : Fin 2) (B : ProductC3H2) :
    productConjL2 (productTransverseDerivFromH2 j B) =
      productTransverseDerivFromH2 j (productConjH2 B) := by
  apply productC3L2_ext_coeff
  intro n k i
  rw [productCoeffCLM_productConjL2,
    productCoeffCLM_productTransverseDerivFromH2,
    productCoeffCLM_productTransverseDerivFromH2,
    productH2Embedding_productConjH2,
    productCoeffCLM_productConjL2]
  simp only [Pi.neg_apply, Int.cast_neg, map_mul, map_neg,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_intCast]
  ring

/-- Product conjugation commutes with the axial weak derivative. -/
theorem productConjL2_productAxialDerivFromH2 (B : ProductC3H2) :
    productConjL2 (productAxialDerivFromH2 B) =
      productAxialDerivFromH2 (productConjH2 B) := by
  apply productC3L2_ext_coeff
  intro n k i
  rw [productCoeffCLM_productConjL2,
    productCoeffCLM_productAxialDerivFromH2,
    productCoeffCLM_productAxialDerivFromH2,
    productH2Embedding_productConjH2,
    productCoeffCLM_productConjL2]
  simp only [Int.cast_neg, map_mul, map_neg, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat, map_intCast]
  ring

/-- Product conjugation commutes with the weak Laplacian. -/
theorem productConjL2_productLaplacianFromH2 (B : ProductC3H2) :
    productConjL2 (productLaplacianFromH2 B) =
      productLaplacianFromH2 (productConjH2 B) := by
  apply productC3L2_ext_coeff
  intro n k i
  rw [productCoeffCLM_productConjL2,
    productCoeffCLM_productLaplacianFromH2,
    productCoeffCLM_productLaplacianFromH2,
    productH2Embedding_productConjH2,
    productCoeffCLM_productConjL2,
    productFrequencyEnergy_neg]
  simp

/-! ## Conjugation of the induction action -/

/-- Conjugation, regarded as a real-linear map, commutes with multiplication
by a real scalar. -/
theorem productConjL2_ofReal_smul (r : ℝ) (V : ProductC3L2) :
    productConjL2 ((r : ℂ) • V) =
      (r : ℂ) • productConjL2 V := by
  calc
    productConjL2 ((r : ℂ) • V) =
        starRingEnd ℂ (r : ℂ) • productConjL2 V :=
      productConjL2_smul (r : ℂ) V
    _ = (r : ℂ) • productConjL2 V := by
      rw [Complex.conj_ofReal]

/-- The diffusion term commutes with conjugation. -/
theorem productConjL2_productInductionDiffusion (B : ProductC3H2) :
    productConjL2 (productInductionDiffusion B) =
      productInductionDiffusion (productConjH2 B) :=
  productConjL2_productLaplacianFromH2 B

/-- Transverse transport by the real velocity commutes with conjugation. -/
theorem productConjL2_productInductionTransverseTransport
    (u : TransverseRealW1Inf) (B : ProductC3H2) :
    productConjL2 (productInductionTransverseTransport u B) =
      productInductionTransverseTransport u (productConjH2 B) := by
  rw [productInductionTransverseTransport_apply,
    productInductionTransverseTransport_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [productConjL2_scalarVectorMulProduct_of_real _
      (pull_velocityCoord_isReal u j.castSucc),
    productConjL2_productTransverseDerivFromH2]

/-- Axial transport by the real velocity commutes with conjugation. -/
theorem productConjL2_productInductionAxialTransport
    (u : TransverseRealW1Inf) (B : ProductC3H2) :
    productConjL2 (productInductionAxialTransport u B) =
      productInductionAxialTransport u (productConjH2 B) := by
  rw [productInductionAxialTransport_apply,
    productInductionAxialTransport_apply,
    productConjL2_scalarVectorMulProduct_of_real _
      (pull_velocityCoord_isReal u 2),
    productConjL2_productAxialDerivFromH2]

/-- Stretching by the weak derivatives of the real velocity commutes with
conjugation. -/
theorem productConjL2_productInductionStretching
    (u : TransverseRealW1Inf) (B : ProductC3H2) :
    productConjL2 (productInductionStretching u B) =
      productInductionStretching u (productConjH2 B) := by
  rw [productInductionStretching_apply,
    productInductionStretching_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [productConjL2_vectorScalarMulProduct_of_real _
      (pull_velocityDeriv_isReal u j),
    productH2Embedding_productConjH2,
    productCoordL2_productConjL2]

/-- The real-coefficient auxiliary induction action commutes with
physical-space complex conjugation. -/
theorem productInductionAction_productConjH2
    (u : TransverseRealW1Inf) (epsilon : ℝ) (B : ProductC3H2) :
    productInductionAction u epsilon (productConjH2 B) =
      productConjL2 (productInductionAction u epsilon B) := by
  symm
  change productConjL2
      ((epsilon : ℂ) • productInductionDiffusion B -
        productInductionTransverseTransport u B -
        productInductionAxialTransport u B +
        productInductionStretching u B) =
    (epsilon : ℂ) • productInductionDiffusion (productConjH2 B) -
      productInductionTransverseTransport u (productConjH2 B) -
      productInductionAxialTransport u (productConjH2 B) +
      productInductionStretching u (productConjH2 B)
  calc
    productConjL2
        (((epsilon : ℂ) • productInductionDiffusion B -
          productInductionTransverseTransport u B -
          productInductionAxialTransport u B) +
          productInductionStretching u B) =
        productConjL2
            ((epsilon : ℂ) • productInductionDiffusion B -
              productInductionTransverseTransport u B -
              productInductionAxialTransport u B) +
          productConjL2 (productInductionStretching u B) :=
      productConjL2.map_add _ _
    _ =
        (productConjL2
            ((epsilon : ℂ) • productInductionDiffusion B -
              productInductionTransverseTransport u B) -
          productConjL2 (productInductionAxialTransport u B)) +
          productConjL2 (productInductionStretching u B) := by
      rw [productConjL2.map_sub]
    _ =
        ((productConjL2
              ((epsilon : ℂ) • productInductionDiffusion B) -
            productConjL2 (productInductionTransverseTransport u B)) -
          productConjL2 (productInductionAxialTransport u B)) +
          productConjL2 (productInductionStretching u B) := by
      rw [productConjL2.map_sub]
    _ =
        (((epsilon : ℂ) •
              productConjL2 (productInductionDiffusion B) -
            productConjL2 (productInductionTransverseTransport u B)) -
          productConjL2 (productInductionAxialTransport u B)) +
          productConjL2 (productInductionStretching u B) := by
      rw [productConjL2_ofReal_smul]
    _ =
        (epsilon : ℂ) • productInductionDiffusion (productConjH2 B) -
          productInductionTransverseTransport u (productConjH2 B) -
          productInductionAxialTransport u (productConjH2 B) +
          productInductionStretching u (productConjH2 B) := by
      have hdiff := productConjL2_productInductionDiffusion B
      have htrans :=
        productConjL2_productInductionTransverseTransport u B
      have haxial := productConjL2_productInductionAxialTransport u B
      have hstretch := productConjL2_productInductionStretching u B
      calc
        (epsilon : ℂ) •
              productConjL2 (productInductionDiffusion B) -
            productConjL2 (productInductionTransverseTransport u B) -
            productConjL2 (productInductionAxialTransport u B) +
            productConjL2 (productInductionStretching u B) =
            (epsilon : ℂ) •
                productInductionDiffusion (productConjH2 B) -
              productConjL2 (productInductionTransverseTransport u B) -
              productConjL2 (productInductionAxialTransport u B) +
              productConjL2 (productInductionStretching u B) :=
          congrArg (fun D : ProductC3L2 ↦
            (epsilon : ℂ) • D -
              productConjL2 (productInductionTransverseTransport u B) -
              productConjL2 (productInductionAxialTransport u B) +
              productConjL2 (productInductionStretching u B)) hdiff
        _ = (epsilon : ℂ) •
                productInductionDiffusion (productConjH2 B) -
              productInductionTransverseTransport u (productConjH2 B) -
              productConjL2 (productInductionAxialTransport u B) +
              productConjL2 (productInductionStretching u B) :=
          congrArg (fun T : ProductC3L2 ↦
            (epsilon : ℂ) •
                productInductionDiffusion (productConjH2 B) - T -
              productConjL2 (productInductionAxialTransport u B) +
              productConjL2 (productInductionStretching u B)) htrans
        _ = (epsilon : ℂ) •
                productInductionDiffusion (productConjH2 B) -
              productInductionTransverseTransport u (productConjH2 B) -
              productInductionAxialTransport u (productConjH2 B) +
              productConjL2 (productInductionStretching u B) :=
          congrArg (fun A : ProductC3L2 ↦
            (epsilon : ℂ) •
                productInductionDiffusion (productConjH2 B) -
              productInductionTransverseTransport u (productConjH2 B) - A +
              productConjL2 (productInductionStretching u B)) haxial
        _ = (epsilon : ℂ) •
                productInductionDiffusion (productConjH2 B) -
              productInductionTransverseTransport u (productConjH2 B) -
              productInductionAxialTransport u (productConjH2 B) +
              productInductionStretching u (productConjH2 B) :=
          congrArg (fun S : ProductC3L2 ↦
            (epsilon : ℂ) •
                productInductionDiffusion (productConjH2 B) -
              productInductionTransverseTransport u (productConjH2 B) -
              productInductionAxialTransport u (productConjH2 B) + S) hstretch

/-- Consequently, the auxiliary induction action commutes with the `H²`
real-part projection. -/
theorem productInductionAction_productRealPartH2
    (u : TransverseRealW1Inf) (epsilon : ℝ) (B : ProductC3H2) :
    productInductionAction u epsilon (productRealPartH2 B) =
      productRealPartL2 (productInductionAction u epsilon B) := by
  rw [productRealPartH2_apply, productRealPartL2_apply]
  change productInductionAction u epsilon
      (((1 / 2 : ℝ) : ℂ) • (B + productConjH2 B)) =
    (((1 / 2 : ℝ) : ℂ) •
      (productInductionAction u epsilon B +
        productConjL2 (productInductionAction u epsilon B)))
  rw [map_smul, map_add, productInductionAction_productConjH2]

/-! ## Eigenpairs and the physical action -/

/-- The auxiliary action on a realified divergence-free state agrees in
`H⁻²` with the physical curl-form action. -/
theorem productInductionAction_productRealPartH2_toHMinus2_eq_physical
    (u : TransverseRealW1Inf) (hdivu : IsTransverseDivergenceFree u)
    (epsilon : ℝ) (B : ProductC3H2)
    (hdivB : productDivergenceFromH2 B = 0) :
    productL2ToHMinus2
        (productInductionAction u epsilon (productRealPartH2 B)) =
      productPhysicalInductionAction u epsilon (productRealPartH2 B) :=
  productInductionAction_toHMinus2_eq_physical u hdivu epsilon
    (productRealPartH2 B)
    (productRealPartH2_preserves_divergenceFree hdivB)

/-- Physical evolution of a realified divergence-free state is the `H⁻²`
embedding of the real part of its auxiliary action. -/
theorem productPhysicalInductionAction_productRealPartH2_of_divergenceFree
    (u : TransverseRealW1Inf) (hdivu : IsTransverseDivergenceFree u)
    (epsilon : ℝ) (B : ProductC3H2)
    (hdivB : productDivergenceFromH2 B = 0) :
    productPhysicalInductionAction u epsilon (productRealPartH2 B) =
      productL2ToHMinus2
        (productRealPartL2 (productInductionAction u epsilon B)) := by
  rw [← productInductionAction_productRealPartH2]
  exact (productInductionAction_productRealPartH2_toHMinus2_eq_physical
    u hdivu epsilon B hdivB).symm

end

end FastDynamo
