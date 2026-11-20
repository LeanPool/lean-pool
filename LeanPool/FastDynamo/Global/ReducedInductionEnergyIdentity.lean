/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.InductionDivergence
public import LeanPool.FastDynamo.Analysis.ProductTransportEnergy
public import LeanPool.FastDynamo.Global.DomainOperatorNumericalRange
public import LeanPool.FastDynamo.Global.TorusLocalCoreMeasurability
public import LeanPool.FastDynamo.Operator.FixedSectorDiffusionInverse

/-!
# Numerical-range energy of the reduced induction operator

This module carries out the quadratic-form calculation for the literal
periodic reduced operator.  Diffusion is evaluated coefficient-by-
coefficient, while transport skewness is obtained by lifting one transverse
Fourier sector to the product torus and applying the weak
Leibniz integration-by-parts theorem there.  The result is the real-part identity
`re_inner_reducedInductionAction_eq`: both transport terms drop out, diffusion contributes
minus the gradient energy, and stretching is bounded by the `L∞` norm of the stretching
coefficient (`re_inner_reducedInductionStretching_le`).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! ## Coordinate decompositions -/

/-- The `L²` inner product of two `ℂ³`-valued fields on the product torus splits as the sum over
the three components of the scalar `L²` inner products of those components. -/
theorem inner_productC3L2_eq_sum_coord
    (f g : ProductC3L2) :
    inner ℂ f g =
      ∑ i : Fin 3, inner ℂ (productCoordL2 i f)
        (productCoordL2 i g) := by
  rw [MeasureTheory.L2.inner_def]
  simp_rw [MeasureTheory.L2.inner_def]
  rw [← integral_finsetSum]
  swap
  · intro i hi
    exact L2.integrable_inner (𝕜 := ℂ)
      (productCoordL2 i f) (productCoordL2 i g)
  apply integral_congr_ae
  have hf : ∀ i : Fin 3,
      ((productCoordL2 i f : ProductScalarL2) : ProductTorus3 → ℂ)
        =ᵐ[productMeasure] fun x ↦ f x i := by
    intro i
    exact (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL f
  have hg : ∀ i : Fin 3,
      ((productCoordL2 i g : ProductScalarL2) : ProductTorus3 → ℂ)
        =ᵐ[productMeasure] fun x ↦ g x i := by
    intro i
    exact (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL g
  filter_upwards [ae_all_iff.2 hf, ae_all_iff.2 hg] with x hfx hgx
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hfx i, hgx i]
  rfl

/-! ## Exact diffusion energy -/

/-- The transverse gradient energy of a reduced strong-domain state. -/
def reducedTransverseGradientEnergy (b : TransverseC3H2) : ℝ :=
  ∑ j : Fin 2, ‖transverseDerivFromH2 j b‖ ^ 2

/-- The transverse gradient energy `Σ_j ‖∂_j b‖²` is nonnegative, being a sum of squares. -/
theorem reducedTransverseGradientEnergy_nonneg
    (b : TransverseC3H2) :
    0 ≤ reducedTransverseGradientEnergy b := by
  exact Finset.sum_nonneg fun j hj ↦ sq_nonneg _

/-- Periodic integration by parts, one component at a time: pairing the `i`-th component of `b`
with the `i`-th component of `Δ_⊥ b` gives minus the sum over `j` of the squared `L²` pairings of
the `i`-th component of `∂_j b` with itself.  Proved on the Fourier side from the multiplier
identity for the transverse Laplacian. -/
private theorem inner_transverseCoord_laplacian_eq_neg_derivatives
    (b : TransverseC3H2) (i : Fin 3) :
    inner ℂ (transverseCoordL2 i (transverseH2Embedding b))
        (transverseCoordL2 i (transverseLaplacianFromH2 b)) =
      -∑ j : Fin 2,
        inner ℂ (transverseCoordL2 i (transverseDerivFromH2 j b))
          (transverseCoordL2 i (transverseDerivFromH2 j b)) := by
  rw [← transverseScalarFourierAnalysis.inner_map_map]
  simp_rw [← transverseScalarFourierAnalysis.inner_map_map]
  simp only [Fin.sum_univ_two]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, lp.inner_eq_tsum]
  rw [← (lp.summable_inner
      (transverseScalarFourierAnalysis
        (transverseCoordL2 i (transverseDerivFromH2 (0 : Fin 2) b)))
      (transverseScalarFourierAnalysis
        (transverseCoordL2 i (transverseDerivFromH2 (0 : Fin 2) b)))).tsum_add
    (lp.summable_inner
      (transverseScalarFourierAnalysis
        (transverseCoordL2 i (transverseDerivFromH2 (1 : Fin 2) b)))
      (transverseScalarFourierAnalysis
        (transverseCoordL2 i (transverseDerivFromH2 (1 : Fin 2) b))))]
  rw [← tsum_neg]
  apply tsum_congr
  intro n
  rw [show transverseScalarFourierAnalysis
        (transverseCoordL2 i (transverseH2Embedding b)) n =
          transverseCoeffCLM n i (transverseH2Embedding b) from rfl,
    show transverseScalarFourierAnalysis
        (transverseCoordL2 i (transverseLaplacianFromH2 b)) n =
          transverseCoeffCLM n i (transverseLaplacianFromH2 b) from rfl,
    show transverseScalarFourierAnalysis
        (transverseCoordL2 i (transverseDerivFromH2 (0 : Fin 2) b)) n =
          transverseCoeffCLM n i
            (transverseDerivFromH2 (0 : Fin 2) b) from rfl,
    show transverseScalarFourierAnalysis
        (transverseCoordL2 i (transverseDerivFromH2 (1 : Fin 2) b)) n =
          transverseCoeffCLM n i
            (transverseDerivFromH2 (1 : Fin 2) b) from rfl,
    transverseCoeffCLM_transverseLaplacianFromH2,
    transverseCoeffCLM_transverseDerivFromH2,
    transverseCoeffCLM_transverseDerivFromH2]
  unfold transverseFrequencyEnergy
  simp only [Fin.sum_univ_two, RCLike.inner_apply]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast,
    map_ofNat]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Exact periodic integration-by-parts identity for the transverse
Laplacian, proved from the complete Fourier basis. -/
theorem inner_transverseH2Embedding_laplacian_eq_neg_gradientEnergy
    (b : TransverseC3H2) :
    inner ℂ (transverseH2Embedding b) (transverseLaplacianFromH2 b) =
      -(reducedTransverseGradientEnergy b : ℂ) := by
  calc
    inner ℂ (transverseH2Embedding b) (transverseLaplacianFromH2 b) =
        ∑ i : Fin 3,
          inner ℂ (transverseCoordL2 i (transverseH2Embedding b))
            (transverseCoordL2 i (transverseLaplacianFromH2 b)) :=
      inner_transverseC3L2_eq_sum_coord _ _
    _ = ∑ i : Fin 3, -∑ j : Fin 2,
          inner ℂ (transverseCoordL2 i (transverseDerivFromH2 j b))
            (transverseCoordL2 i (transverseDerivFromH2 j b)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact inner_transverseCoord_laplacian_eq_neg_derivatives b i
    _ = -∑ j : Fin 2, ∑ i : Fin 3,
          inner ℂ (transverseCoordL2 i (transverseDerivFromH2 j b))
            (transverseCoordL2 i (transverseDerivFromH2 j b)) := by
      rw [Finset.sum_neg_distrib, Finset.sum_comm]
    _ = -∑ j : Fin 2,
          inner ℂ (transverseDerivFromH2 j b)
            (transverseDerivFromH2 j b) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact (inner_transverseC3L2_eq_sum_coord _ _).symm
    _ = -∑ j : Fin 2, (‖transverseDerivFromH2 j b‖ : ℂ) ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact inner_self_eq_norm_sq_to_K _
    _ = -(reducedTransverseGradientEnergy b : ℂ) := by
      unfold reducedTransverseGradientEnergy
      congr 1
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro j hj
      norm_cast

/-- The shifted fixed-sector diffusion has a literal real quadratic form. -/
theorem inner_reducedInductionDiffusion_eq
    (K : ℤ) (b : TransverseC3H2) :
    inner ℂ (transverseH2Embedding b) (reducedInductionDiffusion K b) =
      -((reducedTransverseGradientEnergy b +
          (2 * Real.pi * (K : ℝ)) ^ 2 *
            ‖transverseH2Embedding b‖ ^ 2 : ℝ) : ℂ) := by
  rw [reducedInductionDiffusion_apply, inner_sub_right,
    inner_smul_right,
    inner_transverseH2Embedding_laplacian_eq_neg_gradientEnergy,
    inner_self_eq_norm_sq_to_K]
  apply Complex.ext
  · norm_num [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  · norm_num [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im]

/-- Real part of the fixed-sector diffusion quadratic form: it equals
`-(Σ_j ‖∂_j b‖² + (2πK)² ‖b‖²)`, i.e. the transverse gradient energy plus the axial Fourier
penalty, with a minus sign.  This is the coercive term of the numerical-range estimate. -/
theorem re_inner_reducedInductionDiffusion_eq
    (K : ℤ) (b : TransverseC3H2) :
    (inner ℂ (transverseH2Embedding b)
      (reducedInductionDiffusion K b)).re =
      -(reducedTransverseGradientEnergy b +
        (2 * Real.pi * (K : ℝ)) ^ 2 *
          ‖transverseH2Embedding b‖ ^ 2) := by
  rw [inner_reducedInductionDiffusion_eq]
  simp only [Complex.neg_re, Complex.ofReal_re]

/-- The fixed-sector diffusion quadratic form is real: its imaginary part vanishes, so diffusion
contributes nothing to the imaginary height of the numerical range. -/
theorem im_inner_reducedInductionDiffusion_eq_zero
    (K : ℤ) (b : TransverseC3H2) :
    (inner ℂ (transverseH2Embedding b)
      (reducedInductionDiffusion K b)).im = 0 := by
  rw [inner_reducedInductionDiffusion_eq]
  simp only [Complex.neg_im, Complex.ofReal_im, neg_zero]

/-! ## Strong-domain coordinates in the product `H¹` energy space -/

/-- Recover the scalar product `H¹` certificate of one coordinate of a
product `H²` vector field.  Its multiplier is `H²Weight / H¹Weight`, hence
exactly `H¹Weight` on physical Fourier coefficients. -/
def productH2CoordToScalarH1 (i : Fin 3) :
    ProductC3H2 →L[ℂ] ProductScalarH1 :=
  productScalarH1ValueCoeffMap.comp (productH2WeightedCoord i)

/-- Forgetting the recovered scalar `H¹` certificate gives the physical
coordinate of the original vector field. -/
theorem productScalarH1Embedding_productH2CoordToScalarH1
    (B : ProductC3H2) (i : Fin 3) :
    productScalarH1Embedding (productH2CoordToScalarH1 i B) =
      productCoordL2 i (productH2Embedding B) := by
  apply productScalarFourierAnalysisNested.injective
  apply lp.ext
  funext k
  apply lp.ext
  funext n
  rw [productScalarFourierAnalysisNested_productScalarH1Embedding,
    productScalarFourierAnalysisNested_coord_eq_productCoeffCLM]
  change productH1ValueFourierMultiplier n k *
      (productScalarH1ValueCoeffMap (productH2WeightedCoord i B)) k n =
    productCoeffCLM n k i (productH2Embedding B)
  rw [productScalarH1ValueCoeffMap_apply,
    productH2WeightedCoord_apply,
    productH2WeightedCoeffs_apply]
  unfold productH1ValueFourierMultiplier
  have hw : (productH1Weight n k : ℂ) ≠ 0 := by
    exact_mod_cast (productH1Weight_pos n k).ne'
  have hsq : (productH1Weight n k : ℂ) ^ 2 =
      (productH2Weight n k : ℂ) := by
    exact_mod_cast productH1Weight_sq n k
  field_simp [hw]
  rw [hsq]

/-- The recovered coordinate's transverse derivative is the coordinate of
the strong vector derivative. -/
theorem productScalarTransverseDeriv_productH2CoordToScalarH1
    (B : ProductC3H2) (i : Fin 3) (j : Fin 2) :
    productScalarTransverseDerivFromH1 j
        (productH2CoordToScalarH1 i B) =
      productCoordL2 i (productTransverseDerivFromH2 j B) := by
  apply productScalarFourierAnalysisNested.injective
  apply lp.ext
  funext k
  apply lp.ext
  funext n
  rw [productScalarFourierAnalysisNested_transverseDerivFromH1,
    productScalarFourierAnalysisNested_coord_eq_productCoeffCLM,
    productCoeffCLM_productTransverseDerivFromH2,
    ← productScalarFourierAnalysisNested_coord_eq_productCoeffCLM,
    ← productScalarH1Embedding_productH2CoordToScalarH1]

/-- One coordinate of the fixed-sector lift, bundled in the product
`H¹` space used by the weak Leibniz theorem. -/
def fixedSectorCoordH1 (K : ℤ) (b : TransverseC3H2) (i : Fin 3) :
    ProductScalarH1 :=
  productH2CoordToScalarH1 i (axialLiftH2 K b)

/-- Forgetting the `H¹` certificate of the `i`-th coordinate of the fixed-sector lift returns the
`i`-th component of the lifted state `axialLiftFromH2 K b` in product `L²`. -/
theorem productScalarH1Embedding_fixedSectorCoordH1
    (K : ℤ) (b : TransverseC3H2) (i : Fin 3) :
    productScalarH1Embedding (fixedSectorCoordH1 K b i) =
      productCoordL2 i (axialLiftFromH2 K b) := by
  unfold fixedSectorCoordH1
  rw [productScalarH1Embedding_productH2CoordToScalarH1,
    productH2Embedding_axialLiftH2]

/-- The transverse `H¹` derivative of the `i`-th coordinate of the fixed-sector lift is the `i`-th
component of the lifted transverse derivative `axialTransverseDerivFromH2 K j b`. -/
theorem productScalarTransverseDeriv_fixedSectorCoordH1
    (K : ℤ) (b : TransverseC3H2) (i : Fin 3) (j : Fin 2) :
    productScalarTransverseDerivFromH1 j (fixedSectorCoordH1 K b i) =
      productCoordL2 i (axialTransverseDerivFromH2 K j b) := by
  unfold fixedSectorCoordH1
  rw [productScalarTransverseDeriv_productH2CoordToScalarH1,
    productTransverseDerivFromH2_axialLiftH2]

/-! ## Transport skewness -/

/-- Real part of the transport pairing is symmetric under exchanging the function and its
transverse derivative: since the velocity coordinate is real-valued, multiplication by it is
self-adjoint, so `Re ⟨d, u_j ∂_j d⟩ = Re ⟨∂_j d, u_j d⟩`.  This is the flip that makes the weak
Leibniz rule produce transport skewness. -/
theorem re_inner_productVelocityCoordMul_derivative_eq_flip
    (u : TransverseRealW1Inf) (j : Fin 2) (d : ProductScalarH1) :
    (inner ℂ (productScalarH1Embedding d)
      (scalarMulProduct
        (pullTransverseScalarLInf
          (transverseW1InfComplexValueCoordLInf j.castSucc u))
        (productScalarTransverseDerivFromH1 j d))).re =
      (inner ℂ (productScalarTransverseDerivFromH1 j d)
        (scalarMulProduct
          (pullTransverseScalarLInf
            (transverseW1InfComplexValueCoordLInf j.castSucc u))
          (productScalarH1Embedding d))).re := by
  calc
    (inner ℂ (productScalarH1Embedding d)
      (scalarMulProduct
        (pullTransverseScalarLInf
          (transverseW1InfComplexValueCoordLInf j.castSucc u))
        (productScalarTransverseDerivFromH1 j d))).re =
      (inner ℂ
        (scalarMulProduct
          (pullTransverseScalarLInf
            (transverseW1InfComplexValueCoordLInf j.castSucc u))
          (productScalarH1Embedding d))
        (productScalarTransverseDerivFromH1 j d)).re :=
      congrArg Complex.re
        (inner_productVelocityCoordMul_selfAdjoint u j.castSucc _ _)
    _ = _ := by
      have h := congrArg Complex.re (inner_conj_symm
        (scalarMulProduct
          (pullTransverseScalarLInf
            (transverseW1InfComplexValueCoordLInf j.castSucc u))
          (productScalarH1Embedding d))
        (productScalarTransverseDerivFromH1 j d))
      simpa only [Complex.conj_re] using h.symm

/-- Each scalar coordinate of fixed-sector transverse transport has zero real
quadratic pairing. -/
theorem re_inner_fixedSectorInductionTransport_coord_eq_zero
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (K : ℤ) (b : TransverseC3H2) (i : Fin 3) :
    (inner ℂ (productCoordL2 i (axialLiftFromH2 K b))
      (productCoordL2 i (fixedSectorInductionTransport u K b))).re = 0 := by
  rw [fixedSectorInductionTransport]
  simp only [sum_apply, ContinuousLinearMap.comp_apply, map_sum, inner_sum]
  simp_rw [productCoordL2_scalarVectorMulProduct]
  rw [← productScalarH1Embedding_fixedSectorCoordH1 K b i]
  simp_rw [← productScalarTransverseDeriv_fixedSectorCoordH1 K b i]
  simpa only [Fin.sum_univ_two, Complex.add_re,
    re_inner_productVelocityCoordMul_derivative_eq_flip] using
      (re_sum_transverse_velocity_transport_eq_zero u hu
        (fixedSectorCoordH1 K b i))

/-- Product-space fixed-sector transverse transport is skew in real part. -/
theorem re_inner_fixedSectorInductionTransport_eq_zero
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (K : ℤ) (b : TransverseC3H2) :
    (inner ℂ (axialLiftFromH2 K b)
      (fixedSectorInductionTransport u K b)).re = 0 := by
  rw [inner_productC3L2_eq_sum_coord]
  simp only [Fin.sum_univ_three, Complex.add_re,
    re_inner_fixedSectorInductionTransport_coord_eq_zero u hu K b,
    zero_add]

/-- The literal reduced transverse transport is skew in real part for every
real Fourier-weakly divergence-free periodic velocity. -/
theorem re_inner_reducedInductionTransport_eq_zero
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (K : ℤ) (b : TransverseC3H2) :
    (inner ℂ (transverseH2Embedding b)
      (reducedInductionTransport u b)).re = 0 := by
  calc
    (inner ℂ (transverseH2Embedding b)
      (reducedInductionTransport u b)).re =
        (inner ℂ
          (axialLiftL2 K (transverseH2Embedding b))
          (axialLiftL2 K (reducedInductionTransport u b))).re :=
      congrArg Complex.re
        ((axialLiftL2 K).inner_map_map
          (transverseH2Embedding b)
          (reducedInductionTransport u b)).symm
    _ = (inner ℂ (axialLiftFromH2 K b)
        (fixedSectorInductionTransport u K b)).re := by
      rw [fixedSectorInductionTransport_intertwines]
      rfl
    _ = 0 := re_inner_fixedSectorInductionTransport_eq_zero u hu K b

/-! ## Axial transport -/

/-- The `L²` quadratic form of multiplication by the real axial velocity
coordinate is real.  Multiplication by the purely imaginary axial Fourier
multiplier is consequently skew in real part. -/
theorem re_inner_fixedSectorInductionAxialTransport_coord_eq_zero
    (u : TransverseRealW1Inf) (K : ℤ)
    (b : TransverseC3H2) (i : Fin 3) :
    (inner ℂ (productCoordL2 i (axialLiftFromH2 K b))
      (productCoordL2 i
        (fixedSectorInductionAxialTransport u K b))).re = 0 := by
  let f : ProductScalarL2 :=
    productCoordL2 i (axialLiftFromH2 K b)
  let M : ProductScalarL2 →L[ℂ] ProductScalarL2 :=
    scalarMulProduct
      (pullTransverseScalarLInf
        (transverseW1InfComplexValueCoordLInf (2 : Fin 3) u))
  have hself : inner ℂ f (M f) = inner ℂ (M f) f :=
    inner_productVelocityCoordMul_selfAdjoint u (2 : Fin 3) f f
  have him : (inner ℂ f (M f)).im = 0 := by
    have himsym := inner_im_symm (𝕜 := ℂ) f (M f)
    have hselfIm := congrArg Complex.im hself
    change (inner ℂ f (M f)).im = -(inner ℂ (M f) f).im at himsym
    linarith
  rw [fixedSectorInductionAxialTransport]
  simp only [ContinuousLinearMap.comp_apply,
    productCoordL2_scalarVectorMulProduct, axialDerivFromH2_apply,
    map_smul]
  change (inner ℂ f (axialMultiplier K • M f)).re = 0
  rw [inner_smul_right]
  unfold axialMultiplier
  norm_num [Complex.mul_re, Complex.mul_im, him]

/-- The axial transport term `2πiK u_3 ·` is skew: the real part of its quadratic form on the
fixed-sector lift vanishes, because `u_3` is real (so multiplication by it is self-adjoint) and
the axial Fourier multiplier is purely imaginary. -/
theorem re_inner_fixedSectorInductionAxialTransport_eq_zero
    (u : TransverseRealW1Inf) (K : ℤ) (b : TransverseC3H2) :
    (inner ℂ (axialLiftFromH2 K b)
      (fixedSectorInductionAxialTransport u K b)).re = 0 := by
  rw [inner_productC3L2_eq_sum_coord]
  simp only [Fin.sum_univ_three, Complex.add_re,
    re_inner_fixedSectorInductionAxialTransport_coord_eq_zero u K b,
    zero_add]

/-- The literal axial transport term is skew in real part. -/
theorem re_inner_reducedInductionAxialTransport_eq_zero
    (u : TransverseRealW1Inf) (K : ℤ) (b : TransverseC3H2) :
    (inner ℂ (transverseH2Embedding b)
      (reducedInductionAxialTransport u K b)).re = 0 := by
  calc
    (inner ℂ (transverseH2Embedding b)
      (reducedInductionAxialTransport u K b)).re =
        (inner ℂ
          (axialLiftL2 K (transverseH2Embedding b))
          (axialLiftL2 K
            (reducedInductionAxialTransport u K b))).re :=
      congrArg Complex.re
        ((axialLiftL2 K).inner_map_map
          (transverseH2Embedding b)
          (reducedInductionAxialTransport u K b)).symm
    _ = (inner ℂ (axialLiftFromH2 K b)
        (fixedSectorInductionAxialTransport u K b)).re := by
      rw [fixedSectorInductionAxialTransport_intertwines]
      rfl
    _ = 0 := re_inner_fixedSectorInductionAxialTransport_eq_zero u K b

/-! ## Stretching and the full quadratic form -/

/-- The stretching form is controlled by the literal essentially bounded
gradient-matrix coefficient. -/
theorem norm_inner_reducedInductionStretching_le
    (u : TransverseRealW1Inf) (b : TransverseC3H2) :
    ‖inner ℂ (transverseH2Embedding b)
      (reducedInductionStretching u b)‖ ≤
      ‖transverseStretchingCoefficient u‖ *
        ‖transverseH2Embedding b‖ ^ 2 := by
  rw [← operatorMul_transverseStretchingCoefficient_eq]
  calc
    ‖inner ℂ (transverseH2Embedding b)
      (operatorMulL2 transverseMeasure
        (transverseStretchingCoefficient u)
        (transverseH2Embedding b))‖ ≤
        ‖transverseH2Embedding b‖ *
          ‖operatorMulL2 transverseMeasure
            (transverseStretchingCoefficient u)
            (transverseH2Embedding b)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖transverseH2Embedding b‖ *
        (‖transverseStretchingCoefficient u‖ *
          ‖transverseH2Embedding b‖) := by
      gcongr
      exact norm_operatorMulL2_apply_apply_le transverseMeasure _ _
    _ = ‖transverseStretchingCoefficient u‖ *
        ‖transverseH2Embedding b‖ ^ 2 := by ring

/-- Real part of the stretching form is bounded above by
`‖∇u‖_∞ ‖b‖²`, with `‖∇u‖_∞` the `L∞` norm of the transverse stretching coefficient matrix. -/
theorem re_inner_reducedInductionStretching_le
    (u : TransverseRealW1Inf) (b : TransverseC3H2) :
    (inner ℂ (transverseH2Embedding b)
      (reducedInductionStretching u b)).re ≤
      ‖transverseStretchingCoefficient u‖ *
        ‖transverseH2Embedding b‖ ^ 2 := by
  calc
    (inner ℂ (transverseH2Embedding b)
      (reducedInductionStretching u b)).re ≤
        |(inner ℂ (transverseH2Embedding b)
          (reducedInductionStretching u b)).re| := le_abs_self _
    _ ≤ ‖inner ℂ (transverseH2Embedding b)
          (reducedInductionStretching u b)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ _ := norm_inner_reducedInductionStretching_le u b

/-- Exact algebraic expansion of the reduced induction quadratic form into
diffusion, transverse transport, axial transport, and stretching. -/
theorem inner_reducedInductionAction_eq
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ)
    (b : TransverseC3H2) :
    inner ℂ (transverseH2Embedding b)
        (reducedInductionAction u ε K b) =
      (ε : ℂ) * inner ℂ (transverseH2Embedding b)
        (reducedInductionDiffusion K b) -
      inner ℂ (transverseH2Embedding b)
        (reducedInductionTransport u b) -
      inner ℂ (transverseH2Embedding b)
        (reducedInductionAxialTransport u K b) +
      inner ℂ (transverseH2Embedding b)
        (reducedInductionStretching u b) := by
  rw [reducedInductionAction]
  simp only [add_apply, sub_apply, smul_apply, inner_add_right,
    inner_sub_right, inner_smul_right]

/-- Literal real-part identity for the full reduced action.  Both transport
terms disappear; the only possible real growth is stretching. -/
theorem re_inner_reducedInductionAction_eq
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (K : ℤ) (b : TransverseC3H2) :
    (inner ℂ (transverseH2Embedding b)
      (reducedInductionAction u ε K b)).re =
      -ε * (reducedTransverseGradientEnergy b +
        (2 * Real.pi * (K : ℝ)) ^ 2 *
          ‖transverseH2Embedding b‖ ^ 2) +
      (inner ℂ (transverseH2Embedding b)
        (reducedInductionStretching u b)).re := by
  rw [inner_reducedInductionAction_eq]
  rw [Complex.add_re, Complex.sub_re, Complex.sub_re,
    re_inner_reducedInductionTransport_eq_zero u hu K b,
    re_inner_reducedInductionAxialTransport_eq_zero u K b]
  rw [Complex.mul_re, re_inner_reducedInductionDiffusion_eq,
    im_inner_reducedInductionDiffusion_eq_zero]
  norm_num
  ring

end

end FastDynamo
