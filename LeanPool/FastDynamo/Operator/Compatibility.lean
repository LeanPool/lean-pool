/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.InductionDivergence

/-!
# The physical induction action and its compatibility with the auxiliary one

The paper writes the induction equation in physical curl form (`eq:physical-generator`),
`ε Δ B + curl (u × B)`, whereas the spectral argument is carried out for the
auxiliary transport/stretching action of `FastDynamo.Operator.Product`.  This
module constructs the curl-form operator and proves that the two actions agree
once the velocity and the field are divergence-free.

The physical action is realized in a Fourier model of vector-valued `H⁻²`: an
`L²` coefficient `f̂(n,k)` is represented by `f̂(n,k) / (1 + |ξ|²)`.  In that
model the distributional curl of an arbitrary `L²` vector field is a bounded
map, so neither pointwise representatives nor a weak product rule enter.  Once
solenoidality is known, the auxiliary action embeds onto the physical one.  This
is the non-circular bridge delivering the curl-form eigenvalue equation
`L_{ε,u}V^ε = λ_ε V^ε` of Theorem 1.2 (`eq:main-spectral-conclusion`).

Solenoidality itself is the auxiliary solenoidality theorem, which starts from
the auxiliary operator and is proved by the weak Leibniz and scalar-energy route
in `FastDynamo.Finish.RealSolution`.  It is not in the paper, which recovers the
axial component in `lem:axial-recovery` (Lemma 8.1) instead.

## Contents

* `ProductC3HMinus2`, `productL2ToHMinus2`, `productL2ToHMinus2_injective`: the
  Fourier realization of vector-valued `H⁻²` and the injective `L²` embedding.
* `productWeakCurl`: the distributional curl as a bounded map `L² → H⁻²`.
* `productCrossWithVelocity`: the cross product with the real velocity `u`.
* `productPhysicalInductionAction`, `productPhysicalInductionOperator`: the
  curl-form action and its operator with complete `H²` domain.
* `productWeakCurl_crossWithVelocity_eq_embedding_weakCurl`: the weak curl of
  `u × B` is the embedded `L²` curl built from the Leibniz certificates.
* `productInductionAction_toHMinus2_eq_physical`,
  `productInductionEigenpair_to_physical`: equality of the two actions and the
  resulting transfer of eigenpairs.
-/

@[expose] public section

/-!
## The physical weak induction operator

The paper defines the induction action in physical form as

`epsilon * Delta B + curl (u cross B)`.

It is placed here in the Fourier realization of `H^-2`.  An `L2` coefficient
`fhat(n,k)` is represented by `fhat(n,k) / (1 + |xi|^2)`.  Consequently the
distributional curl of an arbitrary `L2` vector field is a bounded map into
this space.  No choice of pointwise representatives or weak product rule
enters.
-/

namespace FastDynamo

noncomputable section

/-! ## A Fourier realization of vector-valued `H^-2` -/

/-- Scalar Fourier coefficients with the `H^-2` weight already absorbed. -/
abbrev ProductScalarHMinus2 := ProductScalarFourierL2

/-- Three coordinate arrays of scalar `H^-2` Fourier coefficients. -/
abbrev ProductC3HMinus2 := WeightedProductC3Coeffs

/-- The inverse inhomogeneous order-two weight. -/
def productHMinus2EmbedMultiplier
    (n : TransverseFrequency) (k : ℤ) : ℂ :=
  (productH2Weight n k : ℂ)⁻¹

/--
The reciprocal order-two weight has modulus at most one, so dividing coefficients by it is a
contraction from `L²` coefficients into the `H⁻²` model.
-/
lemma norm_productHMinus2EmbedMultiplier_le_one
    (n : TransverseFrequency) (k : ℤ) :
    ‖productHMinus2EmbedMultiplier n k‖ ≤ 1 := by
  rw [productHMinus2EmbedMultiplier, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (productH2Weight_pos n k)]
  exact (inv_le_one₀ (productH2Weight_pos n k)).2 (by
    rw [productH2Weight_eq_one_add_energy]
    exact le_add_of_nonneg_right (productFrequencyEnergy_nonneg n k))

/-- Divide every scalar Fourier coefficient by the inhomogeneous order-two
weight. -/
def productScalarL2ToHMinus2Coeff :
    ProductScalarFourierL2 →L[ℂ] ProductScalarHMinus2 :=
  nestedScalarMultiplier
    (fun k n ↦ productHMinus2EmbedMultiplier n k)
    (fun k n ↦ norm_productHMinus2EmbedMultiplier_le_one n k)

/--
The scalar `L² → H⁻²` coefficient map divides the coefficient at `(n, k)` by the order-two
weight `productH2Weight n k`.
-/
@[simp] theorem productScalarL2ToHMinus2Coeff_apply
    (a : ProductScalarFourierL2) (k : ℤ) (n : TransverseFrequency) :
    productScalarL2ToHMinus2Coeff a k n =
      a k n / (productH2Weight n k : ℂ) := by
  change (productH2Weight n k : ℂ)⁻¹ * a k n = _
  rw [inv_mul_eq_div]

/-- Apply a scalar coefficient map to all three coordinate arrays. -/
def mapWeightedProductCoeff
    (T : ProductScalarFourierL2 →L[ℂ] ProductScalarFourierL2) :
    WeightedProductC3Coeffs →L[ℂ] WeightedProductC3Coeffs :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 3 ↦ ProductScalarFourierL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ T.comp
      (PiLp.proj 2 (fun _ : Fin 3 ↦ ProductScalarFourierL2) i))

/--
`mapWeightedProductCoeff T` applies the scalar coefficient map `T` separately in each of the
three coordinate arrays.
-/
@[simp] theorem mapWeightedProductCoeff_apply
    (T : ProductScalarFourierL2 →L[ℂ] ProductScalarFourierL2)
    (a : WeightedProductC3Coeffs) (i : Fin 3) :
    mapWeightedProductCoeff T a i = T (a i) :=
  rfl

/-- The canonical continuous embedding `L2 -> H^-2`. -/
def productL2ToHMinus2 : ProductC3L2 →L[ℂ] ProductC3HMinus2 :=
  mapWeightedProductCoeff productScalarL2ToHMinus2Coeff |>.comp
    productC3FourierAnalysis

/--
Entrywise formula for the canonical `L² → H⁻²` embedding: it divides each Fourier coefficient of
`V` by the order-two weight.
-/
@[simp] theorem productL2ToHMinus2_apply
    (V : ProductC3L2) (i : Fin 3) (k : ℤ)
    (n : TransverseFrequency) :
    productL2ToHMinus2 V i k n =
      productCoeffCLM n k i V / (productH2Weight n k : ℂ) := by
  change productScalarL2ToHMinus2Coeff
      (productC3FourierAnalysis V i) k n = _
  rw [productScalarL2ToHMinus2Coeff_apply,
    productC3FourierAnalysis_apply]

/--
The `L² → H⁻²` embedding is injective, since dividing by the nonvanishing weight is injective
frequency by frequency. This is what lets an `H⁻²` identity be read back in `L²`.
-/
theorem productL2ToHMinus2_injective :
    Function.Injective productL2ToHMinus2 := by
  intro V W h
  apply productC3L2_ext_coeff
  intro n k i
  have hi := congrArg (fun a : ProductC3HMinus2 ↦ a i k n) h
  simp only [productL2ToHMinus2_apply] at hi
  exact (div_left_inj' (show (productH2Weight n k : ℂ) ≠ 0 by
    exact_mod_cast (productH2Weight_pos n k).ne')).mp hi

/-! ## Distributional curl into `H^-2` -/

/-- The first weak derivative of a scalar `L2` field, represented in
Fourier `H^-2`. -/
def productTransverseWeakDerivToHMinus2 (j : Fin 2) :
    ProductScalarL2 →L[ℂ] ProductScalarHMinus2 :=
  productTransverseDerivCoeffMap j |>.comp
    productScalarFourierAnalysisNested.toContinuousLinearEquiv.toContinuousLinearMap

/-- The axial weak derivative of a scalar `L2` field, represented in
Fourier `H^-2`. -/
def productAxialWeakDerivToHMinus2 :
    ProductScalarL2 →L[ℂ] ProductScalarHMinus2 :=
  productAxialDerivCoeffMap.comp
    productScalarFourierAnalysisNested.toContinuousLinearEquiv.toContinuousLinearMap

/--
The `j`-th transverse weak derivative in the `H⁻²` model multiplies the `(n, k)` coefficient by
`2π i n_j` and divides by the order-two weight.
-/
@[simp] theorem productTransverseWeakDerivToHMinus2_apply
    (j : Fin 2) (f : ProductScalarL2) (k : ℤ)
    (n : TransverseFrequency) :
    productTransverseWeakDerivToHMinus2 j f k n =
      (2 * Real.pi * Complex.I * (n j : ℂ)) /
          (productH2Weight n k : ℂ) *
        productScalarFourierAnalysisNested f k n := by
  simp [productTransverseWeakDerivToHMinus2,
    productTransverseDerivCoeffMap,
    productTransverseDerivFourierMultiplier]

/--
The axial weak derivative in the `H⁻²` model multiplies the `(n, k)` coefficient by `2π i k` and
divides by the order-two weight.
-/
@[simp] theorem productAxialWeakDerivToHMinus2_apply
    (f : ProductScalarL2) (k : ℤ) (n : TransverseFrequency) :
    productAxialWeakDerivToHMinus2 f k n =
      (2 * Real.pi * Complex.I * (k : ℂ)) /
          (productH2Weight n k : ℂ) *
        productScalarFourierAnalysisNested f k n := by
  simp [productAxialWeakDerivToHMinus2,
    productAxialDerivCoeffMap, productAxialDerivFourierMultiplier]

/-- Coordinate zero of the distributional curl. -/
def productWeakCurlCoord0 :
    ProductC3L2 →L[ℂ] ProductScalarHMinus2 :=
  (productTransverseWeakDerivToHMinus2 (1 : Fin 2)).comp
      (productCoordL2 (2 : Fin 3)) -
    productAxialWeakDerivToHMinus2.comp (productCoordL2 (1 : Fin 3))

/-- Coordinate one of the distributional curl. -/
def productWeakCurlCoord1 :
    ProductC3L2 →L[ℂ] ProductScalarHMinus2 :=
  productAxialWeakDerivToHMinus2.comp (productCoordL2 (0 : Fin 3)) -
    (productTransverseWeakDerivToHMinus2 (0 : Fin 2)).comp
      (productCoordL2 (2 : Fin 3))

/-- Coordinate two of the distributional curl. -/
def productWeakCurlCoord2 :
    ProductC3L2 →L[ℂ] ProductScalarHMinus2 :=
  (productTransverseWeakDerivToHMinus2 (0 : Fin 2)).comp
      (productCoordL2 (1 : Fin 3)) -
    (productTransverseWeakDerivToHMinus2 (1 : Fin 2)).comp
      (productCoordL2 (0 : Fin 3))

/-- Distributional curl as a bounded map `L2(C3) -> H^-2(C3)`. -/
def productWeakCurl : ProductC3L2 →L[ℂ] ProductC3HMinus2 :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 3 ↦ ProductScalarHMinus2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦
      ![productWeakCurlCoord0, productWeakCurlCoord1,
        productWeakCurlCoord2] i)

/--
Frequency formula for the first component of the distributional curl:
`(2π i n₁ Ŵ₂ - 2π i k Ŵ₁) / w₂(n,k)`.
-/
@[simp] theorem productWeakCurl_apply_zero
    (W : ProductC3L2) (k : ℤ) (n : TransverseFrequency) :
    productWeakCurl W (0 : Fin 3) k n =
      ((2 * Real.pi * Complex.I * (n (1 : Fin 2) : ℂ)) *
          productCoeffCLM n k (2 : Fin 3) W -
        (2 * Real.pi * Complex.I * (k : ℂ)) *
          productCoeffCLM n k (1 : Fin 3) W) /
        (productH2Weight n k : ℂ) := by
  change
    productTransverseWeakDerivToHMinus2 (1 : Fin 2)
          (productCoordL2 (2 : Fin 3) W) k n -
        productAxialWeakDerivToHMinus2
          (productCoordL2 (1 : Fin 3) W) k n = _
  rw [productTransverseWeakDerivToHMinus2_apply,
    productAxialWeakDerivToHMinus2_apply,
    productScalarFourierAnalysisNested_coord_eq_productCoeffCLM,
    productScalarFourierAnalysisNested_coord_eq_productCoeffCLM]
  ring

/--
Frequency formula for the second component of the distributional curl:
`(2π i k Ŵ₀ - 2π i n₀ Ŵ₂) / w₂(n,k)`.
-/
@[simp] theorem productWeakCurl_apply_one
    (W : ProductC3L2) (k : ℤ) (n : TransverseFrequency) :
    productWeakCurl W (1 : Fin 3) k n =
      ((2 * Real.pi * Complex.I * (k : ℂ)) *
          productCoeffCLM n k (0 : Fin 3) W -
        (2 * Real.pi * Complex.I * (n (0 : Fin 2) : ℂ)) *
          productCoeffCLM n k (2 : Fin 3) W) /
        (productH2Weight n k : ℂ) := by
  change
    productAxialWeakDerivToHMinus2
          (productCoordL2 (0 : Fin 3) W) k n -
        productTransverseWeakDerivToHMinus2 (0 : Fin 2)
          (productCoordL2 (2 : Fin 3) W) k n = _
  rw [productAxialWeakDerivToHMinus2_apply,
    productTransverseWeakDerivToHMinus2_apply,
    productScalarFourierAnalysisNested_coord_eq_productCoeffCLM,
    productScalarFourierAnalysisNested_coord_eq_productCoeffCLM]
  ring

/--
Frequency formula for the third component of the distributional curl:
`(2π i n₀ Ŵ₁ - 2π i n₁ Ŵ₀) / w₂(n,k)`.
-/
@[simp] theorem productWeakCurl_apply_two
    (W : ProductC3L2) (k : ℤ) (n : TransverseFrequency) :
    productWeakCurl W (2 : Fin 3) k n =
      ((2 * Real.pi * Complex.I * (n (0 : Fin 2) : ℂ)) *
          productCoeffCLM n k (1 : Fin 3) W -
        (2 * Real.pi * Complex.I * (n (1 : Fin 2) : ℂ)) *
          productCoeffCLM n k (0 : Fin 3) W) /
        (productH2Weight n k : ℂ) := by
  change
    productTransverseWeakDerivToHMinus2 (0 : Fin 2)
          (productCoordL2 (1 : Fin 3) W) k n -
        productTransverseWeakDerivToHMinus2 (1 : Fin 2)
          (productCoordL2 (0 : Fin 3) W) k n = _
  rw [productTransverseWeakDerivToHMinus2_apply,
    productTransverseWeakDerivToHMinus2_apply,
    productScalarFourierAnalysisNested_coord_eq_productCoeffCLM,
    productScalarFourierAnalysisNested_coord_eq_productCoeffCLM]
  ring

/-! ## Cross product with the real velocity -/

/-- Scalar multiplication `LInf(C) x L2(C) -> L2(C)` on the product torus. -/
def productScalarMul :
    ProductScalarLInf →L[ℂ] ProductScalarL2 →L[ℂ] ProductScalarL2 :=
  scalarVectorMulL2 (E := ℂ) productMeasure

/-- One pulled-back scalar component of the real velocity. -/
def productVelocityCoord (u : TransverseRealW1Inf) (i : Fin 3) :
    ProductScalarLInf :=
  pullTransverseScalarLInf (transverseW1InfComplexValueCoordLInf i u)

/-- One coordinate product `u_i B_j`. -/
def productVelocityTimesCoord (u : TransverseRealW1Inf)
    (i j : Fin 3) : ProductC3L2 →L[ℂ] ProductScalarL2 :=
  (productScalarMul (productVelocityCoord u i)).comp (productCoordL2 j)

/-- Zeroth scalar coordinate of the product-torus cross product `u × B`. -/
def productCrossWithVelocityCoord0 (u : TransverseRealW1Inf) :
    ProductC3L2 →L[ℂ] ProductScalarL2 :=
  productVelocityTimesCoord u (1 : Fin 3) (2 : Fin 3) -
    productVelocityTimesCoord u (2 : Fin 3) (1 : Fin 3)

/-- First scalar coordinate of the product-torus cross product `u × B`. -/
def productCrossWithVelocityCoord1 (u : TransverseRealW1Inf) :
    ProductC3L2 →L[ℂ] ProductScalarL2 :=
  productVelocityTimesCoord u (2 : Fin 3) (0 : Fin 3) -
    productVelocityTimesCoord u (0 : Fin 3) (2 : Fin 3)

/-- Second scalar coordinate of the product-torus cross product `u × B`. -/
def productCrossWithVelocityCoord2 (u : TransverseRealW1Inf) :
    ProductC3L2 →L[ℂ] ProductScalarL2 :=
  productVelocityTimesCoord u (0 : Fin 3) (1 : Fin 3) -
    productVelocityTimesCoord u (1 : Fin 3) (0 : Fin 3)

/-- Pointwise `u cross B`, bundled as a bounded map on quotient `L2`. -/
def productCrossWithVelocity (u : TransverseRealW1Inf) :
    ProductC3L2 →L[ℂ] ProductC3L2 :=
  productC3OfCoordsL2.comp
    ((PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 3 ↦ ProductScalarL2)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi fun i ↦
          ![productCrossWithVelocityCoord0 u,
            productCrossWithVelocityCoord1 u,
            productCrossWithVelocityCoord2 u] i))

/-- First coordinate of `u × B`: the difference `u₁ B₂ - u₂ B₁` of coordinate products. -/
@[simp] theorem productCoordL2_productCrossWithVelocity_zero
    (u : TransverseRealW1Inf) (B : ProductC3L2) :
    productCoordL2 (0 : Fin 3) (productCrossWithVelocity u B) =
      productVelocityTimesCoord u (1 : Fin 3) (2 : Fin 3) B -
        productVelocityTimesCoord u (2 : Fin 3) (1 : Fin 3) B := by
  rw [productCrossWithVelocity, ContinuousLinearMap.comp_apply,
    productCoordL2_productC3OfCoordsL2]
  rfl

/-- Second coordinate of `u × B`: the difference `u₂ B₀ - u₀ B₂` of coordinate products. -/
@[simp] theorem productCoordL2_productCrossWithVelocity_one
    (u : TransverseRealW1Inf) (B : ProductC3L2) :
    productCoordL2 (1 : Fin 3) (productCrossWithVelocity u B) =
      productVelocityTimesCoord u (2 : Fin 3) (0 : Fin 3) B -
        productVelocityTimesCoord u (0 : Fin 3) (2 : Fin 3) B := by
  rw [productCrossWithVelocity, ContinuousLinearMap.comp_apply,
    productCoordL2_productC3OfCoordsL2]
  rfl

/-- Third coordinate of `u × B`: the difference `u₀ B₁ - u₁ B₀` of coordinate products. -/
@[simp] theorem productCoordL2_productCrossWithVelocity_two
    (u : TransverseRealW1Inf) (B : ProductC3L2) :
    productCoordL2 (2 : Fin 3) (productCrossWithVelocity u B) =
      productVelocityTimesCoord u (0 : Fin 3) (1 : Fin 3) B -
        productVelocityTimesCoord u (1 : Fin 3) (0 : Fin 3) B := by
  rw [productCrossWithVelocity, ContinuousLinearMap.comp_apply,
    productCoordL2_productC3OfCoordsL2]
  rfl

/-! ## The physical weak operator -/

/-- The `H^-2` realization of the physical induction action
`epsilon * Delta B + curl (u cross B)`. -/
def productPhysicalInductionAction
    (u : TransverseRealW1Inf) (epsilon : ℝ) :
    ProductC3H2 →L[ℂ] ProductC3HMinus2 :=
  (epsilon : ℂ) • (productL2ToHMinus2.comp productLaplacianFromH2) +
    productWeakCurl.comp
      ((productCrossWithVelocity u).comp productH2Embedding)

/-- The physical weak induction operator with complete `H2` domain and
ambient Fourier `H^-2`. -/
def productPhysicalInductionOperator
    (u : TransverseRealW1Inf) (epsilon : ℝ) :
    DomainOperator ProductC3HMinus2 ProductC3H2 where
  embedding := productL2ToHMinus2.comp productH2Embedding
  embedding_injective := productL2ToHMinus2_injective.comp
    productH2Embedding_injective
  op := productPhysicalInductionAction u epsilon

end

end FastDynamo

/-!
## Compatibility of the auxiliary and physical induction actions

The transport/stretching action agrees in `H⁻²` with the physical curl-form action once the input
field and velocity are divergence-free.  These results are the non-circular bridge used after the
auxiliary solenoidality theorem.
-/

namespace FastDynamo

noncomputable section

/-! ## Cross-product coordinates -/

/--
The first coordinate of `u × B`, for `B` given by an `H²` graph element, is the explicit `L²`
field `productVelocityCrossCoord0 u B` built from the components of `u` and `B`.
-/
theorem productCoordL2_productCrossWithVelocity_H2_zero
    (u : TransverseRealW1Inf) (B : ProductC3H2) :
    productCoordL2 (0 : Fin 3)
        (productCrossWithVelocity u (productH2Embedding B)) =
      productVelocityCrossCoord0 u B := by
  rw [productCoordL2_productCrossWithVelocity_zero]
  rfl

/--
The second coordinate of `u × B`, for `B` given by an `H²` graph element, is the explicit `L²`
field `productVelocityCrossCoord1 u B`.
-/
theorem productCoordL2_productCrossWithVelocity_H2_one
    (u : TransverseRealW1Inf) (B : ProductC3H2) :
    productCoordL2 (1 : Fin 3)
        (productCrossWithVelocity u (productH2Embedding B)) =
      productVelocityCrossCoord1 u B := by
  rw [productCoordL2_productCrossWithVelocity_one]
  rfl

/--
The third coordinate of `u × B`, for `B` given by an `H²` graph element, is the explicit `L²`
field `productVelocityCrossCoord2 u B`.
-/
theorem productCoordL2_productCrossWithVelocity_H2_two
    (u : TransverseRealW1Inf) (B : ProductC3H2) :
    productCoordL2 (2 : Fin 3)
        (productCrossWithVelocity u (productH2Embedding B)) =
      productVelocityCrossCoord2 u B := by
  rw [productCoordL2_productCrossWithVelocity_two]
  rfl

/-! ## Weak-curl compatibility -/

/-- The distributional curl of `u × B` is the `H⁻²` embedding of the
`L²` weak curl constructed from the rigorous Leibniz certificates. -/
theorem productWeakCurl_crossWithVelocity_eq_embedding_weakCurl
    (u : TransverseRealW1Inf) (B : ProductC3H2) :
    productWeakCurl
        (productCrossWithVelocity u (productH2Embedding B)) =
      productL2ToHMinus2 (productVelocityCrossWeakCurl u B) := by
  apply PiLp.ext
  intro i
  apply lp.ext
  funext k
  apply lp.ext
  funext n
  fin_cases i
  · change productWeakCurl
        (productCrossWithVelocity u (productH2Embedding B))
          (0 : Fin 3) k n =
      productL2ToHMinus2 (productVelocityCrossWeakCurl u B)
        (0 : Fin 3) k n
    rw [productWeakCurl_apply_zero, productL2ToHMinus2_apply]
    rw [productCoeffCLM_eq_flatCoordAnalysis,
      productCoeffCLM_eq_flatCoordAnalysis,
      productCoeffCLM_eq_flatCoordAnalysis]
    rw [productCoordL2_productCrossWithVelocity_H2_two,
      productCoordL2_productCrossWithVelocity_H2_one,
      productCoordL2_productVelocityCrossWeakCurl u B (0 : Fin 3)]
    change
      ((2 * Real.pi * Complex.I * (n (1 : Fin 2) : ℂ)) *
          productScalarFourierAnalysisFlat
            (productVelocityCrossCoord2 u B) (Fin.snoc n k) -
        (2 * Real.pi * Complex.I * (k : ℂ)) *
          productScalarFourierAnalysisFlat
            (productVelocityCrossCoord1 u B) (Fin.snoc n k)) /
          (productH2Weight n k : ℂ) =
        productScalarFourierAnalysisFlat
          (productVelocityCrossWeakCurlCoord0 u B) (Fin.snoc n k) /
            (productH2Weight n k : ℂ)
    rw [productVelocityCrossWeakCurlCoord0_flatCoeff]
    have hm1 : (Fin.snoc n k : Fin 3 → ℤ) (1 : Fin 3) = n 1 := by
      change (Fin.snoc n k : Fin 3 → ℤ)
        (Fin.castSucc (1 : Fin 2)) = n 1
      rw [Fin.snoc_castSucc]
    have hm2 : (Fin.snoc n k : Fin 3 → ℤ) (2 : Fin 3) = k := by
      change (Fin.snoc n k : Fin 3 → ℤ) (Fin.last 2) = k
      rw [Fin.snoc_last]
    rw [hm1, hm2]
  · change productWeakCurl
        (productCrossWithVelocity u (productH2Embedding B))
          (1 : Fin 3) k n =
      productL2ToHMinus2 (productVelocityCrossWeakCurl u B)
        (1 : Fin 3) k n
    rw [productWeakCurl_apply_one, productL2ToHMinus2_apply]
    rw [productCoeffCLM_eq_flatCoordAnalysis,
      productCoeffCLM_eq_flatCoordAnalysis,
      productCoeffCLM_eq_flatCoordAnalysis]
    rw [productCoordL2_productCrossWithVelocity_H2_zero,
      productCoordL2_productCrossWithVelocity_H2_two,
      productCoordL2_productVelocityCrossWeakCurl u B (1 : Fin 3)]
    change
      ((2 * Real.pi * Complex.I * (k : ℂ)) *
          productScalarFourierAnalysisFlat
            (productVelocityCrossCoord0 u B) (Fin.snoc n k) -
        (2 * Real.pi * Complex.I * (n (0 : Fin 2) : ℂ)) *
          productScalarFourierAnalysisFlat
            (productVelocityCrossCoord2 u B) (Fin.snoc n k)) /
          (productH2Weight n k : ℂ) =
        productScalarFourierAnalysisFlat
          (productVelocityCrossWeakCurlCoord1 u B) (Fin.snoc n k) /
            (productH2Weight n k : ℂ)
    rw [productVelocityCrossWeakCurlCoord1_flatCoeff]
    have hm0 : (Fin.snoc n k : Fin 3 → ℤ) (0 : Fin 3) = n 0 := by
      change (Fin.snoc n k : Fin 3 → ℤ)
        (Fin.castSucc (0 : Fin 2)) = n 0
      rw [Fin.snoc_castSucc]
    have hm2 : (Fin.snoc n k : Fin 3 → ℤ) (2 : Fin 3) = k := by
      change (Fin.snoc n k : Fin 3 → ℤ) (Fin.last 2) = k
      rw [Fin.snoc_last]
    rw [hm0, hm2]
  · change productWeakCurl
        (productCrossWithVelocity u (productH2Embedding B))
          (2 : Fin 3) k n =
      productL2ToHMinus2 (productVelocityCrossWeakCurl u B)
        (2 : Fin 3) k n
    rw [productWeakCurl_apply_two, productL2ToHMinus2_apply]
    rw [productCoeffCLM_eq_flatCoordAnalysis,
      productCoeffCLM_eq_flatCoordAnalysis,
      productCoeffCLM_eq_flatCoordAnalysis]
    rw [productCoordL2_productCrossWithVelocity_H2_one,
      productCoordL2_productCrossWithVelocity_H2_zero,
      productCoordL2_productVelocityCrossWeakCurl u B (2 : Fin 3)]
    change
      ((2 * Real.pi * Complex.I * (n (0 : Fin 2) : ℂ)) *
          productScalarFourierAnalysisFlat
            (productVelocityCrossCoord1 u B) (Fin.snoc n k) -
        (2 * Real.pi * Complex.I * (n (1 : Fin 2) : ℂ)) *
          productScalarFourierAnalysisFlat
            (productVelocityCrossCoord0 u B) (Fin.snoc n k)) /
          (productH2Weight n k : ℂ) =
        productScalarFourierAnalysisFlat
          (productVelocityCrossWeakCurlCoord2 u B) (Fin.snoc n k) /
            (productH2Weight n k : ℂ)
    rw [productVelocityCrossWeakCurlCoord2_flatCoeff]
    have hm0 : (Fin.snoc n k : Fin 3 → ℤ) (0 : Fin 3) = n 0 := by
      change (Fin.snoc n k : Fin 3 → ℤ)
        (Fin.castSucc (0 : Fin 2)) = n 0
      rw [Fin.snoc_castSucc]
    have hm1 : (Fin.snoc n k : Fin 3 → ℤ) (1 : Fin 3) = n 1 := by
      change (Fin.snoc n k : Fin 3 → ℤ)
        (Fin.castSucc (1 : Fin 2)) = n 1
      rw [Fin.snoc_castSucc]
    rw [hm0, hm1]

/-! ## Equality of the two actions -/

/-- If both `u` and `B` are divergence-free, the auxiliary
transport/stretching action and the physical curl-form action agree exactly
after embedding in `H⁻²`. -/
theorem productInductionAction_toHMinus2_eq_physical
    (u : TransverseRealW1Inf) (hdivu : IsTransverseDivergenceFree u)
    (ε : ℝ) (B : ProductC3H2)
    (hdivB : productDivergenceFromH2 B = 0) :
    productL2ToHMinus2 (productInductionAction u ε B) =
      productPhysicalInductionAction u ε B := by
  rw [productInductionAction_eq_diffusion_add_lower,
    map_add, map_smul]
  change
    (ε : ℂ) • productL2ToHMinus2 (productLaplacianFromH2 B) +
        productL2ToHMinus2 (productInductionLowerField u B) =
      (ε : ℂ) • productL2ToHMinus2 (productLaplacianFromH2 B) +
        productWeakCurl
          (productCrossWithVelocity u (productH2Embedding B))
  rw [productWeakCurl_crossWithVelocity_eq_embedding_weakCurl]
  congr 1
  apply congrArg productL2ToHMinus2
  have hcurl :=
    productInductionLowerField_add_velocityDiv_eq_weakCurl u hdivu B
  rw [hdivB, map_zero] at hcurl
  simpa only [add_zero] using hcurl

/-- An auxiliary eigenpair whose eigenfunction is already known to be
solenoidal transfers to the physical weak operator. -/
theorem productInductionEigenpair_to_physical
    (u : TransverseRealW1Inf) (hdivu : IsTransverseDivergenceFree u)
    (ε : ℝ) (eigenvalue : ℂ) (B : ProductC3H2)
    (hdivB : productDivergenceFromH2 B = 0)
    (h : (productInductionOperator u ε).IsEigenpair eigenvalue B) :
    (productPhysicalInductionOperator u ε).IsEigenpair eigenvalue B := by
  rcases h with ⟨hnonzero, heigen⟩
  constructor
  · change productL2ToHMinus2 (productH2Embedding B) ≠ 0
    change productH2Embedding B ≠ 0 at hnonzero
    intro hz
    apply hnonzero
    apply productL2ToHMinus2_injective
    simpa only [map_zero] using hz
  · change productPhysicalInductionAction u ε B =
      eigenvalue • productL2ToHMinus2 (productH2Embedding B)
    change productInductionAction u ε B =
      eigenvalue • productH2Embedding B at heigen
    rw [← productInductionAction_toHMinus2_eq_physical u hdivu ε B hdivB,
      ← map_smul]
    exact congrArg productL2ToHMinus2 heigen

end

end FastDynamo
