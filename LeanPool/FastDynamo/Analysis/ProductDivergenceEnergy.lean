/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.ProductScalarEnergy
public import LeanPool.FastDynamo.Analysis.ProductVectorCalculus

/-!
# Product divergence in the scalar energy scale

This module places the divergence of a product Fourier `H²` vector field in
the scalar `H¹` space and constructs distributional divergence as a bounded
map `L²(C³) → H⁻¹`.  All compatibility statements are proved directly from
the complete product Fourier basis.

The stored coefficient of `productDivergenceH1 B` is

`sqrt (1 + |xi|^2) * (i xi · Bhat)`,

whereas the Riesz coefficient of `productWeakDivergence V` is

`(i xi · Vhat) / sqrt (1 + |xi|^2)`.

These reciprocal weights make the weak divergence of an `H²` field exactly
the canonical `H¹ → H⁻¹` inclusion of its strong divergence.  They also make
commutation of divergence with the Laplacian an exact multiplier identity.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-! ## Strong divergence with its `H¹` certificate -/

/-- Read one coordinate of the stored product `H²` coefficient array. -/
def productH2WeightedCoord (i : Fin 3) :
    ProductC3H2 →L[ℂ] ProductScalarFourierL2 :=
  (PiLp.proj 2 (fun _ : Fin 3 ↦ ProductScalarFourierL2) i).comp
    productH2WeightedCoeffs

/-- Reading the `i`-th coordinate of the stored `H²` coefficient array of `B` returns the `i`-th
entry of `productH2WeightedCoeffs B`. -/
@[simp] theorem productH2WeightedCoord_apply
    (i : Fin 3) (B : ProductC3H2) :
    productH2WeightedCoord i B = productH2WeightedCoeffs B i :=
  rfl

/-- The divergence of a product `H²` vector field, with its scalar `H¹`
Fourier weight stored in the codomain. -/
def productDivergenceH1 : ProductC3H2 →L[ℂ] ProductScalarH1 :=
  (∑ j : Fin 2,
      (productScalarH1TransverseDerivCoeffMap j).comp
        (productH2WeightedCoord j.castSucc)) +
    productScalarH1AxialDerivCoeffMap.comp
      (productH2WeightedCoord (2 : Fin 3))

/-- The scalar `H¹` divergence of an `H²` field is the sum of the two transverse `H¹` derivative
coefficient maps applied to the corresponding stored components, plus the axial derivative
coefficient map applied to the third component. -/
theorem productDivergenceH1_apply (B : ProductC3H2) :
    productDivergenceH1 B =
      (∑ j : Fin 2,
        productScalarH1TransverseDerivCoeffMap j
          (productH2WeightedCoeffs B j.castSucc)) +
      productScalarH1AxialDerivCoeffMap
        (productH2WeightedCoeffs B (2 : Fin 3)) := by
  simp [productDivergenceH1, productH2WeightedCoord]

/-- Exact stored Fourier coefficient of the scalar `H¹` divergence. -/
theorem productDivergenceH1_coeff
    (B : ProductC3H2) (k : ℤ) (n : TransverseFrequency) :
    productDivergenceH1 B k n =
      (productH1Weight n k : ℂ) *
        productFrequencyDivergenceCoeff n k (productH2Embedding B) := by
  rw [productDivergenceH1_apply]
  simp only [Fin.sum_univ_two]
  change
    productScalarH1TransverseDerivCoeffMap (0 : Fin 2)
          (productH2WeightedCoeffs B (0 : Fin 3)) k n +
        productScalarH1TransverseDerivCoeffMap (1 : Fin 2)
          (productH2WeightedCoeffs B (1 : Fin 3)) k n +
      productScalarH1AxialDerivCoeffMap
          (productH2WeightedCoeffs B (2 : Fin 3)) k n = _
  rw [productScalarH1TransverseDerivCoeffMap_apply,
    productScalarH1TransverseDerivCoeffMap_apply,
    productScalarH1AxialDerivCoeffMap_apply,
    productH2WeightedCoeffs_apply,
    productH2WeightedCoeffs_apply,
    productH2WeightedCoeffs_apply]
  unfold productFrequencyDivergenceCoeff
  simp only [Fin.sum_univ_two]
  have h0 : (0 : Fin 2).castSucc = (0 : Fin 3) := rfl
  have h1 : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
  rw [h0, h1]
  rw [productH1TransverseDerivFourierMultiplier,
    productH1TransverseDerivFourierMultiplier,
    productH1AxialDerivFourierMultiplier]
  have hw : (productH1Weight n k : ℂ) ≠ 0 := by
    exact_mod_cast (productH1Weight_pos n k).ne'
  have hsq : (productH1Weight n k : ℂ) ^ 2 =
      (productH2Weight n k : ℂ) := by
    exact_mod_cast productH1Weight_sq n k
  field_simp [hw]
  rw [hsq]

/-- Forgetting the scalar `H¹` certificate recovers the previously defined
`L²` divergence exactly. -/
theorem productScalarH1Embedding_productDivergenceH1
    (B : ProductC3H2) :
    productScalarH1Embedding (productDivergenceH1 B) =
      productDivergenceFromH2 B := by
  apply productScalarL2_ext_coeff
  intro n k
  rw [← productScalarFourierAnalysisNested_eq_inner
      (productScalarH1Embedding (productDivergenceH1 B)) k n,
    ← productScalarFourierAnalysisNested_eq_inner
      (productDivergenceFromH2 B) k n]
  rw [productScalarFourierAnalysisNested_productScalarH1Embedding,
    productDivergenceH1_coeff,
    productScalarFourierAnalysisNested_eq_inner]
  change _ = productScalarCoeffCLM n k (productDivergenceFromH2 B)
  rw [productScalarCoeffCLM_productDivergenceFromH2]
  unfold productFrequencyDivergenceCoeff
  rw [productH1ValueFourierMultiplier]
  have hw : (productH1Weight n k : ℂ) ≠ 0 := by
    exact_mod_cast (productH1Weight_pos n k).ne'
  field_simp [hw]

/-! ## Weak divergence `L²(C³) → H⁻¹` -/

/-- Fourier analysis of one scalar coordinate of a product vector field. -/
def productCoordFourierAnalysis (i : Fin 3) :
    ProductC3L2 →L[ℂ] ProductScalarFourierL2 :=
  productScalarFourierAnalysisNested.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (productCoordL2 i)

/-- Fourier analysis of the `i`-th coordinate of a product `L²` vector field returns, at axial
frequency `k` and transverse frequency `n`, the vector Fourier coefficient
`productCoeffCLM n k i V`. -/
@[simp] theorem productCoordFourierAnalysis_apply
    (i : Fin 3) (V : ProductC3L2) (k : ℤ)
    (n : TransverseFrequency) :
    productCoordFourierAnalysis i V k n = productCoeffCLM n k i V := by
  change productScalarFourierAnalysisNested (productCoordL2 i V) k n = _
  exact productScalarFourierAnalysisNested_coord_eq_productCoeffCLM V i k n

/-- The Riesz coefficient array representing distributional divergence in
the scalar `H⁻¹` anti-dual. -/
def productWeakDivergenceCoeffMap :
    ProductC3L2 →L[ℂ] ProductScalarFourierL2 :=
  (∑ j : Fin 2,
      (productScalarH1TransverseDerivCoeffMap j).comp
        (productCoordFourierAnalysis j.castSucc)) +
    productScalarH1AxialDerivCoeffMap.comp
      (productCoordFourierAnalysis (2 : Fin 3))

/-- The Riesz coefficient representing the distributional divergence at frequency `(n, k)` is the
divergence symbol `i ξ · V̂(ξ)` divided by the `H¹` weight `√(1 + |ξ|²)`. -/
theorem productWeakDivergenceCoeffMap_apply
    (V : ProductC3L2) (k : ℤ) (n : TransverseFrequency) :
    productWeakDivergenceCoeffMap V k n =
      productFrequencyDivergenceCoeff n k V /
        (productH1Weight n k : ℂ) := by
  simp only [productWeakDivergenceCoeffMap, add_apply,
    ContinuousLinearMap.comp_apply, Fin.sum_univ_two]
  change
    productScalarH1TransverseDerivCoeffMap (0 : Fin 2)
          (productCoordFourierAnalysis (0 : Fin 3) V) k n +
        productScalarH1TransverseDerivCoeffMap (1 : Fin 2)
          (productCoordFourierAnalysis (1 : Fin 3) V) k n +
      productScalarH1AxialDerivCoeffMap
          (productCoordFourierAnalysis (2 : Fin 3) V) k n = _
  rw [productScalarH1TransverseDerivCoeffMap_apply,
    productScalarH1TransverseDerivCoeffMap_apply,
    productScalarH1AxialDerivCoeffMap_apply,
    productCoordFourierAnalysis_apply,
    productCoordFourierAnalysis_apply,
    productCoordFourierAnalysis_apply]
  rw [productH1TransverseDerivFourierMultiplier,
    productH1TransverseDerivFourierMultiplier,
    productH1AxialDerivFourierMultiplier]
  unfold productFrequencyDivergenceCoeff
  simp only [Fin.sum_univ_two]
  have h0 : (0 : Fin 2).castSucc = (0 : Fin 3) := rfl
  have h1 : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
  rw [h0, h1]
  ring

/-- Distributional divergence as a bounded complex-linear map
`L²(C³) → H⁻¹`. -/
def productWeakDivergence :
    ProductC3L2 →L[ℂ] ProductScalarHMinus1 :=
  productScalarHMinus1OfCoeff.comp productWeakDivergenceCoeffMap

/-- The `H⁻¹` functional `productWeakDivergence V` acts on a test function `φ ∈ H¹` as the inner
product of `φ` with the stored Riesz coefficient array of `V`. -/
@[simp] theorem productWeakDivergence_pair
    (V : ProductC3L2) (φ : ProductScalarH1) :
    productWeakDivergence V φ =
      inner ℂ φ (productWeakDivergenceCoeffMap V) :=
  rfl

/-! ## Compatibility with the scalar energy scale -/

/-- On an `H²` field, the weak-divergence Riesz coefficient is obtained by
applying the scalar `H¹` value multiplier twice to the stored strong
divergence. -/
theorem productWeakDivergenceCoeffMap_productH2Embedding
    (B : ProductC3H2) :
    productWeakDivergenceCoeffMap (productH2Embedding B) =
      productScalarH1ValueCoeffMap
        (productScalarH1ValueCoeffMap (productDivergenceH1 B)) := by
  apply lp.ext
  funext k
  apply lp.ext
  funext n
  rw [productWeakDivergenceCoeffMap_apply,
    productScalarH1ValueCoeffMap_apply,
    productScalarH1ValueCoeffMap_apply,
    productDivergenceH1_coeff, productH1ValueFourierMultiplier]
  have hw : (productH1Weight n k : ℂ) ≠ 0 := by
    exact_mod_cast (productH1Weight_pos n k).ne'
  field_simp [hw]

/-- Moving the real positive `H¹` value multiplier between the two slots of
the nested Fourier inner product does not change the pairing. -/
theorem inner_productScalarH1ValueCoeffMap_selfAdjoint
    (a b : ProductScalarH1) :
    inner ℂ (productScalarH1ValueCoeffMap a)
        (productScalarH1ValueCoeffMap b) =
      inner ℂ a
        (productScalarH1ValueCoeffMap
          (productScalarH1ValueCoeffMap b)) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [productScalarH1ValueCoeffMap_apply, RCLike.inner_apply]
  rw [productH1ValueFourierMultiplier]
  have hr : starRingEnd ℂ (1 / (productH1Weight n k : ℂ)) =
      1 / (productH1Weight n k : ℂ) := by
    simp
  rw [map_mul, hr]
  ring

/-- Weak divergence of the `L²` embedding of an `H²` field is exactly the
canonical `H¹ → H⁻¹` inclusion of its strong divergence. -/
theorem productWeakDivergence_productH2Embedding
    (B : ProductC3H2) :
    productWeakDivergence (productH2Embedding B) =
      productScalarH1ToHMinus1 (productDivergenceH1 B) := by
  apply ContinuousLinearMap.ext
  intro φ
  rw [productWeakDivergence_pair,
    productScalarH1ToHMinus1_pair,
    productWeakDivergenceCoeffMap_productH2Embedding,
    inner_productScalarH1ValueCoeffMap_selfAdjoint]

/-- Weak divergence commutes with the product Laplacian. -/
theorem productWeakDivergence_laplacian
    (B : ProductC3H2) :
    productWeakDivergence (productLaplacianFromH2 B) =
      productScalarWeakLaplacian (productDivergenceH1 B) := by
  change productScalarHMinus1OfCoeff
      (productWeakDivergenceCoeffMap (productLaplacianFromH2 B)) =
    productScalarHMinus1OfCoeff
      (productLaplacianCoeffMap (productDivergenceH1 B))
  apply congrArg productScalarHMinus1OfCoeff
  apply lp.ext
  funext k
  apply lp.ext
  funext n
  rw [productWeakDivergenceCoeffMap_apply,
    productFrequencyDivergenceCoeff_laplacian,
    productLaplacianCoeffMap_apply, productDivergenceH1_coeff,
    productLaplacianFourierMultiplier]
  have hw : (productH1Weight n k : ℂ) ≠ 0 := by
    exact_mod_cast (productH1Weight_pos n k).ne'
  have hw2 : (productH2Weight n k : ℂ) ≠ 0 := by
    exact_mod_cast (productH2Weight_pos n k).ne'
  have hsq : (productH1Weight n k : ℂ) ^ 2 =
      (productH2Weight n k : ℂ) := by
    exact_mod_cast productH1Weight_sq n k
  field_simp [hw, hw2]
  rw [hsq]

end

end FastDynamo
