/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.ProductFourier

/-!
# Fourier weak derivatives on the product torus

This module connects the weighted product `H²` graph with
all-frequency `L²` differential operators.  It constructs both
transverse first derivatives, the axial first derivative, and the full
Laplacian as bounded maps `ProductC3H2 → ProductC3L2`.

The construction divides the desired Fourier symbols by the stored positive
`H²` weight, proves that all resulting multipliers have norm at most one,
and synthesizes the resulting complete nested coefficient arrays.  The
coefficient identities give every Fourier coefficient of each derivative.
Finally, the three operators are proved to restrict to the
fixed-axial-sector operators.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-- The nonnegative full product frequency `4π² (|n|² + k²)`. -/
def productFrequencyEnergy (n : TransverseFrequency) (k : ℤ) : ℝ :=
  (2 * Real.pi) ^ 2 *
    ((∑ j, (n j : ℝ) ^ 2) + (k : ℝ) ^ 2)

/-- The full product frequency energy `4π²(|n|² + k²)` is nonnegative. -/
lemma productFrequencyEnergy_nonneg (n : TransverseFrequency) (k : ℤ) :
    0 ≤ productFrequencyEnergy n k := by
  unfold productFrequencyEnergy
  positivity

/-- The stored order-two Fourier weight is `1` plus the frequency energy. -/
lemma productH2Weight_eq_one_add_energy
    (n : TransverseFrequency) (k : ℤ) :
    productH2Weight n k = 1 + productFrequencyEnergy n k := by
  unfold productH2Weight productFrequencyEnergy
  rfl

/-- The order-two Fourier weight is strictly positive, so the symbol multipliers obtained by
dividing by it are well defined. -/
lemma productH2Weight_pos (n : TransverseFrequency) (k : ℤ) :
    0 < productH2Weight n k := by
  rw [productH2Weight_eq_one_add_energy]
  exact add_pos_of_pos_of_nonneg zero_lt_one
    (productFrequencyEnergy_nonneg n k)

/-- Multiplier producing `∂_j` from the stored weighted `H²` coefficients. -/
def productTransverseDerivFourierMultiplier (j : Fin 2)
    (n : TransverseFrequency) (k : ℤ) : ℂ :=
  (2 * Real.pi * Complex.I * (n j : ℂ)) /
    (productH2Weight n k : ℂ)

/-- Multiplier producing the axial derivative from weighted coefficients. -/
def productAxialDerivFourierMultiplier
    (n : TransverseFrequency) (k : ℤ) : ℂ :=
  (2 * Real.pi * Complex.I * (k : ℂ)) /
    (productH2Weight n k : ℂ)

/-- Multiplier producing the full product Laplacian from weighted coefficients. -/
def productLaplacianFourierMultiplier
    (n : TransverseFrequency) (k : ℤ) : ℂ :=
  -(productFrequencyEnergy n k : ℂ) /
    (productH2Weight n k : ℂ)

/-- Common bound behind all three first-order symbols: whenever `r² ≤ |n|² + k²`, the multiplier
`2πi r / (1 + 4π²(|n|² + k²))` has modulus at most one. -/
private lemma norm_productFirstDerivMultiplier_le_one
    (n : TransverseFrequency) (k r : ℤ)
    (hr : (r : ℝ) ^ 2 ≤
      (∑ i, (n i : ℝ) ^ 2) + (k : ℝ) ^ 2) :
    ‖((2 * Real.pi : ℂ) * Complex.I * (r : ℂ)) /
        (productH2Weight n k : ℂ)‖ ≤ 1 := by
  let x : ℝ := 2 * Real.pi * |(r : ℝ)|
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx_sq : x ^ 2 ≤ productFrequencyEnergy n k := by
    dsimp [x, productFrequencyEnergy]
    have hfac : 0 ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
    have hm := mul_le_mul_of_nonneg_left hr hfac
    calc
      (2 * Real.pi * |(r : ℝ)|) ^ 2 =
          (2 * Real.pi) ^ 2 * (r : ℝ) ^ 2 := by
        rw [mul_pow, sq_abs]
      _ ≤ (2 * Real.pi) ^ 2 *
          ((∑ i, (n i : ℝ) ^ 2) + (k : ℝ) ^ 2) := hm
  have hx_weight : x ≤ productH2Weight n k := by
    have hxx : x ≤ 1 + x ^ 2 := by
      nlinarith [sq_nonneg (x - 1)]
    rw [productH2Weight_eq_one_add_energy]
    linarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (productH2Weight_pos n k)]
  have hnum :
      ‖(2 * Real.pi : ℂ) * Complex.I * (r : ℂ)‖ = x := by
    calc
      ‖(2 * Real.pi : ℂ) * Complex.I * (r : ℂ)‖ =
          ‖(2 * Real.pi : ℂ)‖ * ‖Complex.I‖ * ‖(r : ℂ)‖ := by
        rw [norm_mul, norm_mul]
      _ = 2 * Real.pi * |(r : ℝ)| := by
        simp [abs_of_pos Real.pi_pos]
      _ = x := rfl
  rw [hnum]
  exact (div_le_one (productH2Weight_pos n k)).2 hx_weight

/-- The transverse derivative multiplier `2πi nⱼ / (1 + 4π²(|n|² + k²))` has modulus at most
one, since `nⱼ²` is dominated by the full frequency energy. -/
lemma norm_productTransverseDerivFourierMultiplier_le_one
    (j : Fin 2) (n : TransverseFrequency) (k : ℤ) :
    ‖productTransverseDerivFourierMultiplier j n k‖ ≤ 1 := by
  apply norm_productFirstDerivMultiplier_le_one
  exact le_trans (Finset.single_le_sum
      (fun i _ => sq_nonneg (n i : ℝ)) (Finset.mem_univ j))
    (le_add_of_nonneg_right (sq_nonneg (k : ℝ)))

/-- The axial derivative multiplier `2πi k / (1 + 4π²(|n|² + k²))` has modulus at most one,
since `k²` is dominated by the full frequency energy. -/
lemma norm_productAxialDerivFourierMultiplier_le_one
    (n : TransverseFrequency) (k : ℤ) :
    ‖productAxialDerivFourierMultiplier n k‖ ≤ 1 := by
  apply norm_productFirstDerivMultiplier_le_one
  exact le_add_of_nonneg_left
    (Finset.sum_nonneg fun i _ => sq_nonneg (n i : ℝ))

/-- The Laplacian multiplier `-E / (1 + E)`, with `E` the frequency energy, has modulus at most
one. -/
lemma norm_productLaplacianFourierMultiplier_le_one
    (n : TransverseFrequency) (k : ℤ) :
    ‖productLaplacianFourierMultiplier n k‖ ≤ 1 := by
  rw [productLaplacianFourierMultiplier, norm_div, norm_neg,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (productFrequencyEnergy_nonneg n k),
    abs_of_pos (productH2Weight_pos n k)]
  apply (div_le_one (productH2Weight_pos n k)).2
  rw [productH2Weight_eq_one_add_energy]
  linarith

/-- Apply a uniformly bounded scalar multiplier to one transverse Fourier row. -/
def scalarRowMultiplier
    (m : TransverseFrequency → ℂ)
    (hm : ∀ n, ‖m n‖ ≤ 1) :
    TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2 :=
  lp.mapCLM 2
    (fun n => (ContinuousLinearMap.lsmul ℂ ℂ) (m n))
    zero_le_one
    (fun n => (ContinuousLinearMap.opNorm_lsmul_apply_le
      (E := ℂ) (m n)).trans (hm n))

/-- A row multiplier built from entrywise multipliers of modulus at most one is a contraction on
the transverse coefficient row. -/
lemma norm_scalarRowMultiplier_le
    (m : TransverseFrequency → ℂ)
    (hm : ∀ n, ‖m n‖ ≤ 1) :
    ‖scalarRowMultiplier m hm‖ ≤ 1 :=
  lp.norm_mapCLM_le 2 _ zero_le_one
    (fun n => (ContinuousLinearMap.opNorm_lsmul_apply_le
      (E := ℂ) (m n)).trans (hm n))

/-- Apply uniformly bounded scalar multipliers to all nested product Fourier coefficients. -/
def nestedScalarMultiplier
    (m : ℤ → TransverseFrequency → ℂ)
    (hm : ∀ k n, ‖m k n‖ ≤ 1) :
    ProductScalarFourierL2 →L[ℂ] ProductScalarFourierL2 :=
  lp.mapCLM 2
    (fun k => scalarRowMultiplier (m k) (hm k))
    zero_le_one
    (fun k => norm_scalarRowMultiplier_le (m k) (hm k))

/-- The nested multiplier acts entrywise: the `(k, n)` entry of the image is `m k n` times the
`(k, n)` entry of the input array. -/
@[simp] theorem nestedScalarMultiplier_apply
    (m : ℤ → TransverseFrequency → ℂ)
    (hm : ∀ k n, ‖m k n‖ ≤ 1)
    (a : ProductScalarFourierL2) (k : ℤ) (n : TransverseFrequency) :
    nestedScalarMultiplier m hm a k n = m k n * a k n :=
  rfl

/-- Bounded nested coefficient map for one transverse derivative. -/
def productTransverseDerivCoeffMap (j : Fin 2) :
    ProductScalarFourierL2 →L[ℂ] ProductScalarFourierL2 :=
  nestedScalarMultiplier
    (fun k n => productTransverseDerivFourierMultiplier j n k)
    (fun k n => norm_productTransverseDerivFourierMultiplier_le_one j n k)

/-- Bounded nested coefficient map for the axial derivative. -/
def productAxialDerivCoeffMap :
    ProductScalarFourierL2 →L[ℂ] ProductScalarFourierL2 :=
  nestedScalarMultiplier
    (fun k n => productAxialDerivFourierMultiplier n k)
    (fun k n => norm_productAxialDerivFourierMultiplier_le_one n k)

/-- Bounded nested coefficient map for the full Laplacian. -/
def productLaplacianCoeffMap :
    ProductScalarFourierL2 →L[ℂ] ProductScalarFourierL2 :=
  nestedScalarMultiplier
    (fun k n => productLaplacianFourierMultiplier n k)
    (fun k n => norm_productLaplacianFourierMultiplier_le_one n k)

/-- Entrywise action of the transverse derivative coefficient map: multiplication of the `(k, n)`
entry by `productTransverseDerivFourierMultiplier j n k`. -/
@[simp] theorem productTransverseDerivCoeffMap_apply
    (j : Fin 2) (a : ProductScalarFourierL2)
    (k : ℤ) (n : TransverseFrequency) :
    productTransverseDerivCoeffMap j a k n =
      productTransverseDerivFourierMultiplier j n k * a k n :=
  rfl

/-- Entrywise action of the axial derivative coefficient map: multiplication of the `(k, n)`
entry by `productAxialDerivFourierMultiplier n k`. -/
@[simp] theorem productAxialDerivCoeffMap_apply
    (a : ProductScalarFourierL2) (k : ℤ) (n : TransverseFrequency) :
    productAxialDerivCoeffMap a k n =
      productAxialDerivFourierMultiplier n k * a k n :=
  rfl

/-- Entrywise action of the Laplacian coefficient map: multiplication of the `(k, n)` entry by
`productLaplacianFourierMultiplier n k`. -/
@[simp] theorem productLaplacianCoeffMap_apply
    (a : ProductScalarFourierL2) (k : ℤ) (n : TransverseFrequency) :
    productLaplacianCoeffMap a k n =
      productLaplacianFourierMultiplier n k * a k n :=
  rfl

/-! Coordinatewise product synthesis. -/

/-- Three scalar product-torus `L²` fields with their Euclidean product norm. -/
abbrev ProductC3CoordinateL2 :=
  PiLp 2 (fun _ : Fin 3 => ProductScalarL2)

/-- Insert a scalar product-torus `L²` field into one complex vector coordinate. -/
def scalarToC3CoordProductL2 (i : Fin 3) :
    ProductScalarL2 →L[ℂ] ProductC3L2 :=
  (scalarToC3Point i).compLpL 2 productMeasure

/-- Assemble scalar coordinate fields into a `C3`-valued product `L²` field. -/
def productC3OfCoordsL2 :
    ProductC3CoordinateL2 →L[ℂ] ProductC3L2 :=
  ∑ i : Fin 3, (scalarToC3CoordProductL2 i).comp
    (PiLp.proj 2 (fun _ : Fin 3 => ProductScalarL2) i)

/-- Assembling three scalar fields into a `C³`-valued field and then reading off the `j`-th
coordinate returns the `j`-th input field. -/
theorem productCoordL2_productC3OfCoordsL2
    (j : Fin 3) (a : ProductC3CoordinateL2) :
    productCoordL2 j (productC3OfCoordsL2 a) = a j := by
  rw [show productC3OfCoordsL2 a =
      ∑ i : Fin 3, scalarToC3CoordProductL2 i (a i) by
    simp [productC3OfCoordsL2]]
  rw [map_sum]
  ext1
  have hterm : ∀ i : Fin 3,
      ((productCoordL2 j (scalarToC3CoordProductL2 i (a i)) :
          ProductScalarL2) : ProductTorus3 → ℂ) =ᵐ[productMeasure]
        fun x => if i = j then (a i : ProductTorus3 → ℂ) x else 0 := by
    intro i
    have hsingle := (scalarToC3Point i).coeFn_compLpL (a i)
    have hproj := (EuclideanSpace.proj (𝕜 := ℂ) j).coeFn_compLpL
      (scalarToC3CoordProductL2 i (a i))
    filter_upwards [hsingle, hproj] with x hs hp
    change (((EuclideanSpace.proj (𝕜 := ℂ) j).compLp
      (scalarToC3CoordProductL2 i (a i)) : ProductScalarL2) :
        ProductTorus3 → ℂ) x = _
    change (((EuclideanSpace.proj (𝕜 := ℂ) j).compLp
      (scalarToC3CoordProductL2 i (a i)) : ProductScalarL2) :
        ProductTorus3 → ℂ) x = _ at hp
    change (((scalarToC3Point i).compLp (a i) : ProductC3L2) :
      ProductTorus3 → C3) x = _ at hs
    rw [hp]
    change (EuclideanSpace.proj (𝕜 := ℂ) j)
      ((((scalarToC3Point i).compLp (a i) : ProductC3L2) :
        ProductTorus3 → C3) x) = _
    rw [hs]
    simp [scalarToC3Point, eq_comm]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun i : Fin 3 => productCoordL2 j
      (scalarToC3CoordProductL2 i (a i))),
      ae_all_iff.2 hterm] with x hx ht
  rw [hx]
  calc
    (∑ i : Fin 3,
        ((productCoordL2 j (scalarToC3CoordProductL2 i (a i)) :
          ProductScalarL2) : ProductTorus3 → ℂ) x) =
        ∑ i : Fin 3, if i = j then
          (a i : ProductTorus3 → ℂ) x else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ht i
    _ = (a j : ProductTorus3 → ℂ) x := by simp

/-- Apply a scalar synthesis map coordinatewise to a weighted vector array. -/
def mapWeightedProductCoords
    (T : ProductScalarFourierL2 →L[ℂ] ProductScalarL2) :
    WeightedProductC3Coeffs →L[ℂ] ProductC3CoordinateL2 :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 3 => ProductScalarL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => T.comp
      (PiLp.proj 2 (fun _ : Fin 3 => ProductScalarFourierL2) i))

/-- Applying a scalar coefficient-to-field map coordinatewise acts on the `i`-th component of a
three-component coefficient array by that map. -/
@[simp] theorem mapWeightedProductCoords_apply
    (T : ProductScalarFourierL2 →L[ℂ] ProductScalarL2)
    (a : WeightedProductC3Coeffs) (i : Fin 3) :
    mapWeightedProductCoords T a i = T (a i) :=
  rfl

/-- Scalar nested Fourier analysis of the `i`-th coordinate of a vector field agrees with the
vector Fourier coefficient functional `productCoeffCLM n k i`. -/
theorem productScalarFourierAnalysisNested_coord_eq_productCoeffCLM
    (V : ProductC3L2) (i : Fin 3) (k : ℤ)
    (n : TransverseFrequency) :
    productScalarFourierAnalysisNested (productCoordL2 i V) k n =
      productCoeffCLM n k i V := by
  rw [productScalarFourierAnalysisNested_eq_inner]
  rfl

/-- Synthesizing a three-component nested coefficient array coordinatewise produces the field
whose vector Fourier coefficients are exactly the entries of that array. -/
theorem productCoeffCLM_productC3OfCoordsL2_synthesis
    (a : WeightedProductC3Coeffs) (n : TransverseFrequency)
    (k : ℤ) (i : Fin 3) :
    productCoeffCLM n k i
      (productC3OfCoordsL2
        (mapWeightedProductCoords productScalarFourierSynthesisNested a)) =
      a i k n := by
  rw [← productScalarFourierAnalysisNested_coord_eq_productCoeffCLM,
    productCoordL2_productC3OfCoordsL2,
    mapWeightedProductCoords_apply]
  exact congrArg (fun x : ProductScalarFourierL2 => x k n)
    (productScalarFourierAnalysisNested_synthesis (a i))

/-- The `j`-th all-frequency transverse weak derivative as a bounded map. -/
def productTransverseDerivFromH2 (j : Fin 2) :
    ProductC3H2 →L[ℂ] ProductC3L2 :=
  productC3OfCoordsL2.comp
    ((mapWeightedProductCoords
      (productScalarFourierSynthesisNested.comp
        (productTransverseDerivCoeffMap j))).comp
      productH2WeightedCoeffs)

/-- The all-frequency axial weak derivative as a bounded map. -/
def productAxialDerivFromH2 :
    ProductC3H2 →L[ℂ] ProductC3L2 :=
  productC3OfCoordsL2.comp
    ((mapWeightedProductCoords
      (productScalarFourierSynthesisNested.comp
        productAxialDerivCoeffMap)).comp
      productH2WeightedCoeffs)

/-- The all-frequency product weak Laplacian as a bounded map. -/
def productLaplacianFromH2 :
    ProductC3H2 →L[ℂ] ProductC3L2 :=
  productC3OfCoordsL2.comp
    ((mapWeightedProductCoords
      (productScalarFourierSynthesisNested.comp
        productLaplacianCoeffMap)).comp
      productH2WeightedCoeffs)

/-- Exact Fourier symbol of the `j`-th transverse weak derivative: the coefficient at `(n, k, i)`
is `2πi nⱼ` times the corresponding coefficient of the field itself. -/
theorem productCoeffCLM_productTransverseDerivFromH2
    (j : Fin 2) (V : ProductC3H2)
    (n : TransverseFrequency) (k : ℤ) (i : Fin 3) :
    productCoeffCLM n k i (productTransverseDerivFromH2 j V) =
      (2 * Real.pi * Complex.I * (n j : ℂ)) *
        productCoeffCLM n k i (productH2Embedding V) := by
  change productCoeffCLM n k i
    (productC3OfCoordsL2
      (mapWeightedProductCoords
        (productScalarFourierSynthesisNested.comp
          (productTransverseDerivCoeffMap j))
        (productH2WeightedCoeffs V))) = _
  rw [← productScalarFourierAnalysisNested_coord_eq_productCoeffCLM,
    productCoordL2_productC3OfCoordsL2,
    mapWeightedProductCoords_apply, ContinuousLinearMap.comp_apply]
  change productScalarFourierAnalysisNested
    (productScalarFourierSynthesisNested
      (productTransverseDerivCoeffMap j (productH2WeightedCoeffs V i))) k n = _
  rw [show productScalarFourierAnalysisNested
      (productScalarFourierSynthesisNested
        (productTransverseDerivCoeffMap j (productH2WeightedCoeffs V i))) k n =
      productTransverseDerivCoeffMap j (productH2WeightedCoeffs V i) k n by
    exact congrArg (fun x : ProductScalarFourierL2 => x k n)
      (productScalarFourierAnalysisNested_synthesis _),
    productTransverseDerivCoeffMap_apply,
    productH2WeightedCoeffs_apply,
    productTransverseDerivFourierMultiplier]
  have hw : (productH2Weight n k : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (productH2Weight_pos n k))
  field_simp [hw]

/-- Exact Fourier symbol of the axial weak derivative: the coefficient at `(n, k, i)` is `2πi k`
times the corresponding coefficient of the field itself. -/
theorem productCoeffCLM_productAxialDerivFromH2
    (V : ProductC3H2) (n : TransverseFrequency)
    (k : ℤ) (i : Fin 3) :
    productCoeffCLM n k i (productAxialDerivFromH2 V) =
      (2 * Real.pi * Complex.I * (k : ℂ)) *
        productCoeffCLM n k i (productH2Embedding V) := by
  change productCoeffCLM n k i
    (productC3OfCoordsL2
      (mapWeightedProductCoords
        (productScalarFourierSynthesisNested.comp
          productAxialDerivCoeffMap)
        (productH2WeightedCoeffs V))) = _
  rw [← productScalarFourierAnalysisNested_coord_eq_productCoeffCLM,
    productCoordL2_productC3OfCoordsL2,
    mapWeightedProductCoords_apply, ContinuousLinearMap.comp_apply]
  change productScalarFourierAnalysisNested
    (productScalarFourierSynthesisNested
      (productAxialDerivCoeffMap (productH2WeightedCoeffs V i))) k n = _
  rw [show productScalarFourierAnalysisNested
      (productScalarFourierSynthesisNested
        (productAxialDerivCoeffMap (productH2WeightedCoeffs V i))) k n =
      productAxialDerivCoeffMap (productH2WeightedCoeffs V i) k n by
    exact congrArg (fun x : ProductScalarFourierL2 => x k n)
      (productScalarFourierAnalysisNested_synthesis _),
    productAxialDerivCoeffMap_apply,
    productH2WeightedCoeffs_apply,
    productAxialDerivFourierMultiplier]
  have hw : (productH2Weight n k : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (productH2Weight_pos n k))
  field_simp [hw]

/-- Exact Fourier symbol of the weak Laplacian: the coefficient at `(n, k, i)` is
`-4π²(|n|² + k²)` times the corresponding coefficient of the field itself. -/
theorem productCoeffCLM_productLaplacianFromH2
    (V : ProductC3H2) (n : TransverseFrequency)
    (k : ℤ) (i : Fin 3) :
    productCoeffCLM n k i (productLaplacianFromH2 V) =
      -(productFrequencyEnergy n k : ℂ) *
        productCoeffCLM n k i (productH2Embedding V) := by
  change productCoeffCLM n k i
    (productC3OfCoordsL2
      (mapWeightedProductCoords
        (productScalarFourierSynthesisNested.comp
          productLaplacianCoeffMap)
        (productH2WeightedCoeffs V))) = _
  rw [← productScalarFourierAnalysisNested_coord_eq_productCoeffCLM,
    productCoordL2_productC3OfCoordsL2,
    mapWeightedProductCoords_apply, ContinuousLinearMap.comp_apply]
  change productScalarFourierAnalysisNested
    (productScalarFourierSynthesisNested
      (productLaplacianCoeffMap (productH2WeightedCoeffs V i))) k n = _
  rw [show productScalarFourierAnalysisNested
      (productScalarFourierSynthesisNested
        (productLaplacianCoeffMap (productH2WeightedCoeffs V i))) k n =
      productLaplacianCoeffMap (productH2WeightedCoeffs V i) k n by
    exact congrArg (fun x : ProductScalarFourierL2 => x k n)
      (productScalarFourierAnalysisNested_synthesis _),
    productLaplacianCoeffMap_apply,
    productH2WeightedCoeffs_apply,
    productLaplacianFourierMultiplier]
  have hw : (productH2Weight n k : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (productH2Weight_pos n k))
  field_simp [hw]

/-- The all-frequency transverse derivative restricts to the fixed-axial-sector transverse
derivative: it commutes with the axial lift `b ↦ e^{2πiKx₃}b`. -/
theorem productTransverseDerivFromH2_axialLiftH2
    (j : Fin 2) (K : ℤ) (b : TransverseC3H2) :
    productTransverseDerivFromH2 j (axialLiftH2 K b) =
      axialTransverseDerivFromH2 K j b := by
  apply productC3L2_ext_coeff
  intro n k i
  rw [productCoeffCLM_productTransverseDerivFromH2,
    productCoeffCLM_productH2Embedding_axialLiftH2,
    axialTransverseDerivFromH2_apply,
    productCoeffCLM_axialLiftL2]
  by_cases hk : k = K
  · subst k
    simp only [ite_true]
    rw [transverseCoeffCLM_transverseDerivFromH2]
  · simp [hk]

/-- On a field of pure axial frequency `K`, the all-frequency axial derivative agrees with the
fixed-sector axial derivative, i.e. with multiplication by `2πiK`. -/
theorem productAxialDerivFromH2_axialLiftH2
    (K : ℤ) (b : TransverseC3H2) :
    productAxialDerivFromH2 (axialLiftH2 K b) =
      axialDerivFromH2 K b := by
  apply productC3L2_ext_coeff
  intro n k i
  rw [productCoeffCLM_productAxialDerivFromH2,
    productCoeffCLM_productH2Embedding_axialLiftH2,
    axialDerivFromH2_apply, map_smul,
    productCoeffCLM_axialLiftL2]
  by_cases hk : k = K
  · subst k
    simp only [ite_true]
    rfl
  · simp [hk]

/-- On a field of pure axial frequency `K`, the all-frequency Laplacian agrees with the
fixed-sector operator `Δ_⊥ - 4π²K²`. -/
theorem productLaplacianFromH2_axialLiftH2
    (K : ℤ) (b : TransverseC3H2) :
    productLaplacianFromH2 (axialLiftH2 K b) =
      fixedAxialLaplacianFromH2 K b := by
  apply productC3L2_ext_coeff
  intro n k i
  rw [productCoeffCLM_productLaplacianFromH2,
    productCoeffCLM_productH2Embedding_axialLiftH2,
    fixedAxialLaplacianFromH2_apply,
    productCoeffCLM_axialLiftL2]
  by_cases hk : k = K
  · subst k
    simp only [ite_true]
    rw [map_sub, map_smul,
      transverseCoeffCLM_transverseLaplacianFromH2]
    have henergy : (productFrequencyEnergy n K : ℂ) =
        (transverseFrequencyEnergy n : ℂ) +
          (2 * Real.pi * K : ℂ) ^ 2 := by
      unfold productFrequencyEnergy transverseFrequencyEnergy
      push_cast
      ring
    rw [henergy]
    ring
  · simp [hk]

end

end FastDynamo
