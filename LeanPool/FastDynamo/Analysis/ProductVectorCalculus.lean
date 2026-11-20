/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.ProductWeakDerivative

/-!
# Weak divergence on the product torus

This module constructs the first product-space vector-calculus operators needed for the auxiliary
solenoidality argument of `FastDynamo.Finish.RealSolution`.  That argument is a result of
the formalisation with no counterpart in the paper, which recovers
the axial component directly in `lem:axial-recovery` (Lemma 8.1).

* `productDivergenceFromH2` is a bounded scalar `L²` divergence of a product
  Fourier-graph `H²` vector field;
* `IsProductSolenoidal` gives the equivalent coefficientwise distributional
  divergence-free predicate for an arbitrary product `L²` vector field;
* `fixedSectorDivergence` is the exact transverse amplitude of divergence in a
  fixed axial Fourier sector;
* the coefficient calculations prove divergence--Laplacian commutation
  without an appeal to classical representatives.

Weak product rules for the lower-order induction terms require a separate
density/duality argument and are not asserted here.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-! ## Scalar coefficients and divergence -/

/-- A scalar product Fourier coefficient, with the same split monomial
convention as `productCoeffCLM`. -/
def productScalarCoeffCLM (n : TransverseFrequency) (k : ℤ) :
    ProductScalarL2 →L[ℂ] ℂ :=
  innerSL ℂ (productMonomialL2 n k)

/-- The scalar Fourier coefficient of the `i`-th coordinate of a product vector field is the
vector coefficient `productCoeffCLM n k i V`: the two conventions agree. -/
theorem productScalarCoeffCLM_coord (n : TransverseFrequency) (k : ℤ)
    (i : Fin 3) (V : ProductC3L2) :
    productScalarCoeffCLM n k (productCoordL2 i V) =
      productCoeffCLM n k i V :=
  rfl

/-- Product divergence of an `H²` vector field, valued in scalar `L²`. -/
def productDivergenceFromH2 : ProductC3H2 →L[ℂ] ProductScalarL2 :=
  (∑ j : Fin 2,
      (productCoordL2 j.castSucc).comp (productTransverseDerivFromH2 j)) +
    (productCoordL2 (2 : Fin 3)).comp productAxialDerivFromH2

/-- The divergence of an `H²` field is the sum over the two transverse directions of the matching
coordinate of `∂ⱼB`, plus the third coordinate of the axial derivative `∂₃B`. -/
theorem productDivergenceFromH2_apply (B : ProductC3H2) :
    productDivergenceFromH2 B =
      (∑ j : Fin 2,
        productCoordL2 j.castSucc (productTransverseDerivFromH2 j B)) +
      productCoordL2 (2 : Fin 3) (productAxialDerivFromH2 B) := by
  simp [productDivergenceFromH2]

/-- Exact Fourier coefficient of the product divergence. -/
theorem productScalarCoeffCLM_productDivergenceFromH2
    (B : ProductC3H2) (n : TransverseFrequency) (k : ℤ) :
    productScalarCoeffCLM n k (productDivergenceFromH2 B) =
      (∑ j : Fin 2,
        (2 * Real.pi * Complex.I * (n j : ℂ)) *
          productCoeffCLM n k j.castSucc (productH2Embedding B)) +
      (2 * Real.pi * Complex.I * (k : ℂ)) *
        productCoeffCLM n k (2 : Fin 3) (productH2Embedding B) := by
  rw [productDivergenceFromH2_apply, map_add, map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [productScalarCoeffCLM_coord,
      productCoeffCLM_productTransverseDerivFromH2]
  · rw [productScalarCoeffCLM_coord,
      productCoeffCLM_productAxialDerivFromH2]

/-- The distributional divergence symbol at one frequency as a continuous linear functional. -/
def productFrequencyDivergenceCLM (n : TransverseFrequency) (k : ℤ) :
    ProductC3L2 →L[ℂ] ℂ :=
  (∑ j : Fin 2,
    (2 * Real.pi * Complex.I * (n j : ℂ)) • productCoeffCLM n k j.castSucc) +
  (2 * Real.pi * Complex.I * (k : ℂ)) • productCoeffCLM n k (2 : Fin 3)

/-- The distributional divergence coefficient of an arbitrary product `L²`
vector field.  It is defined frequency by frequency and need not itself be an
`L²` coefficient array. -/
def productFrequencyDivergenceCoeff (n : TransverseFrequency) (k : ℤ)
    (V : ProductC3L2) : ℂ :=
  productFrequencyDivergenceCLM n k V

/-- The value of the divergence symbol in terms of the field coefficients. -/
theorem productFrequencyDivergenceCoeff_apply (n : TransverseFrequency) (k : ℤ)
    (V : ProductC3L2) :
    productFrequencyDivergenceCoeff n k V =
  (∑ j : Fin 2,
        (2 * Real.pi * Complex.I * (n j : ℂ)) *
          productCoeffCLM n k j.castSucc V) +
      (2 * Real.pi * Complex.I * (k : ℂ)) *
        productCoeffCLM n k (2 : Fin 3) V := by
  simp [productFrequencyDivergenceCoeff, productFrequencyDivergenceCLM]

/-- Coefficientwise distributional solenoidality for a product `L²` field. -/
def IsProductSolenoidal (V : ProductC3L2) : Prop :=
  ∀ n k, productFrequencyDivergenceCoeff n k V = 0

/-- For an `H²` field, vanishing of the synthesized `L²` divergence is
equivalent to coefficientwise distributional solenoidality. -/
theorem productDivergenceFromH2_eq_zero_iff (B : ProductC3H2) :
    productDivergenceFromH2 B = 0 ↔
      IsProductSolenoidal (productH2Embedding B) := by
  constructor
  · intro h n k
    have hc := congrArg (productScalarCoeffCLM n k) h
    rw [map_zero,
      productScalarCoeffCLM_productDivergenceFromH2] at hc
    rw [productFrequencyDivergenceCoeff_apply]
    exact hc
  · intro h
    apply productScalarL2_ext_coeff
    intro n k
    change productScalarCoeffCLM n k (productDivergenceFromH2 B) =
      productScalarCoeffCLM n k 0
    rw [productScalarCoeffCLM_productDivergenceFromH2,
      ← productFrequencyDivergenceCoeff_apply, h n k]
    exact (productScalarCoeffCLM n k).map_zero.symm

/-! ## Fixed axial sectors -/

/-- Divergence amplitude in one fixed axial Fourier sector. -/
def fixedSectorDivergence (K : ℤ) :
    TransverseC3H2 →L[ℂ] TransverseScalarL2 :=
  (∑ j : Fin 2,
      (transverseCoordL2 j.castSucc).comp (transverseDerivFromH2 j)) +
    (axialMultiplier K) •
      ((transverseCoordL2 (2 : Fin 3)).comp transverseH2Embedding)

/-- In the axial sector of frequency `K`, the divergence amplitude of a transverse `H²` field is
the sum of the two transverse derivative coordinates plus `2πiK` times the third coordinate. -/
theorem fixedSectorDivergence_apply (K : ℤ) (b : TransverseC3H2) :
    fixedSectorDivergence K b =
      (∑ j : Fin 2,
        transverseCoordL2 j.castSucc (transverseDerivFromH2 j b)) +
      axialMultiplier K •
        transverseCoordL2 (2 : Fin 3) (transverseH2Embedding b) := by
  simp [fixedSectorDivergence]

/-- Divergence commutes exactly with the fixed-frequency axial lift. -/
theorem productDivergenceFromH2_axialLiftH2
    (K : ℤ) (b : TransverseC3H2) :
    productDivergenceFromH2 (axialLiftH2 K b) =
      scalarAxialLiftL2 K (fixedSectorDivergence K b) := by
  rw [productDivergenceFromH2_apply, fixedSectorDivergence_apply]
  simp only [productTransverseDerivFromH2_axialLiftH2,
    axialTransverseDerivFromH2_apply,
    productCoordL2_axialLiftL2, map_add, map_sum, map_smul]
  rw [productAxialDerivFromH2_axialLiftH2,
    axialDerivFromH2_apply, map_smul, productCoordL2_axialLiftL2]
  rfl

/-! ## Distributional divergence and the Laplacian -/

/-- Distributional divergence commutes with the Fourier Laplacian. -/
theorem productFrequencyDivergenceCoeff_laplacian
    (B : ProductC3H2) (n : TransverseFrequency) (k : ℤ) :
    productFrequencyDivergenceCoeff n k (productLaplacianFromH2 B) =
      -(productFrequencyEnergy n k : ℂ) *
        productFrequencyDivergenceCoeff n k (productH2Embedding B) := by
  simp only [productFrequencyDivergenceCoeff_apply]
  simp_rw [productCoeffCLM_productLaplacianFromH2]
  simp only [Fin.sum_univ_two]
  ring

end

end FastDynamo
