/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.ProductWeakDerivative
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Scalar `H¹`, `H⁻¹`, and the weak Laplacian on the product torus

This file supplies the scalar energy space needed when the divergence of an
`H²` vector field is tested against itself.  An element `a` of
`ProductScalarH1` stores the weighted Fourier coefficients

`a(k,n) = sqrt(1 + 4π² (|n|² + k²)) * f̂(k,n)`.

The physical `L²` field and all three first weak derivatives are obtained by
bounded Fourier multipliers followed by the product Fourier
synthesis.  The `H⁻¹` space is the continuous complex anti-dual of `H¹`:
functionals are conjugate-linear in the test function.  This convention makes
the inclusion of distributions complex-linear and matches Mathlib's
conjugate-linear-first inner product.

The weak Laplacian has stored anti-dual coefficient

`-4π² (|n|² + k²) / (1 + 4π² (|n|² + k²)) * a(k,n)`.

Its quadratic form is proved non-positive by Parseval in the nested `ℓ²`
model.  No smooth-representative or integration-by-parts assumption is used.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-! ## The scalar Fourier `H¹` model -/

/-- The positive order-one Fourier weight. -/
def productH1Weight (n : TransverseFrequency) (k : ℤ) : ℝ :=
  Real.sqrt (productH2Weight n k)

/-- Squaring the order-one Fourier weight returns the order-two weight
`1 + 4π²(|n|² + k²)`. -/
lemma productH1Weight_sq (n : TransverseFrequency) (k : ℤ) :
    productH1Weight n k ^ 2 = productH2Weight n k := by
  rw [productH1Weight, Real.sq_sqrt]
  exact (productH2Weight_pos n k).le

/-- The order-one Fourier weight is at least `1`, since the frequency energy is nonnegative. -/
lemma one_le_productH1Weight (n : TransverseFrequency) (k : ℤ) :
    1 ≤ productH1Weight n k := by
  rw [productH1Weight, ← Real.sqrt_one]
  apply Real.sqrt_le_sqrt
  rw [productH2Weight_eq_one_add_energy]
  exact le_add_of_nonneg_right (productFrequencyEnergy_nonneg n k)

/-- The order-one Fourier weight is strictly positive, so it may be divided by. -/
lemma productH1Weight_pos (n : TransverseFrequency) (k : ℤ) :
    0 < productH1Weight n k :=
  zero_lt_one.trans_le (one_le_productH1Weight n k)

/-- Scalar periodic `H¹` on the split product torus.  Its entries are the
Fourier coefficients multiplied by `productH1Weight`.

This is a Hilbert space because it is the nested Hilbert sum already used for
product Fourier analysis. -/
abbrev ProductScalarH1 := ProductScalarFourierL2

/-- Multiplier recovering the physical Fourier coefficients from the stored
`H¹` coefficients. -/
def productH1ValueFourierMultiplier
    (n : TransverseFrequency) (k : ℤ) : ℂ :=
  1 / (productH1Weight n k : ℂ)

/-- The multiplier `1 / √(1 + 4π²(|n|² + k²))` recovering physical coefficients from stored `H¹`
coefficients has modulus at most one. -/
lemma norm_productH1ValueFourierMultiplier_le_one
    (n : TransverseFrequency) (k : ℤ) :
    ‖productH1ValueFourierMultiplier n k‖ ≤ 1 := by
  rw [productH1ValueFourierMultiplier, norm_div, norm_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (productH1Weight_pos n k)]
  exact (div_le_one (productH1Weight_pos n k)).2
    (one_le_productH1Weight n k)

/-- Bounded recovery of the unweighted physical coefficient array. -/
def productScalarH1ValueCoeffMap :
    ProductScalarH1 →L[ℂ] ProductScalarFourierL2 :=
  nestedScalarMultiplier
    (fun k n ↦ productH1ValueFourierMultiplier n k)
    (fun k n ↦ norm_productH1ValueFourierMultiplier_le_one n k)

/-- Entrywise action of the recovery map: the `(k, n)` entry of the stored array is divided by
the order-one weight `productH1Weight n k`. -/
@[simp] theorem productScalarH1ValueCoeffMap_apply
    (a : ProductScalarH1) (k : ℤ) (n : TransverseFrequency) :
    productScalarH1ValueCoeffMap a k n =
      productH1ValueFourierMultiplier n k * a k n :=
  rfl

/-- The physical `L²` field represented by a scalar Fourier `H¹` element. -/
def productScalarH1Embedding : ProductScalarH1 →L[ℂ] ProductScalarL2 :=
  productScalarFourierSynthesisNested.comp productScalarH1ValueCoeffMap

/-- The physical Fourier coefficients of the `L²` field represented by an `H¹` element `a` are
the stored entries divided by the order-one weight. -/
theorem productScalarFourierAnalysisNested_productScalarH1Embedding
    (a : ProductScalarH1) (k : ℤ) (n : TransverseFrequency) :
    productScalarFourierAnalysisNested (productScalarH1Embedding a) k n =
      productH1ValueFourierMultiplier n k * a k n := by
  change productScalarFourierAnalysisNested
      (productScalarFourierSynthesisNested
        (productScalarH1ValueCoeffMap a)) k n = _
  rw [show productScalarFourierAnalysisNested
      (productScalarFourierSynthesisNested
        (productScalarH1ValueCoeffMap a)) =
      productScalarH1ValueCoeffMap a by
    exact productScalarFourierAnalysisNested_synthesis _]
  rfl

/-- The recovery map is injective, because every multiplier entry `1 / productH1Weight n k` is
nonzero. -/
theorem productScalarH1ValueCoeffMap_injective :
    Function.Injective productScalarH1ValueCoeffMap := by
  intro a b hab
  apply lp.ext
  funext k
  apply lp.ext
  funext n
  have h := congrArg (fun c : ProductScalarFourierL2 ↦ c k n) hab
  simp only [productScalarH1ValueCoeffMap_apply] at h
  have hm : productH1ValueFourierMultiplier n k ≠ 0 := by
    apply one_div_ne_zero
    exact_mod_cast (productH1Weight_pos n k).ne'
  exact (mul_right_inj' hm).mp h

/-- The physical field determines its scalar `H¹` certificate. -/
theorem productScalarH1Embedding_injective :
    Function.Injective productScalarH1Embedding := by
  intro a b hab
  apply productScalarH1ValueCoeffMap_injective
  have h := congrArg productScalarFourierAnalysisNested hab
  simpa only [productScalarH1Embedding,
    ContinuousLinearMap.comp_apply,
    productScalarFourierAnalysisNested_synthesis] using h

/-- The physical `L²` norm of the field represented by an `H¹` element equals the `ℓ²` norm of
its unweighted Fourier coefficient array, by Parseval. -/
theorem norm_productScalarH1Embedding
    (a : ProductScalarH1) :
    ‖productScalarH1Embedding a‖ = ‖productScalarH1ValueCoeffMap a‖ := by
  calc
    ‖productScalarH1Embedding a‖ =
        ‖productScalarFourierAnalysisNested
          (productScalarH1Embedding a)‖ :=
      (productScalarFourierAnalysisNested.norm_map _).symm
    _ = ‖productScalarH1ValueCoeffMap a‖ := by
      rw [show productScalarFourierAnalysisNested
          (productScalarH1Embedding a) =
          productScalarH1ValueCoeffMap a by
        change productScalarFourierAnalysisNested
          (productScalarFourierSynthesisNested
            (productScalarH1ValueCoeffMap a)) = _
        exact productScalarFourierAnalysisNested_synthesis _]

/-! ## First weak derivatives -/

/-- Transverse first-derivative multiplier acting on stored `H¹`
coefficients. -/
def productH1TransverseDerivFourierMultiplier (j : Fin 2)
    (n : TransverseFrequency) (k : ℤ) : ℂ :=
  (2 * Real.pi * Complex.I * (n j : ℂ)) /
    (productH1Weight n k : ℂ)

/-- Axial first-derivative multiplier acting on stored `H¹` coefficients. -/
def productH1AxialDerivFourierMultiplier
    (n : TransverseFrequency) (k : ℤ) : ℂ :=
  (2 * Real.pi * Complex.I * (k : ℂ)) /
    (productH1Weight n k : ℂ)

/-- Common bound behind all three first-derivative multipliers: if `r² ≤ |n|² + k²`, then
`|2πi r| / √(1 + 4π²(|n|² + k²)) ≤ 1`. -/
private lemma norm_productH1FirstDerivFourierMultiplier_le_one
    (n : TransverseFrequency) (k r : ℤ)
    (hr : (r : ℝ) ^ 2 ≤
      (∑ i, (n i : ℝ) ^ 2) + (k : ℝ) ^ 2) :
    ‖((2 * Real.pi : ℂ) * Complex.I * (r : ℂ)) /
        (productH1Weight n k : ℂ)‖ ≤ 1 := by
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
  have hx_weight : x ≤ productH1Weight n k := by
    apply Real.le_sqrt_of_sq_le
    rw [productH2Weight_eq_one_add_energy]
    linarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (productH1Weight_pos n k)]
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
  exact (div_le_one (productH1Weight_pos n k)).2 hx_weight

/-- The transverse first-derivative multiplier `2πi nⱼ / √(1 + 4π²(|n|² + k²))` has modulus at
most one, since `nⱼ²` is dominated by the full frequency energy. -/
lemma norm_productH1TransverseDerivFourierMultiplier_le_one
    (j : Fin 2) (n : TransverseFrequency) (k : ℤ) :
    ‖productH1TransverseDerivFourierMultiplier j n k‖ ≤ 1 := by
  apply norm_productH1FirstDerivFourierMultiplier_le_one
  exact le_trans (Finset.single_le_sum
      (fun i _ ↦ sq_nonneg (n i : ℝ)) (Finset.mem_univ j))
    (le_add_of_nonneg_right (sq_nonneg (k : ℝ)))

/-- The axial first-derivative multiplier `2πi k / √(1 + 4π²(|n|² + k²))` has modulus at most
one, since `k²` is dominated by the full frequency energy. -/
lemma norm_productH1AxialDerivFourierMultiplier_le_one
    (n : TransverseFrequency) (k : ℤ) :
    ‖productH1AxialDerivFourierMultiplier n k‖ ≤ 1 := by
  apply norm_productH1FirstDerivFourierMultiplier_le_one
  exact le_add_of_nonneg_left
    (Finset.sum_nonneg fun i _ ↦ sq_nonneg (n i : ℝ))

/-- Coefficient map for one transverse derivative of a scalar `H¹` field. -/
def productScalarH1TransverseDerivCoeffMap (j : Fin 2) :
    ProductScalarH1 →L[ℂ] ProductScalarFourierL2 :=
  nestedScalarMultiplier
    (fun k n ↦ productH1TransverseDerivFourierMultiplier j n k)
    (fun k n ↦
      norm_productH1TransverseDerivFourierMultiplier_le_one j n k)

/-- Coefficient map for the axial derivative of a scalar `H¹` field. -/
def productScalarH1AxialDerivCoeffMap :
    ProductScalarH1 →L[ℂ] ProductScalarFourierL2 :=
  nestedScalarMultiplier
    (fun k n ↦ productH1AxialDerivFourierMultiplier n k)
    (fun k n ↦ norm_productH1AxialDerivFourierMultiplier_le_one n k)

/-- Entrywise action of the transverse derivative coefficient map: multiplication of the stored
`(k, n)` entry by `productH1TransverseDerivFourierMultiplier j n k`. -/
@[simp] theorem productScalarH1TransverseDerivCoeffMap_apply
    (j : Fin 2) (a : ProductScalarH1) (k : ℤ)
    (n : TransverseFrequency) :
    productScalarH1TransverseDerivCoeffMap j a k n =
      productH1TransverseDerivFourierMultiplier j n k * a k n :=
  rfl

/-- Entrywise action of the axial derivative coefficient map: multiplication of the stored
`(k, n)` entry by `productH1AxialDerivFourierMultiplier n k`. -/
@[simp] theorem productScalarH1AxialDerivCoeffMap_apply
    (a : ProductScalarH1) (k : ℤ) (n : TransverseFrequency) :
    productScalarH1AxialDerivCoeffMap a k n =
      productH1AxialDerivFourierMultiplier n k * a k n :=
  rfl

/-- The `j`-th transverse weak derivative of a scalar product-torus `H¹`
field. -/
def productScalarTransverseDerivFromH1 (j : Fin 2) :
    ProductScalarH1 →L[ℂ] ProductScalarL2 :=
  productScalarFourierSynthesisNested.comp
    (productScalarH1TransverseDerivCoeffMap j)

/-- The axial weak derivative of a scalar product-torus `H¹` field. -/
def productScalarAxialDerivFromH1 :
    ProductScalarH1 →L[ℂ] ProductScalarL2 :=
  productScalarFourierSynthesisNested.comp
    productScalarH1AxialDerivCoeffMap

/-- The `j`-th transverse weak derivative of an `H¹` field has Fourier coefficients `2πi nⱼ`
times those of the field itself; this is the derivative symbol in physical normalization. -/
theorem productScalarFourierAnalysisNested_transverseDerivFromH1
    (j : Fin 2) (a : ProductScalarH1) (k : ℤ)
    (n : TransverseFrequency) :
    productScalarFourierAnalysisNested
        (productScalarTransverseDerivFromH1 j a) k n =
      (2 * Real.pi * Complex.I * (n j : ℂ)) *
        productScalarFourierAnalysisNested
          (productScalarH1Embedding a) k n := by
  rw [productScalarFourierAnalysisNested_productScalarH1Embedding]
  change productScalarFourierAnalysisNested
      (productScalarFourierSynthesisNested
        (productScalarH1TransverseDerivCoeffMap j a)) k n = _
  rw [show productScalarFourierAnalysisNested
      (productScalarFourierSynthesisNested
        (productScalarH1TransverseDerivCoeffMap j a)) =
      productScalarH1TransverseDerivCoeffMap j a by
    exact productScalarFourierAnalysisNested_synthesis _]
  rw [productScalarH1TransverseDerivCoeffMap_apply,
    productH1TransverseDerivFourierMultiplier,
    productH1ValueFourierMultiplier]
  have hw : (productH1Weight n k : ℂ) ≠ 0 := by
    exact_mod_cast (productH1Weight_pos n k).ne'
  field_simp [hw]

/-- The axial weak derivative of an `H¹` field has Fourier coefficients `2πi k` times those of
the field itself; this is the derivative symbol in physical normalization. -/
theorem productScalarFourierAnalysisNested_axialDerivFromH1
    (a : ProductScalarH1) (k : ℤ) (n : TransverseFrequency) :
    productScalarFourierAnalysisNested
        (productScalarAxialDerivFromH1 a) k n =
      (2 * Real.pi * Complex.I * (k : ℂ)) *
        productScalarFourierAnalysisNested
          (productScalarH1Embedding a) k n := by
  rw [productScalarFourierAnalysisNested_productScalarH1Embedding]
  change productScalarFourierAnalysisNested
      (productScalarFourierSynthesisNested
        (productScalarH1AxialDerivCoeffMap a)) k n = _
  rw [show productScalarFourierAnalysisNested
      (productScalarFourierSynthesisNested
        (productScalarH1AxialDerivCoeffMap a)) =
      productScalarH1AxialDerivCoeffMap a by
    exact productScalarFourierAnalysisNested_synthesis _]
  rw [productScalarH1AxialDerivCoeffMap_apply,
    productH1AxialDerivFourierMultiplier,
    productH1ValueFourierMultiplier]
  have hw : (productH1Weight n k : ℂ) ≠ 0 := by
    exact_mod_cast (productH1Weight_pos n k).ne'
  field_simp [hw]

/-! ## The anti-dual and weak Laplacian -/

/-- Scalar product-torus `H⁻¹`, represented as the continuous anti-dual of
`ProductScalarH1`. -/
abbrev ProductScalarHMinus1 := ProductScalarH1 →L⋆[ℂ] ℂ

/-- The Riesz map from a stored `H⁻¹` coefficient array to the anti-dual.
For `F`, the resulting functional sends a test coefficient array `φ` to
`⟪φ, F⟫`. -/
def productScalarHMinus1OfCoeff :
    ProductScalarFourierL2 →L[ℂ] ProductScalarHMinus1 :=
  innerSLFlip ℂ

/-- The `H⁻¹` functional attached to a coefficient array `F` sends a test element `φ` to
`⟪φ, F⟫`, hence is conjugate-linear in `φ`. -/
@[simp] theorem productScalarHMinus1OfCoeff_apply
    (F φ : ProductScalarFourierL2) :
    productScalarHMinus1OfCoeff F φ = inner ℂ φ F :=
  rfl

/-- The positive coefficient operator defining the canonical inclusion
`H¹ → H⁻¹`.  It is `J† J`, where `J` recovers the physical Fourier
coefficients. -/
def productScalarH1MassCoeffMap :
    ProductScalarH1 →L[ℂ] ProductScalarFourierL2 :=
  productScalarH1ValueCoeffMap.adjoint.comp
    productScalarH1ValueCoeffMap

/-- Canonical inclusion of scalar `H¹` into `H⁻¹`, induced by the physical
`L²` pairing. -/
def productScalarH1ToHMinus1 :
    ProductScalarH1 →L[ℂ] ProductScalarHMinus1 :=
  productScalarHMinus1OfCoeff.comp productScalarH1MassCoeffMap

/-- The canonical inclusion `H¹ → H⁻¹` pairs `d` against a test element `φ` by the physical `L²`
inner product of their unweighted Fourier coefficient arrays. -/
theorem productScalarH1ToHMinus1_pair
    (d φ : ProductScalarH1) :
    productScalarH1ToHMinus1 d φ =
      inner ℂ (productScalarH1ValueCoeffMap φ)
        (productScalarH1ValueCoeffMap d) := by
  change inner ℂ φ
      (productScalarH1ValueCoeffMap.adjoint
        (productScalarH1ValueCoeffMap d)) = _
  exact productScalarH1ValueCoeffMap.adjoint_inner_right _ _

/-- Pairing the canonical `H¹ → H⁻¹` inclusion with the same test field is
exactly its physical `L²` norm squared. -/
theorem productScalarH1ToHMinus1_pair_self
    (d : ProductScalarH1) :
    productScalarH1ToHMinus1 d d =
      (‖productScalarH1Embedding d‖ ^ 2 : ℂ) := by
  calc
    productScalarH1ToHMinus1 d d =
        inner ℂ (productScalarH1ValueCoeffMap d)
          (productScalarH1ValueCoeffMap d) :=
      productScalarH1ToHMinus1_pair d d
    _ = (‖productScalarH1ValueCoeffMap d‖ ^ 2 : ℂ) :=
      inner_self_eq_norm_sq_to_K _
    _ = (‖productScalarH1Embedding d‖ ^ 2 : ℂ) := by
      congr 1
      exact_mod_cast (norm_productScalarH1Embedding d).symm

/-- Real form of the self-pairing of the canonical inclusion: it is the squared physical `L²`
norm of the represented field. -/
theorem productScalarH1ToHMinus1_pair_self_re
    (d : ProductScalarH1) :
    (productScalarH1ToHMinus1 d d).re =
      ‖productScalarH1Embedding d‖ ^ 2 := by
  rw [productScalarH1ToHMinus1_pair_self]
  norm_cast

/-- Weak scalar Laplacian `H¹ → H⁻¹`.  The coefficient multiplier is
`-energy / (1 + energy)`. -/
def productScalarWeakLaplacian :
    ProductScalarH1 →L[ℂ] ProductScalarHMinus1 :=
  productScalarHMinus1OfCoeff.comp productLaplacianCoeffMap

/-- The weak Laplacian of `d` acts on a test element `φ` as `⟪φ, m·d⟫`, where `m` is the
multiplier `-E / (1 + E)` in the frequency energy `E = 4π²(|n|² + k²)`. -/
@[simp] theorem productScalarWeakLaplacian_pair
    (d φ : ProductScalarH1) :
    productScalarWeakLaplacian d φ =
      inner ℂ φ (productLaplacianCoeffMap d) :=
  rfl

/-- Self-pairing of the weak Laplacian, i.e. the quadratic form `⟪d, m·d⟫` used in the energy
estimate. -/
@[simp] theorem productScalarWeakLaplacian_pair_self
    (d : ProductScalarH1) :
    productScalarWeakLaplacian d d =
      inner ℂ d (productLaplacianCoeffMap d) :=
  rfl

/-- The scalar weak Laplacian is dissipative. -/
theorem re_inner_productLaplacianCoeffMap_nonpos
    (d : ProductScalarH1) :
    (inner ℂ d (productLaplacianCoeffMap d)).re ≤ 0 := by
  rw [lp.inner_eq_tsum,
    Complex.re_tsum (lp.summable_inner d (productLaplacianCoeffMap d))]
  apply tsum_nonpos
  intro k
  rw [lp.inner_eq_tsum,
    Complex.re_tsum
      (lp.summable_inner (d k) (productLaplacianCoeffMap d k))]
  apply tsum_nonpos
  intro n
  rw [productLaplacianCoeffMap_apply,
    productLaplacianFourierMultiplier]
  have hw : 0 < productH2Weight n k := productH2Weight_pos n k
  have hE : 0 ≤ productFrequencyEnergy n k :=
    productFrequencyEnergy_nonneg n k
  simp only [RCLike.inner_apply]
  have hr : (-(productFrequencyEnergy n k : ℂ) /
      (productH2Weight n k : ℂ)) =
      (((-productFrequencyEnergy n k / productH2Weight n k : ℝ) : ℂ)) := by
    push_cast
    rfl
  rw [hr]
  let z : ℂ := d k n
  change (((
    ((-productFrequencyEnergy n k / productH2Weight n k : ℝ) : ℂ) * z) *
      starRingEnd ℂ z)).re ≤ 0
  rw [mul_assoc, Complex.mul_conj]
  norm_cast
  exact mul_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hE) hw.le)
    (Complex.normSq_nonneg z)

/-- The weak Laplacian is dissipative: the real part of its quadratic form is nonpositive.  This
is the `-ε ‖∇d‖²` sign used in the auxiliary solenoidality argument of
`FastDynamo.Finish.RealSolution`, which the paper does not carry. -/
theorem productScalarWeakLaplacian_pair_self_re_nonpos
    (d : ProductScalarH1) :
    (productScalarWeakLaplacian d d).re ≤ 0 := by
  rw [productScalarWeakLaplacian_pair_self]
  exact re_inner_productLaplacianCoeffMap_nonpos d

/-! ## Energy endpoint for scalar eigen-equations -/

/-- A scalar weak eigen-equation with skew-real transport and nonnegative
diffusivity has no nonzero solution when the eigenvalue has positive real
part.  This isolates the final algebraic step of the auxiliary solenoidality argument of
`FastDynamo.Finish.RealSolution` from the weak Leibniz/vector-calculus argument that produces
the scalar equation. -/
theorem productScalarWeakEigenfunction_eq_zero
    (transport : ProductScalarHMinus1)
    (d : ProductScalarH1) (eigenvalue : ℂ) (epsilon : ℝ)
    (h_epsilon : 0 ≤ epsilon) (h_eigenvalue : 0 < eigenvalue.re)
    (h_transport : (transport d).re = 0)
    (h_equation :
      eigenvalue • productScalarH1ToHMinus1 d =
        -transport + (epsilon : ℂ) • productScalarWeakLaplacian d) :
    d = 0 := by
  have h_eval := congrArg
    (fun F : ProductScalarHMinus1 ↦ F d) h_equation
  change eigenvalue * productScalarH1ToHMinus1 d d =
      -transport d + (epsilon : ℂ) * productScalarWeakLaplacian d d at h_eval
  have h_mass_im : (productScalarH1ToHMinus1 d d).im = 0 := by
    rw [productScalarH1ToHMinus1_pair_self]
    rw [pow_two, Complex.mul_im]
    simp
  have h_re := congrArg Complex.re h_eval
  rw [Complex.mul_re, Complex.add_re, Complex.neg_re,
    Complex.mul_re] at h_re
  rw [productScalarH1ToHMinus1_pair_self_re, h_mass_im,
    h_transport] at h_re
  have h_diffusion := productScalarWeakLaplacian_pair_self_re_nonpos d
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    neg_zero, zero_add] at h_re
  have h_rhs_nonpos :
      epsilon * (productScalarWeakLaplacian d d).re ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h_epsilon h_diffusion
  have h_norm_sq_zero : ‖productScalarH1Embedding d‖ ^ 2 = 0 := by
    have h_nonneg :
        0 ≤ eigenvalue.re * ‖productScalarH1Embedding d‖ ^ 2 := by
      positivity
    have h_product_zero :
        eigenvalue.re * ‖productScalarH1Embedding d‖ ^ 2 = 0 := by
      linarith
    exact (mul_eq_zero.mp h_product_zero).resolve_left h_eigenvalue.ne'
  apply productScalarH1Embedding_injective
  have h_embedding : productScalarH1Embedding d = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp h_norm_sq_zero)
  simpa using h_embedding

end

end FastDynamo
