/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.PeriodicSecondOrderCutoffs

/-!
# Fourier-summable periodic `H²` cutoff multipliers

The two-resolvent construction of §7.1 (`eq:parametrix-cutoff-bounds`)
localizes periodic second-order fields by multiplying them with smooth cutoffs.  This module
constructs that multiplication on the repository's transverse Fourier `H²` graph without
invoking any unproved Sobolev multiplication theorem: first for finite scalar Fourier
polynomials, then for absolutely summable Fourier series.

A finite scalar Fourier polynomial is an `L∞` multiplier whose value, first derivatives, and
Laplacian are computed on every mode; the weighted coefficient certificate of the product is
synthesized from `χh - Δ(χh)`, and the computed Laplacian identity places that pair in the closed
`H²` graph.  For the limit, each frequency contributes a Banach-space package bundling the value,
both first derivatives, the Laplacian, and the bounded `H²` multiplier of its Fourier monomial;
absolute summability of those package norms is exactly strong enough to sum all four pieces
simultaneously.  The two Leibniz rules are not postulated for the limit: they are closed linear
identities, obtained by applying continuous linear defect maps to the convergent series.

The resulting coefficient condition is operator-adapted, and discharging it needs a
polynomial bound on `secondOrderFourierWeight`; that estimate is not part of the constructions
below, and is proved in `TransverseSmoothBumpH2CutoffConcrete`.

## Contents

* Finite Fourier cutoffs preserve the transverse `H²` graph: polynomial coefficients and their
  bounded representatives, Fourier coefficients under a monomial shift, the frequency algebra
  behind the two product rules, bounded product candidates on the `H²` graph, the computed
  first- and second-order Leibniz identities, closing the Fourier graph, and the concrete
  periodic second-order cutoff.
* Fourier-summable periodic `H²` cutoff multipliers: the simultaneous Banach-space Fourier
  package, closed Leibniz-defect maps, and the completed periodic cutoff.
-/

@[expose] public section

/-!
## Finite Fourier cutoffs preserve the transverse `H²` graph

This part constructs periodic second-order cutoff multiplication for
finite Fourier polynomials.  A finite scalar Fourier polynomial defines an `L∞`
multiplier.  We compute its value, first derivatives, and Laplacian on every
Fourier mode, prove the product rules, and construct an actual bounded map on
the repository's Fourier-graph `TransverseC3H2` domain.

The construction avoids any unproved Sobolev multiplication theorem.  The
weighted coefficient certificate of the product is synthesized from
`χh - Δ(χh)`; the computed Laplacian coefficient identity proves that this
pair belongs to the closed `H²` graph.
-/

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TransverseH2CutoffMultiplier

open PeriodicSecondOrderCutoffs

/-! ## Polynomial coefficients and their bounded representatives -/

/-- Continuous evaluation of a finite trigonometric polynomial. -/
def polynomialContinuous :
    TransverseTrigPolynomial →ₗ[ℂ] C(TransverseTorus, ℂ) :=
  Finsupp.linearCombination ℂ fun n : TransverseFrequency ↦
    UnitAddTorus.mFourier n

/-- A one-term trigonometric polynomial evaluates to the continuous function `c · e_n`. -/
@[simp] theorem polynomialContinuous_single
    (n : TransverseFrequency) (c : ℂ) :
    polynomialContinuous (Finsupp.single n c) =
      c • UnitAddTorus.mFourier n := by
  exact Finsupp.linearCombination_single ℂ c n

/-- A finite scalar Fourier polynomial as a quotient-level `L∞` function. -/
def polynomialLInf (p : TransverseTrigPolynomial) :
    TransverseScalarLInf :=
  (polynomialContinuous p).toLp ∞ transverseMeasure ℂ

/-- The `L∞` class of a trigonometric polynomial is represented almost everywhere by its
continuous evaluation. -/
theorem polynomialLInf_coe_ae (p : TransverseTrigPolynomial) :
    (polynomialLInf p : TransverseTorus → ℂ) =ᵐ[transverseMeasure]
      polynomialContinuous p := by
  exact ContinuousMap.coeFn_toLp transverseMeasure
    (polynomialContinuous p)

/-- The zero polynomial gives the zero `L∞` coefficient. -/
@[simp] theorem polynomialLInf_zero :
    polynomialLInf (0 : TransverseTrigPolynomial) = 0 := by
  apply Lp.ext
  filter_upwards [polynomialLInf_coe_ae
      (0 : TransverseTrigPolynomial),
    Lp.coeFn_zero ℂ ∞ transverseMeasure] with x hp hz
  rw [hp, hz]
  simp [polynomialContinuous]

/-- Passing from finitely supported Fourier coefficients to the `L∞` class is additive. -/
theorem polynomialLInf_add
    (p q : TransverseTrigPolynomial) :
    polynomialLInf (p + q) = polynomialLInf p + polynomialLInf q := by
  apply Lp.ext
  filter_upwards [polynomialLInf_coe_ae (p + q),
    polynomialLInf_coe_ae p, polynomialLInf_coe_ae q,
    Lp.coeFn_add (polynomialLInf p) (polynomialLInf q)]
      with x hpq hp hq hadd
  rw [hpq, hadd]
  change polynomialContinuous (p + q) x =
    polynomialLInf p x + polynomialLInf q x
  rw [hp, hq, map_add]
  rfl

/-- Passing from finitely supported Fourier coefficients to the `L∞` class is homogeneous in the
complex scalar. -/
theorem polynomialLInf_smul
    (c : ℂ) (p : TransverseTrigPolynomial) :
    polynomialLInf (c • p) = c • polynomialLInf p := by
  apply Lp.ext
  filter_upwards [polynomialLInf_coe_ae (c • p),
    polynomialLInf_coe_ae p, Lp.coeFn_smul c (polynomialLInf p)]
      with x hcp hp hsmul
  rw [hcp, hsmul]
  change polynomialContinuous (c • p) x = c * polynomialLInf p x
  rw [hp, map_smul]
  rfl

/-- The `j`-th derivative polynomial, with coefficient
`(2π i n_j) p_n`. -/
def polynomialDeriv (j : Fin 2) :
    TransverseTrigPolynomial →ₗ[ℂ] TransverseTrigPolynomial :=
  transverseTrigPolynomialDeriv j

/-- The Laplacian polynomial, with coefficient `-4π²|n|² p_n`. -/
def polynomialLaplacian :
    TransverseTrigPolynomial →ₗ[ℂ] TransverseTrigPolynomial :=
  Finsupp.linearCombination ℂ fun n : TransverseFrequency ↦
    -(transverseFrequencyEnergy n : ℂ) •
      Finsupp.single n (1 : ℂ)

/-- Coefficientwise differentiation of a one-term polynomial multiplies its single coefficient by
the symbol `2πi nⱼ`, leaving the frequency unchanged. -/
@[simp] theorem polynomialDeriv_single
    (j : Fin 2) (n : TransverseFrequency) (c : ℂ) :
    polynomialDeriv j (Finsupp.single n c) =
      Finsupp.single n (transverseFourierDerivMultiplier j n * c) := by
  rw [polynomialDeriv, transverseTrigPolynomialDeriv_single]
  ext q
  simp [Finsupp.single_apply, smul_eq_mul]
  split_ifs with h
  · subst q
    ring
  · simp

/-- The coefficientwise Laplacian of a one-term polynomial multiplies its single coefficient by
`-4π²|n|²`, leaving the frequency unchanged. -/
@[simp] theorem polynomialLaplacian_single
    (n : TransverseFrequency) (c : ℂ) :
    polynomialLaplacian (Finsupp.single n c) =
      Finsupp.single n (-(transverseFrequencyEnergy n : ℂ) * c) := by
  rw [polynomialLaplacian, Finsupp.linearCombination_single]
  ext q
  simp [Finsupp.single_apply, smul_eq_mul]
  split_ifs with h
  · subst q
    ring
  · simp

/-- The unit-amplitude Fourier monomial as an `L∞` coefficient. -/
def monomialLInf (n : TransverseFrequency) : TransverseScalarLInf :=
  polynomialLInf (Finsupp.single n (1 : ℂ))

/-- The unit-amplitude monomial coefficient is represented almost everywhere by the continuous
character `y ↦ e^{2πi n·y}`. -/
theorem monomialLInf_coe_ae (n : TransverseFrequency) :
    (monomialLInf n : TransverseTorus → ℂ) =ᵐ[transverseMeasure]
      UnitAddTorus.mFourier n := by
  filter_upwards [polynomialLInf_coe_ae
    (Finsupp.single n (1 : ℂ))] with x hx
  change polynomialLInf (Finsupp.single n (1 : ℂ)) x = _
  rw [hx, polynomialContinuous_single]
  simp

/-- The `L∞` coefficient of a one-term polynomial is the scalar multiple `c • monomialLInf n`. -/
theorem polynomialLInf_single
    (n : TransverseFrequency) (c : ℂ) :
    polynomialLInf (Finsupp.single n c) = c • monomialLInf n := by
  rw [show Finsupp.single n c =
      c • Finsupp.single n (1 : ℂ) by
    ext q
    simp [Finsupp.single_apply]]
  exact polynomialLInf_smul c _

/-! ## Fourier coefficients under a monomial shift -/

/-- Multiplying by the monomial `e_m` shifts Fourier coefficients: the `q`-th coefficient of
`e_m f` is the `(q - m)`-th coefficient of `f`. -/
theorem transverseScalarCoeff_monomialMul
    (m q : TransverseFrequency) (f : TransverseScalarL2) :
    transverseScalarCoeffCLM q
        (scalarMulTransverse (monomialLInf m) f) =
      transverseScalarCoeffCLM (q - m) f := by
  rw [transverseScalarCoeffCLM_eq_inner,
    transverseScalarCoeffCLM_eq_inner,
    MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [transverseMonomialL2_coe_ae q,
    transverseMonomialL2_coe_ae (q - m),
    scalarMulTransverse_coe_ae (monomialLInf m) f,
    monomialLInf_coe_ae m] with x hq hqm hmul hm
  rw [hq, hqm, hmul, hm]
  simp only [RCLike.inner_apply]
  rw [← UnitAddTorus.mFourier_neg (n := q) (x := x),
    ← UnitAddTorus.mFourier_neg (n := q - m) (x := x)]
  rw [show (UnitAddTorus.mFourier m x * f x) *
      UnitAddTorus.mFourier (-q) x =
      f x * (UnitAddTorus.mFourier m x *
        UnitAddTorus.mFourier (-q) x) by ring,
    ← UnitAddTorus.mFourier_add]
  congr 2
  abel_nf

/-- Vector form of the monomial frequency shift: the `(q, i)` coefficient of `e_m f` is the
`(q - m, i)` coefficient of `f`. -/
theorem transverseCoeff_monomialVectorMul
    (m q : TransverseFrequency) (i : Fin 3) (f : TransverseC3L2) :
    transverseCoeffCLM q i
        (scalarVectorMulTransverse (monomialLInf m) f) =
      transverseCoeffCLM (q - m) i f := by
  rw [transverseCoeffCLM, ContinuousLinearMap.comp_apply,
    transverseCoordL2_scalarVectorMulTransverse,
    transverseScalarCoeff_monomialMul]
  rfl

/-- Multiplying by the one-term polynomial `c e_m` shifts the frequency by `m` and scales by `c`:
the `(q, i)` coefficient of the product is `c` times the `(q - m, i)` coefficient of `f`. -/
theorem transverseCoeff_polynomialSingleVectorMul
    (m q : TransverseFrequency) (c : ℂ) (i : Fin 3)
    (f : TransverseC3L2) :
    transverseCoeffCLM q i
        (scalarVectorMulTransverse
          (polynomialLInf (Finsupp.single m c)) f) =
      c * transverseCoeffCLM (q - m) i f := by
  rw [polynomialLInf_single, map_smul, smul_apply, map_smul,
    transverseCoeff_monomialVectorMul]
  simp only [smul_eq_mul]

/-! ## Frequency algebra behind the two product rules -/

/-- The first-order Fourier symbol is additive in the frequency: the symbols at `m` and `q - m`
sum to the symbol at `q`.  This is the frequency algebra behind the first Leibniz rule. -/
theorem derivMultiplier_sub_add
    (j : Fin 2) (m q : TransverseFrequency) :
    transverseFourierDerivMultiplier j m +
      transverseFourierDerivMultiplier j (q - m) =
        transverseFourierDerivMultiplier j q := by
  unfold transverseFourierDerivMultiplier
  rw [Pi.sub_apply]
  push_cast
  ring

/-- Frequency algebra behind the second-order Leibniz rule: the Laplacian symbol at `q` equals
the symbol at `q - m`, plus twice the sum over directions of the two first-order symbols at `m`
and `q - m`, minus the symbol at `m`. -/
theorem laplacianMultiplier_product
    (m q : TransverseFrequency) :
    -(transverseFrequencyEnergy q : ℂ) =
      -(transverseFrequencyEnergy (q - m) : ℂ) +
        2 * (∑ j : Fin 2,
          transverseFourierDerivMultiplier j m *
            transverseFourierDerivMultiplier j (q - m)) -
        (transverseFrequencyEnergy m : ℂ) := by
  unfold transverseFrequencyEnergy transverseFourierDerivMultiplier
  simp only [Fin.sum_univ_two, Pi.sub_apply]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## Bounded product candidates on the `H²` graph -/

/-- Physical multiplication `h ↦ χh` from the `H²` domain to `L²`. -/
def polynomialValueMap (p : TransverseTrigPolynomial) :
    TransverseC3H2 →L[ℂ] TransverseC3L2 :=
  (scalarVectorMulTransverse (polynomialLInf p)).comp
    transverseH2Embedding

/-- The first-order product-rule candidate
`(∂_jχ)h + χ ∂_j h`. -/
def polynomialDerivProductMap (p : TransverseTrigPolynomial) (j : Fin 2) :
    TransverseC3H2 →L[ℂ] TransverseC3L2 :=
  (scalarVectorMulTransverse (polynomialLInf (polynomialDeriv j p))).comp
      transverseH2Embedding +
    (scalarVectorMulTransverse (polynomialLInf p)).comp
      (transverseDerivFromH2 j)

/-- The second-order product-rule candidate
`χ Δh + 2 Σ_j (∂_jχ)(∂_j h) + (Δχ)h`. -/
def polynomialLaplacianProductMap (p : TransverseTrigPolynomial) :
    TransverseC3H2 →L[ℂ] TransverseC3L2 :=
  (scalarVectorMulTransverse (polynomialLInf p)).comp
      transverseLaplacianFromH2 +
    (2 : ℂ) • (∑ j : Fin 2,
      (scalarVectorMulTransverse
        (polynomialLInf (polynomialDeriv j p))).comp
          (transverseDerivFromH2 j)) +
    (scalarVectorMulTransverse
      (polynomialLInf (polynomialLaplacian p))).comp
        transverseH2Embedding

/-- Unfolded action of physical multiplication: `χ` times the physical field underlying the `H²`
element `b`. -/
theorem polynomialValueMap_apply
    (p : TransverseTrigPolynomial) (b : TransverseC3H2) :
    polynomialValueMap p b =
      scalarVectorMulTransverse (polynomialLInf p)
        (transverseH2Embedding b) :=
  rfl

/-- Unfolded action of the first-order Leibniz candidate: `(∂ⱼχ) b + χ (∂ⱼ b)`. -/
theorem polynomialDerivProductMap_apply
    (p : TransverseTrigPolynomial) (j : Fin 2) (b : TransverseC3H2) :
    polynomialDerivProductMap p j b =
      scalarVectorMulTransverse (polynomialLInf (polynomialDeriv j p))
          (transverseH2Embedding b) +
        scalarVectorMulTransverse (polynomialLInf p)
          (transverseDerivFromH2 j b) :=
  rfl

/-- Unfolded action of the second-order Leibniz candidate:
`χ Δb + 2 Σⱼ (∂ⱼχ)(∂ⱼ b) + (Δχ) b`. -/
theorem polynomialLaplacianProductMap_apply
    (p : TransverseTrigPolynomial) (b : TransverseC3H2) :
    polynomialLaplacianProductMap p b =
      scalarVectorMulTransverse (polynomialLInf p)
          (transverseLaplacianFromH2 b) +
        (2 : ℂ) • (∑ j : Fin 2,
          scalarVectorMulTransverse
            (polynomialLInf (polynomialDeriv j p))
              (transverseDerivFromH2 j b)) +
        scalarVectorMulTransverse
          (polynomialLInf (polynomialLaplacian p))
            (transverseH2Embedding b) := by
  simp [polynomialLaplacianProductMap]

/-- Multiplication by the zero polynomial is the zero map. -/
theorem polynomialValueMap_zero :
    polynomialValueMap (0 : TransverseTrigPolynomial) = 0 := by
  ext b
  simp [polynomialValueMap]

/-- Physical multiplication depends additively on the polynomial cutoff. -/
theorem polynomialValueMap_add
    (p q : TransverseTrigPolynomial) :
    polynomialValueMap (p + q) =
      polynomialValueMap p + polynomialValueMap q := by
  ext b
  simp [polynomialValueMap, polynomialLInf_add]

/-- The first-order Leibniz candidate of the zero polynomial is the zero map. -/
theorem polynomialDerivProductMap_zero (j : Fin 2) :
    polynomialDerivProductMap (0 : TransverseTrigPolynomial) j = 0 := by
  ext b
  simp [polynomialDerivProductMap]

/-- The first-order Leibniz candidate depends additively on the polynomial cutoff. -/
theorem polynomialDerivProductMap_add
    (p q : TransverseTrigPolynomial) (j : Fin 2) :
    polynomialDerivProductMap (p + q) j =
      polynomialDerivProductMap p j +
        polynomialDerivProductMap q j := by
  apply ContinuousLinearMap.ext
  intro b
  simp only [polynomialDerivProductMap_apply, map_add,
    polynomialLInf_add, add_apply]
  module

/-- The second-order Leibniz candidate of the zero polynomial is the zero map. -/
theorem polynomialLaplacianProductMap_zero :
    polynomialLaplacianProductMap (0 : TransverseTrigPolynomial) = 0 := by
  ext b
  simp [polynomialLaplacianProductMap]

/-- The second-order Leibniz candidate depends additively on the polynomial cutoff. -/
theorem polynomialLaplacianProductMap_add
    (p q : TransverseTrigPolynomial) :
    polynomialLaplacianProductMap (p + q) =
      polynomialLaplacianProductMap p +
        polynomialLaplacianProductMap q := by
  apply ContinuousLinearMap.ext
  intro b
  simp only [polynomialLaplacianProductMap_apply, map_add,
    polynomialLInf_add, add_apply]
  rw [Finset.sum_add_distrib]
  module

/-! ## Computed first- and second-order Leibniz identities -/

/-- First-order Leibniz rule in the Fourier weak sense: `(∂ⱼχ) b + χ (∂ⱼ b)` is the `j`-th
transverse weak derivative of `χ b`, for every finite Fourier polynomial `χ` and every `H²`
field `b`. -/
theorem polynomialMul_hasFourierDerivative
    (p : TransverseTrigPolynomial) (j : Fin 2) (b : TransverseC3H2) :
    HasTransverseFourierDerivative j
      (polynomialValueMap p b) (polynomialDerivProductMap p j b) := by
  induction p using Finsupp.induction_linear with
  | zero =>
      rw [polynomialValueMap_zero, polynomialDerivProductMap_zero]
      intro n i
      simp
  | add p q hp hq =>
      rw [polynomialValueMap_add, polynomialDerivProductMap_add]
      intro n i
      simp only [add_apply, map_add]
      rw [hp n i, hq n i]
      ring
  | single m c =>
      intro q i
      change transverseCoeffCLM q i
          (polynomialDerivProductMap (Finsupp.single m c) j b) =
        transverseFourierDerivMultiplier j q *
          transverseCoeffCLM q i
            (polynomialValueMap (Finsupp.single m c) b)
      rw [polynomialDerivProductMap_apply,
        polynomialValueMap_apply, map_add, polynomialDeriv_single,
        transverseCoeff_polynomialSingleVectorMul,
        transverseCoeff_polynomialSingleVectorMul,
        transverseCoeffCLM_transverseDerivFromH2,
        transverseCoeff_polynomialSingleVectorMul]
      let z := transverseCoeffCLM (q - m) i (transverseH2Embedding b)
      change transverseFourierDerivMultiplier j m * c * z +
          c * (transverseFourierDerivMultiplier j (q - m) * z) =
        transverseFourierDerivMultiplier j q * (c * z)
      rw [← derivMultiplier_sub_add j m q]
      ring

/-- Second-order Leibniz rule in the Fourier weak sense: `χ Δb + 2 Σⱼ (∂ⱼχ)(∂ⱼ b) + (Δχ) b`
is the weak Laplacian of `χ b`, for every finite Fourier polynomial `χ` and every `H²`
field `b`. -/
theorem polynomialMul_hasFourierLaplacian
    (p : TransverseTrigPolynomial) (b : TransverseC3H2) :
    HasTransverseFourierLaplacian
      (polynomialValueMap p b) (polynomialLaplacianProductMap p b) := by
  induction p using Finsupp.induction_linear with
  | zero =>
      rw [polynomialValueMap_zero, polynomialLaplacianProductMap_zero]
      intro n i
      simp
  | add p q hp hq =>
      rw [polynomialValueMap_add, polynomialLaplacianProductMap_add]
      intro n i
      simp only [add_apply, map_add]
      rw [hp n i, hq n i]
      ring
  | single m c =>
      intro q i
      change transverseCoeffCLM q i
          (polynomialLaplacianProductMap (Finsupp.single m c) b) =
        -(transverseFrequencyEnergy q : ℂ) *
          transverseCoeffCLM q i
            (polynomialValueMap (Finsupp.single m c) b)
      rw [polynomialLaplacianProductMap_apply,
        polynomialValueMap_apply, map_add, map_add, map_smul,
        polynomialLaplacian_single,
        transverseCoeff_polynomialSingleVectorMul,
        transverseCoeffCLM_transverseLaplacianFromH2,
        transverseCoeff_polynomialSingleVectorMul,
        transverseCoeff_polynomialSingleVectorMul]
      simp_rw [map_sum, polynomialDeriv_single,
        transverseCoeff_polynomialSingleVectorMul,
        transverseCoeffCLM_transverseDerivFromH2]
      simp only [smul_eq_mul]
      let z := transverseCoeffCLM (q - m) i (transverseH2Embedding b)
      change c * (-(transverseFrequencyEnergy (q - m) : ℂ) * z) +
          2 * (∑ x : Fin 2, transverseFourierDerivMultiplier x m * c *
            (transverseFourierDerivMultiplier x (q - m) * z)) +
          -(transverseFrequencyEnergy m : ℂ) * c * z =
        -(transverseFrequencyEnergy q : ℂ) * (c * z)
      have hlap := laplacianMultiplier_product m q
      rw [hlap]
      simp only [Fin.sum_univ_two]
      ring

/-! ## Closing the Fourier graph -/

/-- Coordinatewise Fourier analysis, bundled here so the cutoff construction
does not depend on the positive-real diffusion-resolvent module. -/
def transverseC3FourierAnalysisCLM :
    TransverseC3L2 →L[ℂ] WeightedTransverseC3Coeffs :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 3 => TransverseScalarFourierL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      transverseScalarFourierAnalysis.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (transverseCoordL2 i))

/-- The bundled coordinatewise analysis map returns the vector Fourier coefficients: its
`(i, n)` entry is `transverseCoeffCLM n i f`. -/
theorem transverseC3FourierAnalysisCLM_coeff
    (f : TransverseC3L2) (n : TransverseFrequency) (i : Fin 3) :
    (transverseC3FourierAnalysisCLM f i) n =
      transverseCoeffCLM n i f :=
  rfl

/-- The weighted coefficient certificate for `p h`, recovered from the
bounded physical fields `p h` and `Δ(p h)`.  The identity
`(1 - Δ)(p h)` has Fourier coefficient
`(1 + 4π²|n|²) (p h)̂(n)`, exactly the stored `H²` graph weight. -/
def polynomialWeightedCertificate (p : TransverseTrigPolynomial) :
    TransverseC3H2 →L[ℂ] WeightedTransverseC3Coeffs :=
  transverseC3FourierAnalysisCLM.comp
    (polynomialValueMap p - polynomialLaplacianProductMap p)

/-- The weighted certificate attached to `χ b` is the coordinatewise Fourier analysis of
`χ b - Δ(χ b)`. -/
theorem polynomialWeightedCertificate_apply
    (p : TransverseTrigPolynomial) (b : TransverseC3H2) :
    polynomialWeightedCertificate p b =
      transverseC3FourierAnalysisCLM
        (polynomialValueMap p b - polynomialLaplacianProductMap p b) :=
  rfl

/-- The ambient product-valued map whose range is the closed transverse
`H²` Fourier graph. -/
def polynomialH2GraphMap (p : TransverseTrigPolynomial) :
    TransverseC3H2 →L[ℂ]
      (TransverseC3L2 × WeightedTransverseC3Coeffs) :=
  (polynomialValueMap p).prod (polynomialWeightedCertificate p)

/-- The pair consisting of `χ b` and the Fourier coefficients of `(1 - Δ)(χ b)` satisfies the
closed `H²` graph constraint, since the second-order Leibniz rule makes those coefficients equal
to `(1 + 4π²|n|²)` times the coefficients of `χ b`. -/
theorem polynomialH2GraphMap_mem
    (p : TransverseTrigPolynomial) (b : TransverseC3H2) :
    polynomialH2GraphMap p b ∈ transverseH2Submodule := by
  rw [mem_transverseH2Submodule_iff]
  intro n i
  change (polynomialWeightedCertificate p b i) n =
    (transverseH2Weight n : ℂ) *
      transverseCoeffCLM n i (polynomialValueMap p b)
  rw [polynomialWeightedCertificate_apply,
    transverseC3FourierAnalysisCLM_coeff, map_sub]
  rw [polynomialMul_hasFourierLaplacian p b n i]
  unfold transverseH2Weight
  push_cast
  ring

/-- Multiplication by a finite scalar Fourier polynomial as an actual bounded
endomorphism of the repository's closed transverse `H²` graph. -/
def polynomialH2Multiplier (p : TransverseTrigPolynomial) :
    TransverseC3H2 →L[ℂ] TransverseC3H2 :=
  (polynomialH2GraphMap p).codRestrict transverseH2Submodule
    (polynomialH2GraphMap_mem p)

theorem
    transverseH2Embedding_polynomialH2Multiplier
    (p : TransverseTrigPolynomial) (b : TransverseC3H2) :
    transverseH2Embedding (polynomialH2Multiplier p b) =
      polynomialValueMap p b :=
  rfl

/-- The `H²`-level cutoff multiplier has the expected first derivatives: `∂ⱼ(χ b)` is the Leibniz
expression `(∂ⱼχ) b + χ (∂ⱼ b)`. -/
theorem transverseDerivFromH2_polynomialH2Multiplier
    (p : TransverseTrigPolynomial) (j : Fin 2) (b : TransverseC3H2) :
    transverseDerivFromH2 j (polynomialH2Multiplier p b) =
      polynomialDerivProductMap p j b := by
  apply (transverseDerivFromH2_hasFourierDerivative j
    (polynomialH2Multiplier p b)).unique
  rw [transverseH2Embedding_polynomialH2Multiplier]
  exact polynomialMul_hasFourierDerivative p j b

/-- The `H²`-level cutoff multiplier has the expected Laplacian: `Δ(χ b)` is the Leibniz
expression `χ Δb + 2 Σⱼ (∂ⱼχ)(∂ⱼ b) + (Δχ) b`. -/
theorem transverseLaplacianFromH2_polynomialH2Multiplier
    (p : TransverseTrigPolynomial) (b : TransverseC3H2) :
    transverseLaplacianFromH2 (polynomialH2Multiplier p b) =
      polynomialLaplacianProductMap p b := by
  apply (transverseLaplacianFromH2_hasFourierLaplacian
    (polynomialH2Multiplier p b)).unique
  rw [transverseH2Embedding_polynomialH2Multiplier]
  exact polynomialMul_hasFourierLaplacian p b

end TransverseH2CutoffMultiplier

end

end FastDynamo

/-!
## Fourier-summable periodic `H²` cutoff multipliers

This part closes the finite-polynomial construction above under an explicit
Banach space summability criterion.  For each transverse frequency we bundle
the value, both first derivatives, the Laplacian, and the bounded `H²`
multiplier of the corresponding Fourier monomial.  Absolute summability
against the norm of this bundle is then exactly strong enough to sum all
four pieces simultaneously.

The first- and second-order Leibniz rules are not postulated for the limit.
They are closed linear identities on the bundle, so they follow by applying
continuous linear defect maps to the absolutely convergent Fourier series.

The resulting coefficient condition is operator-adapted.  For the explicit
bumps of the parametrix it is discharged in `TransverseSmoothBumpH2CutoffConcrete`,
by bounding `secondOrderFourierWeight n` by an explicit polynomial in `n`; that
estimate is not part of the construction below.
-/

namespace FastDynamo

noncomputable section

open MeasureTheory

namespace TransverseSmoothH2CutoffMultiplier

open PeriodicSecondOrderCutoffs
open TransverseH2CutoffMultiplier

/-! ## The simultaneous Banach-space Fourier package -/

/-- The four analytic pieces needed by `PeriodicSecondOrderCutoff`, bundled
in one complete normed space.  Right association makes the projections
literal and keeps the summability criterion transparent. -/
abbrev SecondOrderCutoffPackage :=
  TransverseScalarLInf ×
    ((Fin 2 → TransverseScalarLInf) ×
      (TransverseScalarLInf ×
        (TransverseC3H2 →L[ℂ] TransverseC3H2)))

/-- Value projection from the simultaneous cutoff package. -/
def packageValue : SecondOrderCutoffPackage →L[ℂ] TransverseScalarLInf :=
  ContinuousLinearMap.fst ℂ _ _

/-- Gradient projection from the simultaneous cutoff package. -/
def packageGradient :
    SecondOrderCutoffPackage →L[ℂ] (Fin 2 → TransverseScalarLInf) :=
  (ContinuousLinearMap.fst ℂ _ _).comp
    (ContinuousLinearMap.snd ℂ TransverseScalarLInf _)

/-- One first-derivative projection from the simultaneous cutoff package. -/
def packageGradientCoord (j : Fin 2) :
    SecondOrderCutoffPackage →L[ℂ] TransverseScalarLInf :=
  (ContinuousLinearMap.proj j).comp packageGradient

/-- Laplacian projection from the simultaneous cutoff package. -/
def packageLaplacian :
    SecondOrderCutoffPackage →L[ℂ] TransverseScalarLInf :=
  (ContinuousLinearMap.fst ℂ _ _).comp
    ((ContinuousLinearMap.snd ℂ _ _).comp
      (ContinuousLinearMap.snd ℂ TransverseScalarLInf _))

/-- Domain-multiplier projection from the simultaneous cutoff package. -/
def packageDomainMul :
    SecondOrderCutoffPackage →L[ℂ]
      (TransverseC3H2 →L[ℂ] TransverseC3H2) :=
  (ContinuousLinearMap.snd ℂ _ _).comp
    ((ContinuousLinearMap.snd ℂ _ _).comp
      (ContinuousLinearMap.snd ℂ TransverseScalarLInf _))

/-- The value projection of the simultaneous cutoff package is exactly the first
component of the tuple. -/
@[simp] theorem packageValue_apply (x : SecondOrderCutoffPackage) :
    packageValue x = x.1 := rfl

/-- The gradient projection of the simultaneous cutoff package is exactly the second
component of the tuple. -/
@[simp] theorem packageGradient_apply (x : SecondOrderCutoffPackage) :
    packageGradient x = x.2.1 := rfl

/-- The `j`th first-derivative projection of the simultaneous cutoff package is the `j`th
entry of its gradient component. -/
@[simp] theorem packageGradientCoord_apply
    (j : Fin 2) (x : SecondOrderCutoffPackage) :
    packageGradientCoord j x = x.2.1 j := rfl

/-- The Laplacian projection of the simultaneous cutoff package is exactly the third
component of the tuple. -/
@[simp] theorem packageLaplacian_apply (x : SecondOrderCutoffPackage) :
    packageLaplacian x = x.2.2.1 := rfl

/-- The domain-multiplier projection of the simultaneous cutoff package is exactly the
last component of the tuple, the bounded operator on `TransverseC3H2`. -/
@[simp] theorem packageDomainMul_apply (x : SecondOrderCutoffPackage) :
    packageDomainMul x = x.2.2.2 := rfl

/-- The simultaneous value/gradient/Laplacian/domain package of a unit
Fourier monomial. -/
def monomialSecondOrderPackage (n : TransverseFrequency) :
    SecondOrderCutoffPackage :=
  (monomialLInf n,
    (fun j ↦ polynomialLInf
      (polynomialDeriv j (Finsupp.single n (1 : ℂ)))),
    polynomialLInf
      (polynomialLaplacian (Finsupp.single n (1 : ℂ))),
    polynomialH2Multiplier (Finsupp.single n (1 : ℂ)))

/-- The simultaneous package of one Fourier frequency with an arbitrary
complex coefficient.  Keeping the coefficient inside the polynomial term
also makes the exact operator-norm summability premise independent of any
operator-norm homogeneity lemma. -/
def coefficientSecondOrderPackage
    (n : TransverseFrequency) (c : ℂ) : SecondOrderCutoffPackage :=
  (polynomialLInf (Finsupp.single n c),
    (fun j ↦ polynomialLInf
      (polynomialDeriv j (Finsupp.single n c))),
    polynomialLInf
      (polynomialLaplacian (Finsupp.single n c)),
    polynomialH2Multiplier (Finsupp.single n c))

/-- The exact operator-adapted second-order Fourier weight.  It controls in
one number the `L∞` value, both `L∞` derivatives, the `L∞` Laplacian,
and multiplication on the closed transverse `H²` graph. -/
def secondOrderFourierWeight (n : TransverseFrequency) : ℝ :=
  ‖monomialSecondOrderPackage n‖

/-- The second-order Fourier weight is nonnegative, being the norm of the monomial
package `monomialSecondOrderPackage n`. -/
theorem secondOrderFourierWeight_nonneg (n : TransverseFrequency) :
    0 ≤ secondOrderFourierWeight n :=
  by exact norm_nonneg (monomialSecondOrderPackage n)

/-- Absolute Fourier summability at the exact second-order multiplier
weight.  This is the sole analytic premise of the completion theorem. -/
def HasSummableSecondOrderFourierWeight
    (a : TransverseFrequency → ℂ) : Prop :=
  Summable fun n ↦ ‖coefficientSecondOrderPackage n (a n)‖

/-- The coefficient-scaled series of simultaneous monomial packages. -/
def secondOrderPackageSeries (a : TransverseFrequency → ℂ)
    (n : TransverseFrequency) : SecondOrderCutoffPackage :=
  coefficientSecondOrderPackage n (a n)

/-- Absolute summability at the second-order weight makes the package-valued series
summable in the Banach space `SecondOrderCutoffPackage`, so value, both derivatives, the
Laplacian and the `H²` multiplier all converge simultaneously. -/
theorem summable_secondOrderPackageSeries
    {a : TransverseFrequency → ℂ}
    (ha : HasSummableSecondOrderFourierWeight a) :
    Summable (secondOrderPackageSeries a) := by
  refine @Summable.of_norm TransverseFrequency
    SecondOrderCutoffPackage _ _ (secondOrderPackageSeries a) ?_
  change Summable fun n ↦
    ‖coefficientSecondOrderPackage n (a n)‖ at ha
  simpa only [secondOrderPackageSeries] using ha

/-- The simultaneous Banach-space sum of a second-order summable Fourier
coefficient family. -/
def completedSecondOrderPackage
    (a : TransverseFrequency → ℂ) : SecondOrderCutoffPackage :=
  ∑' n, secondOrderPackageSeries a n

/-! ## Closed Leibniz-defect maps -/

/-- Evaluation of the domain component of a package at a fixed `H²`
field. -/
def packageDomainApply (b : TransverseC3H2) :
    SecondOrderCutoffPackage →L[ℂ] TransverseC3H2 :=
  (ContinuousLinearMap.apply ℂ TransverseC3H2 b).comp packageDomainMul

/-- Evaluation of a scalar multiplier component against a fixed `L²`
vector field. -/
def scalarMultiplierApply (f : TransverseC3L2) :
    TransverseScalarLInf →L[ℂ] TransverseC3L2 :=
  (ContinuousLinearMap.apply ℂ TransverseC3L2 f).comp
    scalarVectorMulTransverse

/-- The zeroth-order product-rule defect, viewed as a continuous linear map
of the simultaneous package. -/
def embeddingDefect (b : TransverseC3H2) :
    SecondOrderCutoffPackage →L[ℂ] TransverseC3L2 :=
  (transverseH2Embedding.comp (packageDomainApply b) :
      SecondOrderCutoffPackage →L[ℂ] TransverseC3L2) +
    (-1 : ℂ) •
      ((scalarMultiplierApply (transverseH2Embedding b)).comp packageValue)

/-- The `j`-th first-order product-rule defect. -/
def derivativeDefect (j : Fin 2) (b : TransverseC3H2) :
    SecondOrderCutoffPackage →L[ℂ] TransverseC3L2 :=
  ((transverseDerivFromH2 j).comp (packageDomainApply b) :
      SecondOrderCutoffPackage →L[ℂ] TransverseC3L2) +
    (-1 : ℂ) •
      ((scalarMultiplierApply (transverseH2Embedding b)).comp
          (packageGradientCoord j) +
        (scalarMultiplierApply (transverseDerivFromH2 j b)).comp
          packageValue)

/-- The second-order Laplacian product-rule defect. -/
def laplacianDefect (b : TransverseC3H2) :
    SecondOrderCutoffPackage →L[ℂ] TransverseC3L2 :=
  (transverseLaplacianFromH2.comp (packageDomainApply b) :
      SecondOrderCutoffPackage →L[ℂ] TransverseC3L2) +
    (-1 : ℂ) •
      ((scalarMultiplierApply (transverseLaplacianFromH2 b)).comp
          packageValue +
        (2 : ℂ) • (∑ j : Fin 2,
          (scalarMultiplierApply (transverseDerivFromH2 j b)).comp
            (packageGradientCoord j)) +
        (scalarMultiplierApply (transverseH2Embedding b)).comp
          packageLaplacian)

/-- The zeroth-order product-rule defect vanishes on a single-frequency package: for the
monomial `c e_n` the `H²` multiplier followed by the `L²` embedding equals multiplication
by the `L∞` value. -/
theorem embeddingDefect_coefficient
    (n : TransverseFrequency) (c : ℂ) (b : TransverseC3H2) :
    embeddingDefect b (coefficientSecondOrderPackage n c) = 0 := by
  simp only [embeddingDefect, packageDomainApply, scalarMultiplierApply,
    coefficientSecondOrderPackage, packageDomainMul_apply,
    packageValue_apply, add_apply, smul_apply, one_smul, neg_smul,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  change transverseH2Embedding
      (polynomialH2Multiplier (Finsupp.single n c) b) -
    scalarVectorMulTransverse (polynomialLInf (Finsupp.single n c))
      (transverseH2Embedding b) = 0
  rw [transverseH2Embedding_polynomialH2Multiplier]
  rw [polynomialValueMap_apply]
  exact sub_self _

/-- The `j`th first-order product-rule defect vanishes on a single-frequency package, i.e.
`∂_j (m b) = (∂_j m) b + m (∂_j b)` holds exactly for the monomial multiplier `c e_n`. -/
theorem derivativeDefect_coefficient
    (n : TransverseFrequency) (c : ℂ) (j : Fin 2)
    (b : TransverseC3H2) :
    derivativeDefect j b (coefficientSecondOrderPackage n c) = 0 := by
  simp only [derivativeDefect, packageDomainApply, scalarMultiplierApply,
    coefficientSecondOrderPackage, packageDomainMul_apply,
    packageGradientCoord_apply, packageValue_apply,
    add_apply, smul_apply,
    one_smul, neg_smul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply]
  rw [transverseDerivFromH2_polynomialH2Multiplier,
    polynomialDerivProductMap_apply]
  exact add_neg_cancel _

/-- The second-order product-rule defect vanishes on a single-frequency package, i.e.
`Δ(m b) = (Δm) b + 2 ∑_j (∂_j m)(∂_j b) + m (Δb)` holds exactly for the monomial
multiplier `c e_n`. -/
theorem laplacianDefect_coefficient
    (n : TransverseFrequency) (c : ℂ) (b : TransverseC3H2) :
    laplacianDefect b (coefficientSecondOrderPackage n c) = 0 := by
  simp only [laplacianDefect, packageDomainApply, scalarMultiplierApply,
    coefficientSecondOrderPackage, packageDomainMul_apply,
    packageValue_apply, packageGradientCoord_apply,
    packageLaplacian_apply, add_apply, smul_apply, one_smul, neg_smul,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    sum_apply]
  rw [transverseLaplacianFromH2_polynomialH2Multiplier,
    polynomialLaplacianProductMap_apply]
  exact add_neg_cancel _

/-- Since `embeddingDefect b` is a continuous linear map killing every single-frequency
term, it also kills the summed package: the completed multiplier still agrees with
multiplication by its `L∞` value after embedding into `L²`. -/
theorem embeddingDefect_completed_eq_zero
    {a : TransverseFrequency → ℂ}
    (ha : HasSummableSecondOrderFourierWeight a)
    (b : TransverseC3H2) :
    embeddingDefect b (completedSecondOrderPackage a) = 0 := by
  unfold completedSecondOrderPackage
  rw [(embeddingDefect b).map_tsum
    (summable_secondOrderPackageSeries ha)]
  simp [secondOrderPackageSeries, embeddingDefect_coefficient]

/-- The first-order Leibniz identity passes to the Fourier limit: the continuous linear
defect map `derivativeDefect j b` annihilates the completed package. -/
theorem derivativeDefect_completed_eq_zero
    {a : TransverseFrequency → ℂ}
    (ha : HasSummableSecondOrderFourierWeight a)
    (j : Fin 2) (b : TransverseC3H2) :
    derivativeDefect j b (completedSecondOrderPackage a) = 0 := by
  unfold completedSecondOrderPackage
  rw [(derivativeDefect j b).map_tsum
    (summable_secondOrderPackageSeries ha)]
  simp [secondOrderPackageSeries, derivativeDefect_coefficient]

/-- The second-order Leibniz identity passes to the Fourier limit: the continuous linear
defect map `laplacianDefect b` annihilates the completed package. -/
theorem laplacianDefect_completed_eq_zero
    {a : TransverseFrequency → ℂ}
    (ha : HasSummableSecondOrderFourierWeight a)
    (b : TransverseC3H2) :
    laplacianDefect b (completedSecondOrderPackage a) = 0 := by
  unfold completedSecondOrderPackage
  rw [(laplacianDefect b).map_tsum
    (summable_secondOrderPackageSeries ha)]
  simp [secondOrderPackageSeries, laplacianDefect_coefficient]

/-! ## The completed periodic cutoff -/

/-- A Fourier coefficient family summable at the simultaneous second-order
weight defines an actual periodic cutoff on the repository's closed `H²`
graph, with the first- and second-order Leibniz identities. -/
def summableFourierPeriodicSecondOrderCutoff
    (a : TransverseFrequency → ℂ)
    (ha : HasSummableSecondOrderFourierWeight a) :
    PeriodicSecondOrderCutoff where
  value := packageValue (completedSecondOrderPackage a)
  gradient := fun j ↦ packageGradientCoord j
    (completedSecondOrderPackage a)
  laplacian := packageLaplacian (completedSecondOrderPackage a)
  domainMul := packageDomainMul (completedSecondOrderPackage a)
  embedding_domainMul := by
    intro b
    have h := embeddingDefect_completed_eq_zero ha b
    have h' :
        transverseH2Embedding
            (packageDomainMul (completedSecondOrderPackage a) b) -
          scalarVectorMulTransverse
            (packageValue (completedSecondOrderPackage a))
            (transverseH2Embedding b) = 0 := by
      simp only [embeddingDefect, packageDomainApply,
        scalarMultiplierApply, packageDomainMul_apply,
        packageValue_apply, add_apply, smul_apply, one_smul, neg_smul,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply] at h
      rw [← sub_eq_add_neg] at h
      exact h
    simpa using sub_eq_zero.mp h'
  deriv_domainMul := by
    intro j b
    have h := derivativeDefect_completed_eq_zero ha j b
    have h' :
        transverseDerivFromH2 j
            (packageDomainMul (completedSecondOrderPackage a) b) -
          (scalarVectorMulTransverse
              (packageGradientCoord j (completedSecondOrderPackage a))
              (transverseH2Embedding b) +
            scalarVectorMulTransverse
              (packageValue (completedSecondOrderPackage a))
              (transverseDerivFromH2 j b)) = 0 := by
      simp only [derivativeDefect, packageDomainApply,
        scalarMultiplierApply, packageDomainMul_apply,
        packageGradientCoord_apply, packageValue_apply,
        add_apply, smul_apply, one_smul, neg_smul,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply] at h
      rw [← sub_eq_add_neg] at h
      exact h
    simpa using sub_eq_zero.mp h'
  laplacian_domainMul := by
    intro b
    have h := laplacianDefect_completed_eq_zero ha b
    have h' :
        transverseLaplacianFromH2
            (packageDomainMul (completedSecondOrderPackage a) b) -
          (scalarVectorMulTransverse
              (packageValue (completedSecondOrderPackage a))
              (transverseLaplacianFromH2 b) +
            (2 : ℂ) • (∑ j : Fin 2,
              scalarVectorMulTransverse
                (packageGradientCoord j (completedSecondOrderPackage a))
                (transverseDerivFromH2 j b)) +
            scalarVectorMulTransverse
              (packageLaplacian (completedSecondOrderPackage a))
              (transverseH2Embedding b)) = 0 := by
      simp only [laplacianDefect, packageDomainApply,
        scalarMultiplierApply, packageDomainMul_apply,
        packageValue_apply, packageGradientCoord_apply,
        packageLaplacian_apply, add_apply, smul_apply, one_smul, neg_smul,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply, sum_apply] at h
      rw [← sub_eq_add_neg] at h
      exact h
    simpa using sub_eq_zero.mp h'

end TransverseSmoothH2CutoffMultiplier

end

end FastDynamo
