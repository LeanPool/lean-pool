/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.TransverseSmoothH2CutoffMultiplier
public import Mathlib.Analysis.PSeries

/-!
# Concrete polynomial bound for the smooth periodic cutoff package

The two-resolvent construction of §7.1 (`eq:parametrix-cutoff-bounds`)
multiplies periodic `H²` fields by smooth parametrix cut-offs, which the formalisation realises
as Schwartz bumps.  The
abstract Fourier completion in `TransverseSmoothH2CutoffMultiplier` makes that multiplication
bounded once the simultaneous value/derivative/Laplacian/multiplier package is absolutely
summable over the frequency lattice.  This module supplies the two ingredients of that
summability for coefficients with rapid decay on the frequency lattice, such as the lattice
Fourier samples of a Schwartz bump (applied in `Global/TorusSchwartzPeriodicCutoff.lean`).

The summability premise is first reduced: the package at frequency `n` with coefficient `c` is
exactly `c` times the unit-monomial package, so scalar weighted `ℓ¹` summability against
`secondOrderFourierWeight` suffices, and rapid decay on the lattice absorbs every polynomially
growing weight.  What this leaves open, a polynomial bound for the operator weight itself, is
then proved quantitatively: the value, the first derivatives, the Laplacian, and the
closed-graph `H²` multiplier of a Fourier character are all bounded by a fixed constant times
`(1 + ‖n‖)²`.

## Contents

* Reduction of the summability premise: scalar homogeneity of the simultaneous package, integer
  frequency points, and absorption of every polynomial operator weight by rapid decay.
* Concrete polynomial bound for the smooth periodic cutoff package: scalar Fourier-character
  estimates, the closed-graph `H²` multiplier estimate, polynomial growth of the simultaneous
  package, and exact coefficients of the completed Fourier series.
-/

@[expose] public section

/-!
## Reduction of the summability premise

The abstract Fourier completion in
`TransverseSmoothH2CutoffMultiplier` asks for summability of a Banach-space
package.  This part separates that premise into two ingredients.

* The package at frequency `n` and coefficient `c` is exactly `c` times the
  unit-monomial package.  Thus the scalar weighted `ℓ¹` condition
  `Summable (fun n ↦ ‖a n‖ * secondOrderFourierWeight n)`
  is sufficient for the abstract premise.
* Coefficients with arbitrary polynomial decay on the integer frequency
  lattice (`HasRapidDecayOnFrequencyLattice`) satisfy that condition for every
  polynomially growing weight.

Consequently the only further input is a polynomial-growth estimate for the
concrete operator weight `secondOrderFourierWeight`; it is proved in the second
part below.
-/

namespace FastDynamo

noncomputable section

open scoped FourierTransform SchwartzMap

namespace TransverseSmoothBumpH2Cutoff

open TransverseH2CutoffMultiplier
open TransverseSmoothH2CutoffMultiplier
open ParametrixExplicitCutoff

/-! ## Scalar homogeneity of the simultaneous package -/

/-- The bounded `H²` multiplication operator attached to the monomial with coefficient `c`
at frequency `n` is `c` times the one attached to the unit monomial. -/
theorem polynomialH2Multiplier_single_smul
    (n : TransverseFrequency) (c : ℂ) :
    polynomialH2Multiplier (Finsupp.single n c) =
      c • polynomialH2Multiplier (Finsupp.single n (1 : ℂ)) := by
  apply ContinuousLinearMap.ext
  intro b
  apply transverseH2Embedding_injective
  simp only [smul_apply]
  rw [map_smul, transverseH2Embedding_polynomialH2Multiplier]
  rw [polynomialValueMap_apply, polynomialLInf_single, map_smul]
  rw [transverseH2Embedding_polynomialH2Multiplier,
    polynomialValueMap_apply]
  rfl

/-- The whole four-component package at frequency `n` is homogeneous in the coefficient:
`coefficientSecondOrderPackage n c = c • monomialSecondOrderPackage n`. -/
theorem coefficientSecondOrderPackage_eq_smul
    (n : TransverseFrequency) (c : ℂ) :
    coefficientSecondOrderPackage n c =
      c • monomialSecondOrderPackage n := by
  apply Prod.ext
  · exact polynomialLInf_single n c
  · apply Prod.ext
    · funext j
      change polynomialLInf
          (polynomialDeriv j (Finsupp.single n c)) =
        c • polynomialLInf
          (polynomialDeriv j (Finsupp.single n (1 : ℂ)))
      rw [polynomialDeriv_single, polynomialLInf_single,
        polynomialDeriv_single, polynomialLInf_single]
      simp only [smul_smul]
      congr 1
      ring
    · apply Prod.ext
      · change polynomialLInf
            (polynomialLaplacian (Finsupp.single n c)) =
          c • polynomialLInf
            (polynomialLaplacian (Finsupp.single n (1 : ℂ)))
        rw [polynomialLaplacian_single, polynomialLInf_single,
          polynomialLaplacian_single, polynomialLInf_single]
        simp only [smul_smul]
        congr 1
        ring
      · change polynomialH2Multiplier (Finsupp.single n c) =
          c • polynomialH2Multiplier (Finsupp.single n (1 : ℂ))
        exact polynomialH2Multiplier_single_smul n c

/-- Scalar bound for the simultaneous package: its norm is at most `‖c‖` times the
operator-adapted weight `secondOrderFourierWeight n`.  This is what turns the abstract
Banach-valued summability premise into an ordinary weighted `ℓ¹` condition. -/
theorem norm_coefficientSecondOrderPackage_le
    (n : TransverseFrequency) (c : ℂ) :
    ‖coefficientSecondOrderPackage n c‖ ≤
      ‖c‖ * secondOrderFourierWeight n := by
  rw [coefficientSecondOrderPackage_eq_smul]
  rw [secondOrderFourierWeight]
  simp only [monomialSecondOrderPackage, Prod.norm_def, Prod.smul_fst,
    Prod.smul_snd]
  rw [max_le_iff, max_le_iff, max_le_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      (le_max_left _ (max _ (max _ _))) (norm_nonneg c)
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      ((le_max_left _ (max _ _)).trans
        (le_max_right _ _)) (norm_nonneg c)
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      ((le_max_left _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))) (norm_nonneg c)
  · exact (ContinuousLinearMap.opNorm_smul_le c _).trans
      (mul_le_mul_of_nonneg_left
        ((le_max_right _ _).trans
          ((le_max_right _ _).trans (le_max_right _ _)))
        (norm_nonneg c))

/-- The operator-adapted summability premise follows from the ordinary scalar
weighted `ℓ1` premise.  This is the convenient interface for Fourier-decay
estimates. -/
theorem hasSummableSecondOrderFourierWeight_of_scalar
    (a : TransverseFrequency → ℂ)
    (ha : Summable (fun n ↦ ‖a n‖ * secondOrderFourierWeight n)) :
    HasSummableSecondOrderFourierWeight a := by
  change Summable fun n ↦ ‖coefficientSecondOrderPackage n (a n)‖
  exact Summable.of_nonneg_of_le
    (f := fun n ↦ ‖a n‖ * secondOrderFourierWeight n)
    (g := fun n ↦ ‖coefficientSecondOrderPackage n (a n)‖)
    (fun n ↦ norm_nonneg (coefficientSecondOrderPackage n (a n)))
    (fun n ↦ norm_coefficientSecondOrderPackage_le n (a n)) ha

/-! ## Integer frequency points -/

/-- The normalized integer frequency as a point of the whole-plane Fourier
variable. -/
def frequencyPoint (n : TransverseFrequency) : WholePlane :=
  WithLp.toLp 2 (fun j ↦ (n j : ℝ))

/-- The lattice point attached to an integer frequency has the frequency's integer entries
as its real coordinates. -/
@[simp] theorem frequencyPoint_apply
    (n : TransverseFrequency) (j : Fin 2) :
    frequencyPoint n j = (n j : ℝ) :=
  rfl

/-! ## Rapid decay absorbs every polynomial operator weight -/

/-- Arbitrary radial polynomial decay on the integer frequency lattice. -/
def HasRapidDecayOnFrequencyLattice
    (a : TransverseFrequency → ℂ) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, ∀ n : TransverseFrequency,
    ‖frequencyPoint n‖ ^ k * ‖a n‖ ≤ C

/-- Radial rapid decay remains true with the convenient inhomogeneous
weight `1 + ‖n‖`. -/
theorem HasRapidDecayOnFrequencyLattice.one_add
    {a : TransverseFrequency → ℂ}
    (ha : HasRapidDecayOnFrequencyLattice a) (k : ℕ) :
    ∃ C : ℝ, ∀ n : TransverseFrequency,
      (1 + ‖frequencyPoint n‖) ^ k * ‖a n‖ ≤ C := by
  rcases ha 0 with ⟨C0, h0⟩
  rcases ha k with ⟨Ck, hk⟩
  refine ⟨2 ^ (k - 1) * (C0 + Ck), fun n ↦ ?_⟩
  have hp := add_pow_le (show 0 ≤ (1 : ℝ) by norm_num)
    (norm_nonneg (frequencyPoint n)) k
  calc
    (1 + ‖frequencyPoint n‖) ^ k * ‖a n‖ ≤
        (2 ^ (k - 1) *
          (1 ^ k + ‖frequencyPoint n‖ ^ k)) * ‖a n‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg (a n))
    _ = 2 ^ (k - 1) *
        (‖frequencyPoint n‖ ^ 0 * ‖a n‖ +
          ‖frequencyPoint n‖ ^ k * ‖a n‖) := by ring
    _ ≤ 2 ^ (k - 1) * (C0 + Ck) :=
      mul_le_mul_of_nonneg_left (add_le_add (h0 n) (hk n)) (by positivity)

/-- A one-dimensional summable quadratic-decay envelope. -/
def integerDecayTwo (m : ℤ) : ℝ :=
  (1 + |(m : ℝ)|) ^ (-2 : ℝ)

/-- The one-dimensional envelope `(1 + |m|)^(-2)` is nonnegative. -/
theorem integerDecayTwo_nonneg (m : ℤ) :
    0 ≤ integerDecayTwo m :=
  Real.rpow_nonneg (by positivity) _

/-- The one-dimensional envelope is summable over `ℤ`: `∑_{m ∈ ℤ} (1 + |m|)^(-2) < ∞`. -/
theorem summable_integerDecayTwo : Summable integerDecayTwo := by
  apply Summable.of_norm_bounded_eventually
    (Real.summable_abs_int_rpow (b := 2) (by norm_num))
  have hevent : ∀ᶠ m : ℤ in Filter.cofinite, m ≠ 0 := by
    rw [Filter.eventually_cofinite]
    simp
  filter_upwards [hevent] with m _hm
  rw [Real.norm_eq_abs, abs_of_nonneg (integerDecayTwo_nonneg m)]
  unfold integerDecayTwo
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (abs_nonneg _)]
  gcongr
  linarith [abs_nonneg (m : ℝ)]

/-- Product quadratic decay in the two integer coordinates. -/
def transverseProductDecayFour (n : TransverseFrequency) : ℝ :=
  integerDecayTwo (n 0) * integerDecayTwo (n 1)

/-- The product envelope `(1 + |n 0|)^(-2) (1 + |n 1|)^(-2)` is summable over the
two-dimensional integer frequency lattice. -/
theorem summable_transverseProductDecayFour :
    Summable transverseProductDecayFour := by
  let _ : AddCommMonoid ℝ := Real.instAddCommGroup.toAddCommMonoid
  have hp : Summable (fun z : ℤ × ℤ ↦
      integerDecayTwo z.1 * integerDecayTwo z.2) :=
    summable_integerDecayTwo.mul_of_nonneg summable_integerDecayTwo
      integerDecayTwo_nonneg integerDecayTwo_nonneg
  have hc := hp.comp_injective (finTwoArrowEquiv ℤ).injective
  exact hc.congr (fun _ ↦ rfl)

/-- Each integer coordinate of a transverse frequency is bounded by the Euclidean norm of
the associated lattice point. -/
theorem abs_frequency_le_norm_frequencyPoint
    (n : TransverseFrequency) (j : Fin 2) :
    |(n j : ℝ)| ≤ ‖frequencyPoint n‖ := by
  simpa [frequencyPoint, Real.norm_eq_abs] using
    PiLp.norm_apply_le (frequencyPoint n) j

/-- A radial fourth-order envelope on the integer lattice. -/
def transverseRadialDecayFour (n : TransverseFrequency) : ℝ :=
  (1 + ‖frequencyPoint n‖) ^ (-4 : ℝ)

/-- The radial envelope `(1 + ‖n‖)^(-4)` is dominated by the product envelope, since each
coordinate is bounded by the norm. -/
theorem transverseRadialDecayFour_le_product
    (n : TransverseFrequency) :
    transverseRadialDecayFour n ≤ transverseProductDecayFour n := by
  have hcoord (j : Fin 2) :
      (1 + ‖frequencyPoint n‖) ^ (-2 : ℝ) ≤
        (1 + |(n j : ℝ)|) ^ (-2 : ℝ) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
    gcongr
    exact abs_frequency_le_norm_frequencyPoint n j
  unfold transverseRadialDecayFour transverseProductDecayFour integerDecayTwo
  rw [show (-4 : ℝ) = -2 + -2 by norm_num,
    Real.rpow_add (by positivity)]
  exact mul_le_mul (hcoord 0) (hcoord 1)
    (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (by positivity) _)

/-- The radial fourth-order envelope `(1 + ‖n‖)^(-4)` is summable over the integer
frequency lattice, by comparison with the product envelope. -/
theorem summable_transverseRadialDecayFour :
    Summable transverseRadialDecayFour := by
  exact Summable.of_nonneg_of_le
    (fun _ ↦ Real.rpow_nonneg (by positivity) _)
    transverseRadialDecayFour_le_product
    summable_transverseProductDecayFour

/-- Polynomial growth on the integer frequency lattice. -/
def HasPolynomialGrowthOnFrequencyLattice
    (w : TransverseFrequency → ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∃ d : ℕ, ∀ n : TransverseFrequency,
    w n ≤ A * (1 + ‖frequencyPoint n‖) ^ d

/-- Arbitrary Schwartz decay absorbs every nonnegative polynomially growing
lattice weight in dimension two. -/
theorem summable_norm_mul_of_rapidDecay_polynomialGrowth
    {a : TransverseFrequency → ℂ} {w : TransverseFrequency → ℝ}
    (ha : HasRapidDecayOnFrequencyLattice a)
    (hw0 : ∀ n, 0 ≤ w n)
    (hw : HasPolynomialGrowthOnFrequencyLattice w) :
    Summable (fun n ↦ ‖a n‖ * w n) := by
  rcases hw with ⟨A, hA, d, hw⟩
  rcases ha.one_add (d + 4) with ⟨C, hC⟩
  have hpoint (n : TransverseFrequency) :
      ‖a n‖ * w n ≤ A * C * transverseRadialDecayFour n := by
    let x : ℝ := 1 + ‖frequencyPoint n‖
    have hx : 0 < x := by
      dsimp [x]
      positivity
    have hx4 : 0 < x ^ 4 := pow_pos hx _
    have hcore : x ^ d * ‖a n‖ ≤ C / x ^ 4 := by
      apply (le_div_iff₀ hx4).2
      calc
        x ^ d * ‖a n‖ * x ^ 4 = x ^ (d + 4) * ‖a n‖ := by
          rw [pow_add]
          ring
        _ ≤ C := hC n
    calc
      ‖a n‖ * w n ≤ ‖a n‖ * (A * x ^ d) :=
        mul_le_mul_of_nonneg_left (hw n) (norm_nonneg (a n))
      _ = A * (x ^ d * ‖a n‖) := by ring
      _ ≤ A * (C / x ^ 4) := mul_le_mul_of_nonneg_left hcore hA
      _ = A * C * transverseRadialDecayFour n := by
        unfold transverseRadialDecayFour
        rw [Real.rpow_neg (by positivity)]
        norm_num
        ring
  exact Summable.of_nonneg_of_le
    (fun n ↦ mul_nonneg (norm_nonneg (a n)) (hw0 n)) hpoint
    (summable_transverseRadialDecayFour.mul_left (A * C))

/-- Polynomial growth of the concrete simultaneous monomial package: given rapid decay of the
coefficients, the only further estimate needed (proved in the second part). -/
def SecondOrderFourierWeightHasPolynomialGrowth : Prop :=
  HasPolynomialGrowthOnFrequencyLattice secondOrderFourierWeight

end TransverseSmoothBumpH2Cutoff

end

end FastDynamo

/-!
## Concrete polynomial bound for the smooth periodic cutoff package

This part proves the operator-growth premise
`SecondOrderFourierWeightHasPolynomialGrowth` of the first part.  The proof is quantitative:
the value, first derivatives, Laplacian, and the closed-graph `H²` multiplier of a Fourier character
are all bounded by a fixed constant times `(1 + ‖n‖)²`. -/

namespace FastDynamo

noncomputable section

open MeasureTheory

namespace TransverseSmoothBumpH2CutoffConcrete

open TransverseH2CutoffMultiplier
open TransverseSmoothH2CutoffMultiplier
open TransverseSmoothBumpH2Cutoff

/-! ## Scalar Fourier-character estimates -/

/-- A quotient-level Fourier character has `L∞` norm at most one. -/
theorem norm_monomialLInf_le_one (n : TransverseFrequency) :
    ‖monomialLInf n‖ ≤ 1 := by
  let T : C(TransverseTorus, ℂ) →L[ℂ] TransverseScalarLInf :=
    ContinuousMap.toLp ⊤ transverseMeasure ℂ
  let e : TransverseScalarLInf := T (UnitAddTorus.mFourier n)
  have heq : monomialLInf n = e := by
    apply Lp.ext
    filter_upwards [monomialLInf_coe_ae n,
      ContinuousMap.coeFn_toLp (p := (⊤ : ENNReal)) (𝕜 := ℂ)
        transverseMeasure (UnitAddTorus.mFourier n)] with x hx he
    exact hx.trans he.symm
  rw [heq]
  have hT : ‖T‖ ≤ 1 := by
    simpa [T] using ContinuousMap.toLp_norm_le
      (p := (⊤ : ENNReal)) (μ := transverseMeasure) (𝕜 := ℂ)
  calc
    ‖e‖ ≤ ‖T‖ * ‖UnitAddTorus.mFourier n‖ := T.le_opNorm _
    _ ≤ 1 * 1 := by
      simpa [UnitAddTorus.mFourier_norm] using hT
    _ = 1 := one_mul _

/-- The inhomogeneous radial lattice variable used below. -/
def frequencyRadius (n : TransverseFrequency) : ℝ :=
  1 + ‖frequencyPoint n‖

/-- The inhomogeneous radial variable `1 + ‖frequencyPoint n‖` is at least one. -/
theorem one_le_frequencyRadius (n : TransverseFrequency) :
    1 ≤ frequencyRadius n := by
  unfold frequencyRadius
  exact le_add_of_nonneg_right (norm_nonneg _)

/-- The inhomogeneous radial variable is nonnegative. -/
theorem frequencyRadius_nonneg (n : TransverseFrequency) :
    0 ≤ frequencyRadius n :=
  (zero_le_one.trans (one_le_frequencyRadius n))

/-- The Euclidean norm of a lattice frequency is below its inhomogeneous radial
variable `1 + ‖frequencyPoint n‖`. -/
theorem norm_frequencyPoint_le_frequencyRadius (n : TransverseFrequency) :
    ‖frequencyPoint n‖ ≤ frequencyRadius n := by
  unfold frequencyRadius
  linarith

/-- Since the radial variable is at least one, it is dominated by its square; this is what
lets every first-order estimate be stated with the single quadratic weight. -/
theorem frequencyRadius_le_sq (n : TransverseFrequency) :
    frequencyRadius n ≤ frequencyRadius n ^ 2 := by
  nlinarith [one_le_frequencyRadius n]

/-- The squared radial variable is at least one. -/
theorem one_le_frequencyRadius_sq (n : TransverseFrequency) :
    1 ≤ frequencyRadius n ^ 2 :=
  (one_le_frequencyRadius n).trans (frequencyRadius_le_sq n)

/-- The Euclidean norm of a lattice frequency is dominated by the quadratic weight
`frequencyRadius n ^ 2`. -/
theorem norm_frequencyPoint_le_radius_sq (n : TransverseFrequency) :
    ‖frequencyPoint n‖ ≤ frequencyRadius n ^ 2 :=
  (norm_frequencyPoint_le_frequencyRadius n).trans
    (frequencyRadius_le_sq n)

/-- The `L∞` norm of the `j`th derivative of the unit Fourier character at frequency `n`
equals `2π |n j|`, hence is at most `2π (1 + ‖n‖)²`. -/
theorem norm_monomialDerivLInf_le
    (n : TransverseFrequency) (j : Fin 2) :
    ‖polynomialLInf
        (polynomialDeriv j (Finsupp.single n (1 : ℂ)))‖ ≤
      (2 * Real.pi) * frequencyRadius n ^ 2 := by
  rw [polynomialDeriv_single, polynomialLInf_single, norm_smul]
  simp only [mul_one]
  calc
    ‖transverseFourierDerivMultiplier j n‖ * ‖monomialLInf n‖ ≤
        ‖transverseFourierDerivMultiplier j n‖ * 1 := by
      gcongr
      exact norm_monomialLInf_le_one n
    _ = (2 * Real.pi) * |(n j : ℝ)| := by
      simp [transverseFourierDerivMultiplier, abs_of_pos Real.pi_pos]
    _ ≤ (2 * Real.pi) * ‖frequencyPoint n‖ := by
      gcongr
      exact abs_frequency_le_norm_frequencyPoint n j
    _ ≤ (2 * Real.pi) * frequencyRadius n ^ 2 := by
      gcongr
      exact norm_frequencyPoint_le_radius_sq n

/-- The Fourier symbol `(2π)² (n₀² + n₁²)` of the transverse Laplacian is bounded by
`2 (2π)² (1 + ‖n‖)²`. -/
theorem transverseFrequencyEnergy_le_radius_sq
    (n : TransverseFrequency) :
    transverseFrequencyEnergy n ≤
      (2 * (2 * Real.pi) ^ 2) * frequencyRadius n ^ 2 := by
  have h0 := abs_frequency_le_norm_frequencyPoint n (0 : Fin 2)
  have h1 := abs_frequency_le_norm_frequencyPoint n (1 : Fin 2)
  have hs0 : (n 0 : ℝ) ^ 2 ≤ ‖frequencyPoint n‖ ^ 2 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (n 0 : ℝ), norm_nonneg (frequencyPoint n)]
  have hs1 : (n 1 : ℝ) ^ 2 ≤ ‖frequencyPoint n‖ ^ 2 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (n 1 : ℝ), norm_nonneg (frequencyPoint n)]
  have hr := norm_frequencyPoint_le_frequencyRadius n
  have hrsq : ‖frequencyPoint n‖ ^ 2 ≤ frequencyRadius n ^ 2 := by
    nlinarith [norm_nonneg (frequencyPoint n), frequencyRadius_nonneg n]
  unfold transverseFrequencyEnergy
  simp only [Fin.sum_univ_two]
  have hpi : 0 ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
  calc
    (2 * Real.pi) ^ 2 * ((n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2) ≤
        (2 * Real.pi) ^ 2 *
          (2 * ‖frequencyPoint n‖ ^ 2) := by
      gcongr
      linarith
    _ ≤ (2 * Real.pi) ^ 2 *
          (2 * frequencyRadius n ^ 2) := by
      gcongr
    _ = (2 * (2 * Real.pi) ^ 2) * frequencyRadius n ^ 2 := by ring

/-- The `L∞` norm of the transverse Laplacian of the unit Fourier character at frequency
`n` is its frequency energy, hence at most `2 (2π)² (1 + ‖n‖)²`. -/
theorem norm_monomialLaplacianLInf_le
    (n : TransverseFrequency) :
    ‖polynomialLInf
        (polynomialLaplacian (Finsupp.single n (1 : ℂ)))‖ ≤
      (2 * (2 * Real.pi) ^ 2) * frequencyRadius n ^ 2 := by
  rw [polynomialLaplacian_single, polynomialLInf_single, norm_smul]
  calc
    ‖(-(transverseFrequencyEnergy n : ℂ) * (1 : ℂ))‖ *
          ‖monomialLInf n‖ ≤
        ‖(-(transverseFrequencyEnergy n : ℂ) * (1 : ℂ))‖ * 1 := by
      gcongr
      exact norm_monomialLInf_le_one n
    _ = transverseFrequencyEnergy n := by
      simp [abs_of_nonneg (transverseFrequencyEnergy_nonneg n)]
    _ ≤ (2 * (2 * Real.pi) ^ 2) * frequencyRadius n ^ 2 :=
      transverseFrequencyEnergy_le_radius_sq n

/-! ## The closed-graph `H²` multiplier estimate -/

/-- A fixed constant controlling the three terms in the Laplacian product
rule.  All dependence on the Fourier frequency is kept outside this
constant. -/
def laplacianProductGrowthConstant : ℝ :=
  ‖transverseLaplacianFromH2‖ +
    2 * (2 * Real.pi) *
      (‖transverseDerivFromH2 (0 : Fin 2)‖ +
        ‖transverseDerivFromH2 (1 : Fin 2)‖) +
    2 * (2 * Real.pi) ^ 2

/-- Multiplying an `H²` field by a unit Fourier character is contractive into `L²`, so in
particular it obeys the quadratic bound `‖·‖ ≤ (1 + ‖n‖)² ‖b‖`. -/
theorem norm_monomialValueMap_apply_le
    (n : TransverseFrequency) (b : TransverseC3H2) :
    ‖polynomialValueMap (Finsupp.single n (1 : ℂ)) b‖ ≤
      frequencyRadius n ^ 2 * ‖b‖ := by
  rw [polynomialValueMap_apply]
  calc
    ‖scalarVectorMulTransverse (monomialLInf n)
        (transverseH2Embedding b)‖ ≤
        ‖monomialLInf n‖ * ‖transverseH2Embedding b‖ :=
      norm_scalarVectorMulTransverse_apply_le _ _
    _ ≤ 1 * ‖b‖ := by
      exact mul_le_mul (norm_monomialLInf_le_one n)
        (norm_transverseH2Embedding_le b) (norm_nonneg _) zero_le_one
    _ ≤ frequencyRadius n ^ 2 * ‖b‖ := by
      gcongr
      exact one_le_frequencyRadius_sq n

/-- The mixed term `(∂_j m)(∂_j b)` of the Laplacian product rule, for `m` the unit
character at frequency `n`, is bounded by `2π ‖∂_j‖ (1 + ‖n‖)² ‖b‖`. -/
theorem norm_monomialDerivTerm_le
    (n : TransverseFrequency) (j : Fin 2) (b : TransverseC3H2) :
    ‖scalarVectorMulTransverse
        (polynomialLInf
          (polynomialDeriv j (Finsupp.single n (1 : ℂ))))
        (transverseDerivFromH2 j b)‖ ≤
      ((2 * Real.pi) * ‖transverseDerivFromH2 j‖) *
        frequencyRadius n ^ 2 * ‖b‖ := by
  calc
    ‖scalarVectorMulTransverse
        (polynomialLInf
          (polynomialDeriv j (Finsupp.single n (1 : ℂ))))
        (transverseDerivFromH2 j b)‖ ≤
        ‖polynomialLInf
          (polynomialDeriv j (Finsupp.single n (1 : ℂ)))‖ *
          ‖transverseDerivFromH2 j b‖ :=
      norm_scalarVectorMulTransverse_apply_le _ _
    _ ≤ ((2 * Real.pi) * frequencyRadius n ^ 2) *
          (‖transverseDerivFromH2 j‖ * ‖b‖) := by
      exact mul_le_mul (norm_monomialDerivLInf_le n j)
        ((transverseDerivFromH2 j).le_opNorm b)
        (norm_nonneg _) (by positivity)
    _ = ((2 * Real.pi) * ‖transverseDerivFromH2 j‖) *
          frequencyRadius n ^ 2 * ‖b‖ := by ring

/-- The term `(Δm) b` of the Laplacian product rule, for `m` the unit character at
frequency `n`, is bounded by `2 (2π)² (1 + ‖n‖)² ‖b‖`. -/
theorem norm_monomialLaplacianTerm_le
    (n : TransverseFrequency) (b : TransverseC3H2) :
    ‖scalarVectorMulTransverse
        (polynomialLInf
          (polynomialLaplacian (Finsupp.single n (1 : ℂ))))
        (transverseH2Embedding b)‖ ≤
      (2 * (2 * Real.pi) ^ 2) * frequencyRadius n ^ 2 * ‖b‖ := by
  calc
    ‖scalarVectorMulTransverse
        (polynomialLInf
          (polynomialLaplacian (Finsupp.single n (1 : ℂ))))
        (transverseH2Embedding b)‖ ≤
        ‖polynomialLInf
          (polynomialLaplacian (Finsupp.single n (1 : ℂ)))‖ *
          ‖transverseH2Embedding b‖ :=
      norm_scalarVectorMulTransverse_apply_le _ _
    _ ≤ ((2 * (2 * Real.pi) ^ 2) * frequencyRadius n ^ 2) * ‖b‖ := by
      exact mul_le_mul (norm_monomialLaplacianLInf_le n)
        (norm_transverseH2Embedding_le b) (norm_nonneg _) (by positivity)
    _ = (2 * (2 * Real.pi) ^ 2) * frequencyRadius n ^ 2 * ‖b‖ := rfl

/-- Adding the three product-rule terms gives the quadratic bound
`‖Δ(m b)‖ ≤ laplacianProductGrowthConstant · (1 + ‖n‖)² ‖b‖` for the unit character `m` at
frequency `n`. -/
theorem norm_monomialLaplacianProductMap_apply_le
    (n : TransverseFrequency) (b : TransverseC3H2) :
    ‖polynomialLaplacianProductMap (Finsupp.single n (1 : ℂ)) b‖ ≤
      laplacianProductGrowthConstant * frequencyRadius n ^ 2 * ‖b‖ := by
  rw [polynomialLaplacianProductMap_apply]
  simp only [Fin.sum_univ_two]
  let x := scalarVectorMulTransverse (monomialLInf n)
      (transverseLaplacianFromH2 b)
  let y0 := scalarVectorMulTransverse
      (polynomialLInf
        (polynomialDeriv (0 : Fin 2) (Finsupp.single n (1 : ℂ))))
      (transverseDerivFromH2 (0 : Fin 2) b)
  let y1 := scalarVectorMulTransverse
      (polynomialLInf
        (polynomialDeriv (1 : Fin 2) (Finsupp.single n (1 : ℂ))))
      (transverseDerivFromH2 (1 : Fin 2) b)
  let z := scalarVectorMulTransverse
      (polynomialLInf
        (polynomialLaplacian (Finsupp.single n (1 : ℂ))))
      (transverseH2Embedding b)
  change ‖x + (2 : ℂ) • (y0 + y1) + z‖ ≤ _
  have hx : ‖x‖ ≤
      ‖transverseLaplacianFromH2‖ * frequencyRadius n ^ 2 * ‖b‖ := by
    calc
      ‖x‖ ≤ ‖transverseLaplacianFromH2 b‖ := by
        dsimp [x]
        calc
          ‖scalarVectorMulTransverse (monomialLInf n)
              (transverseLaplacianFromH2 b)‖ ≤
              ‖monomialLInf n‖ * ‖transverseLaplacianFromH2 b‖ :=
            norm_scalarVectorMulTransverse_apply_le _ _
          _ ≤ 1 * ‖transverseLaplacianFromH2 b‖ := by
            gcongr
            exact norm_monomialLInf_le_one n
          _ = ‖transverseLaplacianFromH2 b‖ := one_mul _
      _ ≤ ‖transverseLaplacianFromH2‖ * ‖b‖ :=
        transverseLaplacianFromH2.le_opNorm b
      _ ≤ ‖transverseLaplacianFromH2‖ *
            frequencyRadius n ^ 2 * ‖b‖ := by
        rw [mul_assoc]
        gcongr
        exact le_mul_of_one_le_left (norm_nonneg b)
          (one_le_frequencyRadius_sq n)
  have hy0 : ‖y0‖ ≤
      ((2 * Real.pi) * ‖transverseDerivFromH2 (0 : Fin 2)‖) *
        frequencyRadius n ^ 2 * ‖b‖ := by
    exact norm_monomialDerivTerm_le n (0 : Fin 2) b
  have hy1 : ‖y1‖ ≤
      ((2 * Real.pi) * ‖transverseDerivFromH2 (1 : Fin 2)‖) *
        frequencyRadius n ^ 2 * ‖b‖ := by
    exact norm_monomialDerivTerm_le n (1 : Fin 2) b
  have hz : ‖z‖ ≤
      (2 * (2 * Real.pi) ^ 2) * frequencyRadius n ^ 2 * ‖b‖ := by
    exact norm_monomialLaplacianTerm_le n b
  calc
    ‖x + (2 : ℂ) • (y0 + y1) + z‖ ≤
        ‖x‖ + ‖(2 : ℂ) • (y0 + y1)‖ + ‖z‖ := by
      calc
        ‖x + (2 : ℂ) • (y0 + y1) + z‖ ≤
            ‖x + (2 : ℂ) • (y0 + y1)‖ + ‖z‖ := norm_add_le _ _
        _ ≤ ‖x‖ + ‖(2 : ℂ) • (y0 + y1)‖ + ‖z‖ :=
          add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ‖x‖ + 2 * (‖y0‖ + ‖y1‖) + ‖z‖ := by
      rw [norm_smul, Complex.norm_ofNat]
      gcongr
      exact norm_add_le _ _
    _ ≤
        (‖transverseLaplacianFromH2‖ * frequencyRadius n ^ 2 * ‖b‖) +
          2 *
            ((((2 * Real.pi) * ‖transverseDerivFromH2 (0 : Fin 2)‖) *
                frequencyRadius n ^ 2 * ‖b‖) +
              (((2 * Real.pi) * ‖transverseDerivFromH2 (1 : Fin 2)‖) *
                frequencyRadius n ^ 2 * ‖b‖)) +
          ((2 * (2 * Real.pi) ^ 2) * frequencyRadius n ^ 2 * ‖b‖) := by
      gcongr
    _ = laplacianProductGrowthConstant * frequencyRadius n ^ 2 * ‖b‖ := by
      unfold laplacianProductGrowthConstant
      ring

/-- The fixed constant controlling multiplication by a monomial on the
closed Fourier-graph realization of transverse `H²`. -/
def h2MultiplierGrowthConstant : ℝ :=
  max 1
    (‖transverseC3FourierAnalysisCLM‖ *
      (1 + laplacianProductGrowthConstant))

/-- The `H²` multiplier constant is at least one, since it is defined as a maximum with
`1`. -/
theorem one_le_h2MultiplierGrowthConstant :
    1 ≤ h2MultiplierGrowthConstant := by
  exact le_max_left _ _

/-- The `H²` multiplier constant is nonnegative. -/
theorem h2MultiplierGrowthConstant_nonneg :
    0 ≤ h2MultiplierGrowthConstant :=
  zero_le_one.trans one_le_h2MultiplierGrowthConstant

/-- The second branch of the defining maximum, namely
`‖transverseC3FourierAnalysisCLM‖ * (1 + laplacianProductGrowthConstant)`, is bounded by
`h2MultiplierGrowthConstant`. -/
theorem fourierAnalysis_factor_le_h2MultiplierGrowthConstant :
    ‖transverseC3FourierAnalysisCLM‖ *
        (1 + laplacianProductGrowthConstant) ≤
      h2MultiplierGrowthConstant := by
  exact le_max_right _ _

/-- Multiplication by the unit Fourier character at frequency `n`, on the closed
Fourier-graph realization of transverse `H²`, obeys the quadratic bound
`‖m b‖ ≤ h2MultiplierGrowthConstant · (1 + ‖n‖)² ‖b‖`; both graph components (value and
weighted certificate) are estimated separately. -/
theorem norm_monomialH2Multiplier_apply_le
    (n : TransverseFrequency) (b : TransverseC3H2) :
    ‖polynomialH2Multiplier (Finsupp.single n (1 : ℂ)) b‖ ≤
      h2MultiplierGrowthConstant * frequencyRadius n ^ 2 * ‖b‖ := by
  change ‖polynomialH2GraphMap (Finsupp.single n (1 : ℂ)) b‖ ≤ _
  change ‖(polynomialValueMap (Finsupp.single n (1 : ℂ)) b,
      polynomialWeightedCertificate (Finsupp.single n (1 : ℂ)) b)‖ ≤ _
  rw [Prod.norm_def, max_le_iff]
  constructor
  · exact (norm_monomialValueMap_apply_le n b).trans <| by
      gcongr
      exact le_mul_of_one_le_left (sq_nonneg _)
        one_le_h2MultiplierGrowthConstant
  · rw [polynomialWeightedCertificate_apply]
    calc
      ‖transverseC3FourierAnalysisCLM
          (polynomialValueMap (Finsupp.single n (1 : ℂ)) b -
            polynomialLaplacianProductMap
              (Finsupp.single n (1 : ℂ)) b)‖ ≤
          ‖transverseC3FourierAnalysisCLM‖ *
            ‖polynomialValueMap (Finsupp.single n (1 : ℂ)) b -
              polynomialLaplacianProductMap
                (Finsupp.single n (1 : ℂ)) b‖ :=
        transverseC3FourierAnalysisCLM.le_opNorm _
      _ ≤ ‖transverseC3FourierAnalysisCLM‖ *
          (‖polynomialValueMap (Finsupp.single n (1 : ℂ)) b‖ +
            ‖polynomialLaplacianProductMap
              (Finsupp.single n (1 : ℂ)) b‖) := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ ‖transverseC3FourierAnalysisCLM‖ *
          ((frequencyRadius n ^ 2 * ‖b‖) +
            (laplacianProductGrowthConstant *
              frequencyRadius n ^ 2 * ‖b‖)) := by
        gcongr
        · exact norm_monomialValueMap_apply_le n b
        · exact norm_monomialLaplacianProductMap_apply_le n b
      _ = (‖transverseC3FourierAnalysisCLM‖ *
            (1 + laplacianProductGrowthConstant)) *
          frequencyRadius n ^ 2 * ‖b‖ := by ring
      _ ≤ h2MultiplierGrowthConstant * frequencyRadius n ^ 2 * ‖b‖ := by
        gcongr
        exact fourierAnalysis_factor_le_h2MultiplierGrowthConstant

/-- Operator-norm form of the previous estimate: the `H²` multiplication operator of the
unit character at frequency `n` has norm at most `h2MultiplierGrowthConstant · (1 + ‖n‖)²`. -/
theorem norm_monomialH2Multiplier_le
    (n : TransverseFrequency) :
    ‖polynomialH2Multiplier (Finsupp.single n (1 : ℂ))‖ ≤
      h2MultiplierGrowthConstant * frequencyRadius n ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg h2MultiplierGrowthConstant_nonneg (sq_nonneg _))
  intro b
  exact norm_monomialH2Multiplier_apply_le n b

/-! ## Polynomial growth of the simultaneous package -/

/-- One frequency-independent constant dominating all four components of
the second-order package. -/
def secondOrderPackageGrowthConstant : ℝ :=
  1 + (2 * Real.pi) + 2 * (2 * Real.pi) ^ 2 +
    h2MultiplierGrowthConstant

/-- The single constant dominating all four package components is nonnegative. -/
theorem secondOrderPackageGrowthConstant_nonneg :
    0 ≤ secondOrderPackageGrowthConstant := by
  unfold secondOrderPackageGrowthConstant
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hsq : 0 ≤ 2 * (2 * Real.pi) ^ 2 := by positivity
  have hh := h2MultiplierGrowthConstant_nonneg
  linarith

/-- The single constant dominating all four package components is at least one, which
covers the contractive `L∞` value component. -/
theorem one_le_secondOrderPackageGrowthConstant :
    1 ≤ secondOrderPackageGrowthConstant := by
  unfold secondOrderPackageGrowthConstant
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hsq : 0 ≤ 2 * (2 * Real.pi) ^ 2 := by positivity
  have hh := h2MultiplierGrowthConstant_nonneg
  linarith

/-- The first-derivative factor `2π` is dominated by the common package constant. -/
theorem derivFactor_le_secondOrderPackageGrowthConstant :
    2 * Real.pi ≤ secondOrderPackageGrowthConstant := by
  unfold secondOrderPackageGrowthConstant
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hsq : 0 ≤ 2 * (2 * Real.pi) ^ 2 := by positivity
  have hh := h2MultiplierGrowthConstant_nonneg
  linarith

/-- The Laplacian factor `2 (2π)²` is dominated by the common package constant. -/
theorem laplacianFactor_le_secondOrderPackageGrowthConstant :
    2 * (2 * Real.pi) ^ 2 ≤ secondOrderPackageGrowthConstant := by
  unfold secondOrderPackageGrowthConstant
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hsq : 0 ≤ 2 * (2 * Real.pi) ^ 2 := by positivity
  have hh := h2MultiplierGrowthConstant_nonneg
  linarith

/-- The `H²` multiplier constant is dominated by the common package constant. -/
theorem h2MultiplierGrowthConstant_le_secondOrderPackageGrowthConstant :
    h2MultiplierGrowthConstant ≤ secondOrderPackageGrowthConstant := by
  unfold secondOrderPackageGrowthConstant
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hsq : 0 ≤ 2 * (2 * Real.pi) ^ 2 := by positivity
  linarith

/-- Explicit quadratic growth of the exact simultaneous monomial package. -/
theorem secondOrderFourierWeight_le
    (n : TransverseFrequency) :
    secondOrderFourierWeight n ≤
      secondOrderPackageGrowthConstant * frequencyRadius n ^ 2 := by
  rw [secondOrderFourierWeight]
  simp only [monomialSecondOrderPackage, Prod.norm_def]
  rw [max_le_iff, max_le_iff, max_le_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (norm_monomialLInf_le_one n).trans <| by
      calc
        1 ≤ secondOrderPackageGrowthConstant :=
          one_le_secondOrderPackageGrowthConstant
        _ ≤ secondOrderPackageGrowthConstant * frequencyRadius n ^ 2 := by
          exact le_mul_of_one_le_right secondOrderPackageGrowthConstant_nonneg
            (one_le_frequencyRadius_sq n)
  · apply (pi_norm_le_iff_of_nonneg
      (mul_nonneg secondOrderPackageGrowthConstant_nonneg (sq_nonneg _))).2
    intro j
    exact (norm_monomialDerivLInf_le n j).trans <| by
      gcongr
      exact derivFactor_le_secondOrderPackageGrowthConstant
  · exact (norm_monomialLaplacianLInf_le n).trans <| by
      gcongr
      exact laplacianFactor_le_secondOrderPackageGrowthConstant
  · exact (norm_monomialH2Multiplier_le n).trans <| by
      gcongr
      exact h2MultiplierGrowthConstant_le_secondOrderPackageGrowthConstant

/-- The operator-growth premise holds: the second-order Fourier weight grows polynomially. -/
theorem secondOrderFourierWeight_hasPolynomialGrowth :
    SecondOrderFourierWeightHasPolynomialGrowth := by
  refine ⟨secondOrderPackageGrowthConstant,
    secondOrderPackageGrowthConstant_nonneg, 2, ?_⟩
  intro n
  simpa [frequencyRadius] using secondOrderFourierWeight_le n

/-! ## Exact coefficients of the completed Fourier series -/

/-- The `L∞ → L²` inclusion sends the `L∞` Fourier character at frequency `n` to the `L²`
character `transverseMonomialL2 n`. -/
theorem transverseScalarLInfToL2_monomialLInf
    (n : TransverseFrequency) :
    transverseScalarLInfToL2 (monomialLInf n) =
      transverseMonomialL2 n := by
  apply Lp.ext
  filter_upwards [transverseScalarLInfToL2_coe_ae (monomialLInf n),
    monomialLInf_coe_ae n, transverseMonomialL2_coe_ae n]
      with x hinc hinf hl2
  rw [hinc, hinf, hl2]

/-- Fourier coefficients of a character are the Kronecker delta: the `q`th coefficient of
the character at frequency `n` is `1` if `q = n` and `0` otherwise, by orthonormality of
`transverseScalarFourierBasis`. -/
theorem transverseScalarCoeff_monomialLInf
    (q n : TransverseFrequency) :
    transverseScalarCoeffCLM q
        (transverseScalarLInfToL2 (monomialLInf n)) =
      if q = n then 1 else 0 := by
  rw [transverseScalarLInfToL2_monomialLInf,
    transverseScalarCoeffCLM_eq_inner]
  change inner ℂ (transverseScalarFourierBasis q)
      (transverseScalarFourierBasis n) = _
  exact (orthonormal_iff_ite.mp
    transverseScalarFourierBasis.orthonormal) q n

/-- The value component of the single-frequency package at `(n, c)` has `q`th Fourier
coefficient `c` when `q = n` and `0` otherwise. -/
theorem transverseScalarCoeff_packageValue_coefficient
    (q n : TransverseFrequency) (c : ℂ) :
    transverseScalarCoeffCLM q
        (transverseScalarLInfToL2
          (packageValue (coefficientSecondOrderPackage n c))) =
      if q = n then c else 0 := by
  simp only [packageValue_apply, coefficientSecondOrderPackage]
  rw [polynomialLInf_single, map_smul, map_smul,
    transverseScalarCoeff_monomialLInf]
  split_ifs <;> simp

/-- Coefficient extraction from the value component of the simultaneous
package, as one continuous functional. -/
def packageValueCoeff (q : TransverseFrequency) :
    SecondOrderCutoffPackage →L[ℂ] ℂ :=
  (transverseScalarCoeffCLM q).comp
    (transverseScalarLInfToL2.comp packageValue)

/-- On a single-frequency package the coefficient functional returns the coefficient `c` at
its own frequency and `0` elsewhere; this is the term-by-term input to the sum below. -/
@[simp] theorem packageValueCoeff_coefficient
    (q n : TransverseFrequency) (c : ℂ) :
    packageValueCoeff q (coefficientSecondOrderPackage n c) =
      if q = n then c else 0 := by
  exact transverseScalarCoeff_packageValue_coefficient q n c

/-- The completed value field has exactly the coefficient family from
which it was built.  This identifies the Banach-space sum with its Fourier
series independently of any pointwise periodization theorem. -/
theorem transverseScalarCoeff_completedSecondOrderValue
    (a : TransverseFrequency → ℂ)
    (ha : HasSummableSecondOrderFourierWeight a)
    (q : TransverseFrequency) :
    transverseScalarCoeffCLM q
        (transverseScalarLInfToL2
          (packageValue (completedSecondOrderPackage a))) = a q := by
  change packageValueCoeff q (completedSecondOrderPackage a) = a q
  unfold completedSecondOrderPackage
  rw [(packageValueCoeff q).map_tsum
    (summable_secondOrderPackageSeries ha)]
  rw [tsum_eq_single q]
  · rw [secondOrderPackageSeries, packageValueCoeff_coefficient,
      ite_eq_left rfl]
  · intro n hn
    rw [secondOrderPackageSeries, packageValueCoeff_coefficient]
    exact ite_eq_right (Ne.symm hn)

end TransverseSmoothBumpH2CutoffConcrete

end

end FastDynamo
