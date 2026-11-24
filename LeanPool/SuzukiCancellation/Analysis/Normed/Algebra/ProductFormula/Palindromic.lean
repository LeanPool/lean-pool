/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths and consolidated proofs. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ExponentialList
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.Logarithm
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.BCH.Symmetric
public import Mathlib.Analysis.RCLike.Basic
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SuzukiArguments

/-!
# Palindromic Suzuki products

The eleven exponential arguments of five Strang blocks with weights
`p, p, 1 - 4p, p, p` form a palindrome. The number of blocks does not specify
the approximation order: fourth-order accuracy requires cubic cancellation.
Reflection of the time parameter therefore inverts the product.
Its logarithm exponentiates back to the product on the source convergence domain,
and is odd when both logarithms lie in the local injectivity ball.

## Main definitions

* `fiveStageStrangArguments`: the ordered eleven exponent arguments.
* `fiveStageStrangProduct`: their ordered exponential product, with arbitrary parameter `p`.
* `fiveStageStrangArgNormBound`: the source coefficient bound for the argument norms.
* `fiveStageStrangLog`: the logarithm of the product.
* `strangBlock`: a single symmetric three-factor step.

## Main results

* `fiveStageStrangProduct_mul_neg_eq_one`: reflection gives an inverse.
* `exp_fiveStageStrangLog`: the local exponential/logarithm round trip.
* `fiveStageStrangLog_neg`: local oddness of the logarithm.
* `fiveStageStrangProduct_eq_strangBlock_prod`: the five-block factorization.
* `fiveStageStrangProduct_eq_exp_of_commute`: exactness for commuting generators.
* `log_strangBlock_eq_symmetricBch`: the local symmetric BCH representation of a Strang block.
* `fiveStageStrangLog_neg_of_lt_quarter`: oddness from the coefficient bound alone.
-/

@[expose] public noncomputable section

open NormedSpace

namespace FQFP.BCH

section Definitions

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

variable [TopologicalSpace A] [IsTopologicalRing A]

/-- The ordered eleven-factor Suzuki product, with unrestricted coefficient `p`. -/
def fiveStageStrangProduct (a b : A) (p t : K) : A :=
  ((fiveStageStrangArguments a b p t).map exp).prod

/-- The logarithm of the five-block Suzuki product. -/
def fiveStageStrangLog (a b : A) (p t : K) : A := log (fiveStageStrangProduct a b p t)

/-- A symmetric three-factor Strang step with coefficient `c`, equal to `S₂(c t)`. -/
def strangBlock (a b : A) (c t : K) : A :=
  exp ((c * t / 2) • a) * exp ((c * t) • b) * exp ((c * t / 2) • a)

/-- The argument-list definition agrees with the explicit eleven-factor source product. -/
lemma fiveStageStrangProduct_eq (a b : A) (p t : K) :
    fiveStageStrangProduct a b p t =
      exp ((p / 2 * t) • a) * exp ((p * t) • b) *
      exp ((p * t) • a) * exp ((p * t) • b) *
      exp (((1 - 3 * p) / 2 * t) • a) * exp (((1 - 4 * p) * t) • b) *
      exp (((1 - 3 * p) / 2 * t) • a) * exp ((p * t) • b) *
      exp ((p * t) • a) * exp ((p * t) • b) * exp ((p / 2 * t) • a) := by
  simp [fiveStageStrangProduct, fiveStageStrangArguments, mul_assoc]

/-- At time zero, the product is one. -/
@[simp]
lemma fiveStageStrangProduct_zero (a b : A) (p : K) : fiveStageStrangProduct a b p 0 = 1 := by
  simp [fiveStageStrangProduct, fiveStageStrangArguments]

/-- At time zero, the logarithm is zero. -/
@[simp]
lemma fiveStageStrangLog_zero (a b : A) (p : K) : fiveStageStrangLog a b p 0 = 0 := by
  simp [fiveStageStrangLog]

end Definitions

section NormBounds

variable {K A : Type*} [RCLike K] [NormedRing A]

/-- The source bound on the total norm of the eleven exponent arguments. -/
def fiveStageStrangArgNormBound (a b : A) (p t : K) : ℝ :=
  ‖t‖ * ((3 * ‖p‖ + ‖1 - 3 * p‖) * ‖a‖ + (4 * ‖p‖ + ‖1 - 4 * p‖) * ‖b‖)

/-- The argument-norm bound is nonnegative. -/
lemma fiveStageStrangArgNormBound_nonneg (a b : A) (p t : K) :
    0 ≤ fiveStageStrangArgNormBound a b p t := by
  unfold fiveStageStrangArgNormBound
  positivity

/-- The coefficient bound is unchanged by time reflection. -/
@[simp]
lemma fiveStageStrangArgNormBound_neg (a b : A) (p t : K) :
    fiveStageStrangArgNormBound a b p (-t) = fiveStageStrangArgNormBound a b p t := by
  simp [fiveStageStrangArgNormBound]

variable [NormedAlgebra K A]

/-- The argument norms sum to the source coefficient bound. -/
lemma sum_norm_fiveStageStrangArguments (a b : A) (p t : K) :
    ((fiveStageStrangArguments a b p t).map norm).sum = fiveStageStrangArgNormBound a b p t := by
  simp [fiveStageStrangArguments, fiveStageStrangArgNormBound, norm_smul, norm_mul, norm_div]
  ring

variable [CompleteSpace A]

private lemma exp_smul_mul_exp_smul_mul (a z : A) (x y : K) :
    exp (x • a) * (exp (y • a) * z) = exp ((x + y) • a) * z := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ K A
  rw [← mul_assoc, ← exp_add_of_commute (((Commute.refl a).smul_left x).smul_right y),
    ← add_smul]

/-- Five Strang blocks merge to the eleven-factor Suzuki product. -/
theorem fiveStageStrangProduct_eq_strangBlock_prod (a b : A) (p t : K) :
    fiveStageStrangProduct a b p t =
      strangBlock a b p t * strangBlock a b p t * strangBlock a b (1 - 4 * p) t *
      strangBlock a b p t * strangBlock a b p t := by
  have hpp : p * t / 2 + p * t / 2 = p * t := by ring
  have hpq : p * t / 2 + (1 - 4 * p) * t / 2 = (1 - 3 * p) / 2 * t := by ring
  have hqp : (1 - 4 * p) * t / 2 + p * t / 2 = (1 - 3 * p) / 2 * t := by ring
  simp only [fiveStageStrangProduct_eq, strangBlock, mul_assoc]
  rw [exp_smul_mul_exp_smul_mul a, hpp, exp_smul_mul_exp_smul_mul a, hpq,
    exp_smul_mul_exp_smul_mul a, hqp, exp_smul_mul_exp_smul_mul a, hpp]
  rw [div_mul_eq_mul_div]

/-- A Strang block is exact when its two generators commute. -/
theorem strangBlock_eq_exp_of_commute (a b : A) (hab : Commute a b) (c t : K) :
    strangBlock a b c t = exp ((c * t) • (a + b)) := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ K A
  rw [strangBlock, ← exp_add_of_commute ((hab.smul_left (c * t / 2)).smul_right (c * t))]
  rw [← exp_add_of_commute
    (((Commute.refl a).smul_left (c * t / 2)).smul_right (c * t / 2) |>.add_left
      ((hab.symm.smul_left (c * t)).smul_right (c * t / 2)))]
  congr 1
  module

/-- The five-block product is exact for commuting generators, for every coefficient and time. -/
theorem fiveStageStrangProduct_eq_exp_of_commute (a b : A) (hab : Commute a b) (p t : K) :
    fiveStageStrangProduct a b p t = exp (t • (a + b)) := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ K A
  have hmul (x y : K) : exp (x • (a + b)) * exp (y • (a + b)) =
      exp ((x + y) • (a + b)) := by
    rw [← exp_add_of_commute (((Commute.refl (a + b)).smul_left x).smul_right y),
      ← add_smul]
  rw [fiveStageStrangProduct_eq_strangBlock_prod]
  simp only [strangBlock_eq_exp_of_commute a b hab, hmul]
  congr 2
  ring

/-- The product at reflected time is a right inverse, without smallness assumptions. -/
theorem fiveStageStrangProduct_mul_neg_eq_one (a b : A) (p t : K) :
    fiveStageStrangProduct a b p t * fiveStageStrangProduct a b p (-t) = 1 := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ K A
  simpa only [fiveStageStrangProduct, fiveStageStrangArguments_neg, List.map_map,
    fiveStageStrangArguments_reverse, Function.comp_def] using
    prod_exp_mul_reverse_neg_eq_one (fiveStageStrangArguments a b p t)

/-- The product at reflected time is also a left inverse. -/
theorem fiveStageStrangProduct_neg_mul_eq_one (a b : A) (p t : K) :
    fiveStageStrangProduct a b p (-t) * fiveStageStrangProduct a b p t = 1 := by
  simpa only [neg_neg] using fiveStageStrangProduct_mul_neg_eq_one a b p (-t)

variable [NormOneClass A]

/-- A small Strang block has the same logarithm as the nested symmetric BCH element. -/
theorem log_strangBlock_eq_symmetricBch (a b : A) (c t : K)
    (h : ‖((2 : K)⁻¹ * (c * t)) • a‖ + ‖(c * t) • b‖ < Real.log 2) :
    letI : NormedAlgebra ℚ A := .restrictScalars ℚ K A
    log (strangBlock a b c t) = symmetricBch ((c * t) • a) ((c * t) • b) := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ K A
  have hhalf : (2 : ℚ)⁻¹ • ((c * t) • a) = (c * t / 2) • a := by
    change (algebraMap ℚ K (2 : ℚ)⁻¹) • ((c * t) • a) = _
    norm_num
    rw [smul_smul]
    congr 1
    ring
  rw [symmetricBch_eq_log_exp_mul_exp_mul_exp]
  · rw [hhalf, strangBlock]
  · simpa only [hhalf, inv_mul_eq_div] using h

/-- The scalar majorant for the distance of the Suzuki product from one. -/
theorem norm_fiveStageStrangProduct_sub_one_le (a b : A) (p t : K) :
    ‖fiveStageStrangProduct a b p t - 1‖ ≤ Real.exp (fiveStageStrangArgNormBound a b p t) - 1 := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ K A
  simpa only [fiveStageStrangProduct, sum_norm_fiveStageStrangArguments] using
    norm_prod_exp_sub_one_le (fiveStageStrangArguments a b p t)

/-- The source coefficient regime puts the Suzuki product inside the logarithm ball. -/
theorem norm_fiveStageStrangProduct_sub_one_lt_one (a b : A) (p t : K)
    (h : fiveStageStrangArgNormBound a b p t < Real.log 2) :
    ‖fiveStageStrangProduct a b p t - 1‖ < 1 := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ K A
  exact norm_prod_exp_sub_one_lt_one _ (by rwa [sum_norm_fiveStageStrangArguments])

/-- The exponential of the Suzuki logarithm equals the product on the source domain. -/
theorem exp_fiveStageStrangLog (a b : A) (p t : K)
    (h : fiveStageStrangArgNormBound a b p t < Real.log 2) :
    exp (fiveStageStrangLog a b p t) = fiveStageStrangProduct a b p t := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ K A
  exact exp_log (norm_fiveStageStrangProduct_sub_one_lt_one a b p t h)

/-- The Suzuki logarithm is odd on the source local injectivity domain. -/
theorem fiveStageStrangLog_neg (a b : A) (p t : K)
    (h : fiveStageStrangArgNormBound a b p t < Real.log 2)
    (ht : ‖fiveStageStrangLog a b p t‖ < Real.log 2)
    (hnt : ‖fiveStageStrangLog a b p (-t)‖ < Real.log 2) :
    fiveStageStrangLog a b p (-t) = -fiveStageStrangLog a b p t := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ K A
  have hprod : exp (fiveStageStrangLog a b p t) * exp (fiveStageStrangLog a b p (-t)) = 1 := by
    rw [exp_fiveStageStrangLog a b p t h, exp_fiveStageStrangLog a b p (-t) (by simpa using h)]
    exact fiveStageStrangProduct_mul_neg_eq_one a b p t
  have heq : exp (fiveStageStrangLog a b p (-t)) = exp (-fiveStageStrangLog a b p t) := by
    calc
      _ = (exp (-fiveStageStrangLog a b p t) * exp (fiveStageStrangLog a b p t)) *
          exp (fiveStageStrangLog a b p (-t)) := by
        rw [TrotterError.exp_neg_mul_self, one_mul]
      _ = _ := by rw [mul_assoc, hprod, mul_one]
  calc
    _ = log (exp (fiveStageStrangLog a b p (-t))) := (log_exp_of_norm_lt _ hnt).symm
    _ = log (exp (-fiveStageStrangLog a b p t)) := congrArg log heq
    _ = _ := log_exp_of_norm_lt _ (by simpa only [norm_neg] using ht)

/-- A quarter-radius coefficient bound also puts the logarithm in its injectivity ball. -/
theorem norm_fiveStageStrangLog_lt_log_two (a b : A) (p t : K)
    (h : fiveStageStrangArgNormBound a b p t < 1 / 4) :
    ‖fiveStageStrangLog a b p t‖ < Real.log 2 := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ K A
  have hd := eleven_sixteenths_le_two_sub_exp (fiveStageStrangArgNormBound_nonneg a b p t) h le_rfl
  have hb := norm_fiveStageStrangProduct_sub_one_le a b p t
  have hn : ‖fiveStageStrangProduct a b p t - 1‖ ≤ 5 / 16 := by linarith only [hd, hb]
  have hl := norm_log_one_add_le (fiveStageStrangProduct a b p t - 1)
    (by linarith only [hn] : ‖fiveStageStrangProduct a b p t - 1‖ < 1)
  rw [← add_sub_assoc, add_sub_cancel_left] at hl
  apply lt_of_le_of_lt (hl.trans ?_) half_lt_log_two
  apply (div_le_iff₀ (by linarith only [hn])).mpr
  linarith only [hn]

/-- On the quarter-radius coefficient domain the Suzuki logarithm is odd. -/
theorem fiveStageStrangLog_neg_of_lt_quarter (a b : A) (p t : K)
    (h : fiveStageStrangArgNormBound a b p t < 1 / 4) :
    fiveStageStrangLog a b p (-t) = -fiveStageStrangLog a b p t :=
  fiveStageStrangLog_neg a b p t (h.trans (by linarith only [half_lt_log_two]))
    (norm_fiveStageStrangLog_lt_log_two a b p t h)
    (norm_fiveStageStrangLog_lt_log_two a b p (-t)
      (by simpa only [fiveStageStrangArgNormBound_neg] using h))

end NormBounds

end FQFP.BCH
