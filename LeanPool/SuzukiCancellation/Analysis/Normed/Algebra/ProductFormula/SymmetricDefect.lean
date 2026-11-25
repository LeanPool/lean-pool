/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ExponentialListTaylor
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ExponentialConjugation
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.SymmetricDuhamel
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.GroupedConjugation

/-!
# Symmetric defects of ordered exponential products

An arbitrary ordered half-list determines a symmetric exponential product. Its
defect factors through the sum of a half-defect at opposite times. All inverses
are explicit reversed exponential products, so no division-ring structure is used.

## Main definitions

* `expListProduct`: the ordered half-product.
* `expListLogDeriv`: its logarithmic derivative `U⁻¹U'`.
* `halfDefect`: the transported half-defect.
* `symmetricDefect`: the symmetric residual of the full product.

## Main results

* `symmetricDefect_eq_halfDefect_add`: transport of the even middle defect.
* `halfDefect_eq_groupedConj`: the conjugation recurrence with generator kicks.
* `symmetricExpProduct_sub_exp_eq_integral`: the two-sided Duhamel identity.
-/

@[expose] public noncomputable section

open NormedSpace TrotterError MeasureTheory
open scoped RealScalar ContDiff

namespace FQFP

variable {A : Type*} [NormedRing A]

section

variable [NormedAlgebra ℝ A]

/-- The ordered exponential product of a finite generator list. -/
def expListProduct (l : List A) (t : ℝ) : A :=
  (l.map fun a ↦ exp (t • a)).prod

/-- The logarithmic derivative `U⁻¹U'`, using the explicit inverse product. -/
def expListLogDeriv (l : List A) (t : ℝ) : A :=
  expListProduct l.reverse (-t) * deriv (expListProduct l) t

/-- Transport of an algebra element into the half-product's moving frame. -/
def expListConj (l : List A) (B : A) (t : ℝ) : A :=
  expListProduct l.reverse (-t) * B * expListProduct l t

/-- The half-defect associated with a prescribed total generator. -/
def halfDefect (l : List A) (G : A) (t : ℝ) : A :=
  expListLogDeriv l t - (1 / 2 : ℝ) • expListConj l G t

/-- The symmetric product formed by a half-list and its reversal. -/
def symmetricExpProduct (l : List A) (t : ℝ) : A :=
  expListProduct l t * expListProduct l.reverse t

/-- The symmetric differential residual for a prescribed total generator. -/
def symmetricDefect (l : List A) (G : A) (t : ℝ) : A :=
  deriv (symmetricExpProduct l) t -
    (1 / 2 : ℝ) • (G * symmetricExpProduct l t + symmetricExpProduct l t * G)

@[simp] lemma expListProduct_nil (t : ℝ) : expListProduct ([] : List A) t = 1 := rfl

lemma expListProduct_singleton (a : A) (t : ℝ) :
    expListProduct [a] t = exp (t • a) := by simp [expListProduct]

@[simp] lemma expListProduct_cons (a : A) (l : List A) (t : ℝ) :
    expListProduct (a :: l) t = exp (t • a) * expListProduct l t := rfl

@[simp] lemma expListProduct_zero (l : List A) : expListProduct l 0 = 1 := by
  simp [expListProduct]

/-- Concatenation preserves the order of exponential multiplication. -/
lemma expListProduct_append (l m : List A) (t : ℝ) :
    expListProduct (l ++ m) t = expListProduct l t * expListProduct m t := by
  simp [expListProduct]

end

variable [NormedAlgebra ℚ A] [CompleteSpace A]

/-- The explicit reversed negative product is a right inverse. -/
lemma expListProduct_mul_reverse_neg (l : List A) (t : ℝ) :
    expListProduct l t * expListProduct l.reverse (-t) = 1 := by
  simpa [expListProduct, List.map_reverse, List.map_map, Function.comp_def, neg_smul] using
    prod_exp_mul_reverse_neg_eq_one (l.map fun a ↦ t • a)

/-- The explicit reversed negative product is a left inverse. -/
lemma expListProduct_reverse_neg_mul (l : List A) (t : ℝ) :
    expListProduct l.reverse (-t) * expListProduct l t = 1 := by
  simpa using expListProduct_mul_reverse_neg l.reverse (-t)

/-- Every ordered exponential product is smooth. -/
lemma contDiff_expListProduct (l : List A) : ContDiff ℝ ∞ (expListProduct l) :=
  contDiff_prod_exp_smul l

/-- The derivative of an ordered exponential product exists at every real time. -/
lemma hasDerivAt_expListProduct (l : List A) (t : ℝ) :
    HasDerivAt (expListProduct l) (deriv (expListProduct l) t) t :=
  ((contDiff_expListProduct l).differentiable (by simp)).differentiableAt.hasDerivAt

/-- Multiplying the logarithmic derivative by the product recovers its derivative. -/
lemma expListProduct_mul_logDeriv (l : List A) (t : ℝ) :
    expListProduct l t * expListLogDeriv l t = deriv (expListProduct l) t := by
  rw [expListLogDeriv, ← mul_assoc, expListProduct_mul_reverse_neg, one_mul]

/-- The reversed half-product has the reflected logarithmic derivative on its left. -/
lemma deriv_reverse_expListProduct (l : List A) (t : ℝ) :
    deriv (expListProduct l.reverse) t = expListLogDeriv l (-t) * expListProduct l.reverse t := by
  have hprod := ((hasDerivAt_expListProduct l (-t)).scomp t (hasDerivAt_neg t)).mul
    (hasDerivAt_expListProduct l.reverse t)
  have heq : (fun x : ℝ ↦ expListProduct l (-x) * expListProduct l.reverse x) =
      fun _ ↦ (1 : A) := by
    funext x
    simpa using expListProduct_mul_reverse_neg l (-x)
  have hzero := hprod.deriv
  change deriv (fun x : ℝ ↦ expListProduct l (-x) * expListProduct l.reverse x) t =
    _ at hzero
  rw [heq, deriv_const] at hzero
  simp only [Function.comp_apply, neg_one_smul, neg_mul] at hzero
  have hc := congrArg (fun z ↦ expListProduct l.reverse t * z) hzero
  simp only [mul_add, mul_neg, ← mul_assoc,
    show expListProduct l.reverse t * expListProduct l (-t) = 1 from
      by simpa using expListProduct_reverse_neg_mul l (-t), one_mul, mul_zero] at hc
  dsimp [expListLogDeriv]
  simpa [mul_assoc] using (neg_add_eq_zero.mp hc.symm).symm

/-- The symmetric exponential product is smooth. -/
lemma contDiff_symmetricExpProduct (l : List A) :
    ContDiff ℝ ∞ (symmetricExpProduct l) :=
  (contDiff_expListProduct l).mul (contDiff_expListProduct l.reverse)

@[simp] lemma symmetricExpProduct_zero (l : List A) : symmetricExpProduct l 0 = 1 := by
  simp [symmetricExpProduct]

/-- Exact derivative of the full symmetric product in its moving frame. -/
lemma hasDerivAt_symmetricExpProduct (l : List A) (t : ℝ) :
    HasDerivAt (symmetricExpProduct l)
      (expListProduct l t * (expListLogDeriv l t + expListLogDeriv l (-t)) *
        expListProduct l.reverse t) t := by
  convert (hasDerivAt_expListProduct l t).mul
    (hasDerivAt_expListProduct l.reverse t) using 1
  · rfl
  · rw [deriv_reverse_expListProduct, ← expListProduct_mul_logDeriv l t]
    noncomm_ring

/-- The symmetric defect is obtained by transporting an even half-defect. -/
theorem symmetricDefect_eq_halfDefect_add (l : List A) (G : A) (t : ℝ) :
    symmetricDefect l G t =
      expListProduct l t * (halfDefect l G t + halfDefect l G (-t)) *
        expListProduct l.reverse t := by
  rw [symmetricDefect, (hasDerivAt_symmetricExpProduct l t).deriv]
  simp only [halfDefect, expListConj, neg_neg,
    mul_add, mul_sub, add_mul, sub_mul, smul_mul_assoc, mul_smul_comm]
  simp only [← mul_assoc, expListProduct_mul_reverse_neg, one_mul]
  have hc : expListProduct l (-t) * expListProduct l.reverse t = 1 := by
    simpa using expListProduct_mul_reverse_neg l (-t)
  simp only [mul_assoc, hc, mul_one, symmetricExpProduct, smul_add]
  module

/-- The middle factor of the symmetric defect is even. -/
lemma halfDefect_add_reflected_neg (l : List A) (G : A) (t : ℝ) :
    halfDefect l G (-t) + halfDefect l G (-(-t)) =
      halfDefect l G t + halfDefect l G (-t) := by
  simp only [neg_neg, add_comm]

/-- Appending a factor conjugates the logarithmic derivative and adds its generator. -/
lemma expListLogDeriv_append_singleton (l : List A) (a : A) (t : ℝ) :
    expListLogDeriv (l ++ [a]) t = expSMulConj (-a) (expListLogDeriv l t) t + a := by
  have hd : deriv (expListProduct (l ++ [a])) t =
      deriv (expListProduct l) t * exp (t • a) +
        expListProduct l t * (a * exp (t • a)) := by
    have heq : expListProduct (l ++ [a]) =
        fun x ↦ expListProduct l x * exp (x • a) := by
      funext x
      simp [expListProduct_append]
    rw [heq]
    exact ((hasDerivAt_expListProduct l t).mul (hasDerivAt_exp_smul_const' a t)).deriv
  have ha : exp ((-t) • a) * a = a * exp ((-t) • a) :=
    ((Commute.refl a).smul_left (-t)).exp_left.eq
  simp only [expListLogDeriv, hd, List.reverse_append, List.reverse_singleton,
    expListProduct_append, expListProduct_singleton, expSMulConj, smul_neg]
  rw [mul_add]
  congr 1
  · simp only [neg_smul, neg_neg, mul_assoc]
  · rw [mul_assoc, ← mul_assoc (expListProduct l.reverse (-t)),
      expListProduct_reverse_neg_mul, one_mul]
    rw [← mul_assoc, ha, mul_assoc, neg_smul, exp_neg_mul_self, mul_one]

/-- Appending a factor conjugates the transported generator. -/
lemma expListConj_append_singleton (l : List A) (a B : A) (t : ℝ) :
    expListConj (l ++ [a]) B t = expSMulConj (-a) (expListConj l B t) t := by
  simp [expListConj, List.reverse_append, expListProduct_append,
    expSMulConj, mul_assoc]

/-- A half-defect follows the conjugation recurrence with generator kicks. -/
lemma halfDefect_append_singleton (l : List A) (a G : A) (t : ℝ) :
    halfDefect (l ++ [a]) G t = expSMulConj (-a) (halfDefect l G t) t + a := by
  rw [halfDefect, expListLogDeriv_append_singleton, expListConj_append_singleton]
  simp only [halfDefect, expSMulConj, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
  abel

/-- The half-defect is the finite conjugation recurrence starting at `-G/2`. -/
theorem halfDefect_eq_foldl (l : List A) (G : A) (t : ℝ) :
    halfDefect l G t =
      l.foldl (fun B a ↦ expSMulConj (-a) B t + a) (-(1 / 2 : ℝ) • G) := by
  induction l using List.reverseRecOn with
  | nil =>
      simp [halfDefect, expListLogDeriv, expListConj,
        show expListProduct ([] : List A) = fun _ ↦ (1 : A) from rfl]
  | append_singleton l a ih =>
      rw [halfDefect_append_singleton, List.foldl_append, ih]
      rfl

/-- The grouped conjugation mechanism computes the actual logarithmic half-defect. -/
theorem halfDefect_eq_groupedConj {s : ℕ} (Z : Fin s → A) (G : A) (t : ℝ) :
    halfDefect (List.ofFn Z) G t =
      groupedConj (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) t := by
  rw [halfDefect_eq_foldl, groupedConj_eq_foldl]
  have hp : List.ofFn (fun i ↦ (-Z i, Z i)) =
      (List.ofFn Z).map (fun a ↦ (-a, a)) := by
    rw [List.map_ofFn]
    rfl
  rw [hp, List.foldl_map]

/-- The half-defect's constant value is the half-list sum minus half the generator. -/
lemma halfDefect_zero {s : ℕ} (Z : Fin s → A) (G : A) :
    halfDefect (List.ofFn Z) G 0 = ∑ i, Z i - (1 / 2 : ℝ) • G := by
  rw [halfDefect_eq_groupedConj, groupedConj_zero]
  module

/-- The prescribed consistency condition cancels the constant half-defect. -/
lemma halfDefect_zero_of_sum_eq {s : ℕ} (Z : Fin s → A) (G : A)
    (hZ : ∑ i, Z i = (1 / 2 : ℝ) • G) :
    halfDefect (List.ofFn Z) G 0 = 0 := by
  rw [halfDefect_zero, hZ, sub_self]

/-- The symmetric defect is continuous on the whole real line. -/
lemma continuous_symmetricDefect (l : List A) (G : A) :
    Continuous (symmetricDefect l G) := by
  exact ((contDiff_symmetricExpProduct l).continuous_deriv (by simp)).sub
    (((continuous_const.mul (contDiff_symmetricExpProduct l).continuous).add
      ((contDiff_symmetricExpProduct l).continuous.mul continuous_const)).const_smul _)

/-- The transported symmetric defect is integrable for every real endpoint. -/
theorem symmetricDefect_integrable (l : List A) (G : A) (h : ℝ) :
    IntervalIntegrable (fun x ↦ exp (((h - x) / 2) • G) * symmetricDefect l G x *
      exp (((h - x) / 2) • G)) volume 0 h := by
  have he : Continuous (fun x : ℝ ↦ exp (((h - x) / 2) • G)) :=
    (contDiff_exp_smul_const G).continuous.comp
      ((continuous_const.sub continuous_id).div_const 2)
  exact ((he.mul (continuous_symmetricDefect l G)).mul he).intervalIntegrable 0 h

/-- **Symmetric Duhamel identity** for an arbitrary finite half-list and real step. -/
theorem symmetricExpProduct_sub_exp_eq_integral (l : List A) (G : A) (h : ℝ) :
    symmetricExpProduct l h - exp (h • G) =
      ∫ x in 0..h, exp (((h - x) / 2) • G) * symmetricDefect l G x *
        exp (((h - x) / 2) • G) := by
  have hs (x : ℝ) : HasDerivAt (symmetricExpProduct l)
      (deriv (symmetricExpProduct l) x) x :=
    ((contDiff_symmetricExpProduct l).differentiable (by simp)).differentiableAt.hasDerivAt
  have hduhamel := sub_exp_eq_integral_symmetricResidual ((1 / 2 : ℝ) • G) hs
    ((contDiff_symmetricExpProduct l).continuous_deriv (by simp))
    (symmetricExpProduct_zero l) h
  simpa only [symmetricDefect, smul_smul, mul_one_div, mul_div_cancel_left₀ _ (by norm_num :
    (2 : ℝ) ≠ 0), smul_mul_assoc, mul_smul_comm, smul_add] using hduhamel

end FQFP
