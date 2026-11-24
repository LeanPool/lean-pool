/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths and consolidated proofs. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SymmetricLocalError
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.HalfDefectConjugation
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.CommutatorQuadratic

/-!
# Centered local errors of symmetric exponential products

Centering the Duhamel integral preserves the complete quintic Lie polynomial.
A second-order conjugation remainder controls its change of frame.

## Main definitions

* `centeredConjugationList`: the centered generators, in innermost-to-outermost order.
* `centeredConjugationConstant`: their original quadratic commutator constant.
* `centeredSymmetricDefect`: the defect transported to the centered frame.

## Main results

* `conjCoeff_zero`: the constant coefficient is the transported element.
* `conjCoeff_one`: the linear coefficient is the bracket with the generator sum.
* `centeredConjugationConstant_eq_sum`: the original diagonal and mixed bracket formula.
* `norm_centered_half_transport_sub_conjugation_le`: the local error bounds the transport error.
* `norm_centered_symmetricExpProduct_sub_quintic_le`: the centered local error bound.
-/

@[expose] public noncomputable section

open NormedSpace TrotterError MeasureTheory Finset
open scoped RealScalar algebraMap

namespace TrotterError

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The constant coefficient of an ordered conjugation is its initial value. -/
@[simp] lemma conjCoeff_zero {s : ℕ} (Z : Fin s → A) (B : A) :
    conjCoeff Z B 0 = B := by
  induction s with
  | zero => simp [conjCoeff, finAntidiagonal_zero]
  | succ s ih => simp [conjCoeff_succ, ih]

/-- The linear coefficient is the bracket with the sum of all generators. -/
lemma conjCoeff_one {s : ℕ} (Z : Fin s → A) (B : A) :
    conjCoeff Z B 1 = ⁅∑ i, Z i, B⁆ := by
  induction s with
  | zero => simp [conjCoeff, finAntidiagonal_zero, Ring.lie_def]
  | succ s ih =>
      rw [conjCoeff_succ]
      simp only [Nat.reduceAdd, sum_range_succ, range_one, sum_singleton,
        Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, tsub_zero, ih,
        Ring.lie_def, sum_mul, mul_sum, one_apply_eq_self, one_smul,
        Nat.factorial_one, pow_one, tsub_self, conjCoeff_zero, LieAlgebra.ad_apply,
        Fin.sum_univ_castSucc]
      simp only [← Finset.sum_mul, ← Finset.mul_sum]
      noncomm_ring

end TrotterError

namespace FQFP

/-- The innermost-to-outermost generators of the centered half-product. -/
def centeredConjugationList {A : Type*} [SMul ℝ A] (l : List A) (G : A) : List A :=
  l.reverse ++ [-(1 / 2 : ℝ) • G]

/-- Consistency cancels the linear centered-conjugation coefficient. -/
lemma conjCoeff_centeredConjugationList_one {A : Type*} [Ring A] [Algebra ℝ A]
    (l : List A) (G B : A)
    (hsum : l.sum = (1 / 2 : ℝ) • G) :
    conjCoeff (centeredConjugationList l G).get B 1 = 0 := by
  rw [conjCoeff_one]
  have hs : ∑ i, (centeredConjugationList l G).get i = 0 := by
    rw [← List.sum_ofFn, List.ofFn_get]
    simp [centeredConjugationList, hsum]
  rw [hs]
  simp [Ring.lie_def]

section Definitions

variable {A : Type*} [NormedRing A] [Algebra ℝ A]

/-- The original second-order multinomial commutator constant for the centered frame. -/
def centeredConjugationConstant (l : List A) (G L : A) : ℝ :=
  αCommConj (centeredConjugationList l G).get L 2

/-- Every term in the centered commutator constant is nonnegative. -/
lemma centeredConjugationConstant_nonneg (l : List A) (G L : A) :
    0 ≤ centeredConjugationConstant l G L := by
  unfold centeredConjugationConstant αCommConj
  positivity

/-- The centered constant is exactly the diagonal double-bracket sum plus twice
the ordered off-diagonal double-bracket sum in the paper. -/
theorem centeredConjugationConstant_eq_sum (l : List A) (G L : A) :
    let W := (centeredConjugationList l G).get
    centeredConjugationConstant l G L =
      (∑ i, ‖⁅W i, ⁅W i, L⁆⁆‖) +
        2 * ∑ i, ∑ j ∈ univ.filter (fun j ↦ i < j), ‖⁅W j, ⁅W i, L⁆⁆‖ :=
  αCommConj_two_eq_sum _ _

end Definitions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- The centered half-product conjugation has its natural ordered-list representation. -/
lemma multiConj_centeredConjugationList (l : List A) (G B : A) (x : ℝ) :
    multiConj (centeredConjugationList l G).get B x =
      exp ((-x / 2) • G) * expListProduct l x * B *
        expListProduct l.reverse (-x) * exp ((x / 2) • G) := by
  simp only [multiConj, List.get_eq_getElem]
  rw [List.ofFn_getElem_eq_map (centeredConjugationList l G) (fun a ↦ exp (x • a)),
    List.ofFn_getElem_eq_map (centeredConjugationList l G) (fun a ↦ exp ((-x) • a))]
  simp only [centeredConjugationList, List.map_append, List.map_reverse,
    List.map_cons, List.map_nil, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.reverse_reverse, List.prod_append,
    List.prod_cons, List.prod_nil, mul_one, smul_smul, expListProduct]
  rw [show x * -(1 / 2 : ℝ) = -x / 2 by ring,
    show -x * -(1 / 2 : ℝ) = x / 2 by ring]
  noncomm_ring

/-- Centered half-generators inherit the two-sided exponential bounds. -/
lemma norm_exp_smul_centeredConjugationList_le_one (l : List A) (G : A)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1)
    (i : Fin (centeredConjugationList l G).length) (u : ℝ) :
    ‖exp (u • (centeredConjugationList l G).get i)‖ ≤ 1 := by
  have hi := List.get_mem (centeredConjugationList l G) i
  simp only [centeredConjugationList, List.mem_append, List.mem_reverse,
    List.mem_singleton] at hi
  rcases hi with hi | hi
  · exact hZ _ hi u
  · change ‖exp (u • (l.reverse ++ [-(1 / 2 : ℝ) • G]).get i)‖ ≤ 1
    rw [hi, smul_smul]
    exact hG _

/-- The centered change of frame has a second-order error with the original commutator constant. -/
theorem norm_centeredConjugation_sub_le (l : List A) (G L : A)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1)
    (hsum : l.sum = (1 / 2 : ℝ) • G) (x : ℝ) :
    ‖exp ((-x / 2) • G) * expListProduct l x * L *
      expListProduct l.reverse (-x) * exp ((x / 2) • G) - L‖ ≤
      x ^ 2 / 2 * centeredConjugationConstant l G L := by
  have hb := norm_multiConj_sub_sum_le_of_le_one
    (centeredConjugationList l G).get L 2 (by norm_num) x
    (norm_exp_smul_centeredConjugationList_le_one l G hZ hG)
  rw [multiConj_centeredConjugationList] at hb
  simp only [sum_range_succ, sum_range_zero, zero_add, conjCoeff_zero,
    conjCoeff_centeredConjugationList_one l G L hsum, zero_mul, add_zero,
    pow_zero, mul_one] at hb
  norm_num only [Nat.factorial, Nat.cast_ofNat, sq_abs] at hb
  convert hb using 1
  simp only [centeredConjugationConstant]
  ring

end FQFP

namespace FQFP

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- Centering the exact exponential gives the identity. -/
lemma exp_neg_half_mul_exp_mul_exp_neg_half (G : A) (x : ℝ) :
    exp ((-x / 2) • G) * exp (x • G) * exp ((-x / 2) • G) = 1 := by
  rw [exp_smul_mul_exp_smul, exp_smul_mul_exp_smul]
  simp [show -x / 2 + x + -x / 2 = 0 by ring]

/-- The centered symmetric product minus one has exactly the original local-error norm. -/
lemma norm_centered_symmetricExpProduct_sub_one (l : List A) (G : A)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1) (x : ℝ) :
    ‖exp ((-x / 2) • G) * symmetricExpProduct l x * exp ((-x / 2) • G) - 1‖ =
      ‖symmetricExpProduct l x - exp (x • G)‖ := by
  rw [← exp_neg_half_mul_exp_mul_exp_neg_half G x, ← sub_mul, ← mul_sub,
    norm_mul_exp_smul_eq_of_le_one G _ hG, norm_exp_smul_mul_eq_of_le_one G _ hG]

/-- The centered half-transport differs from its conjugation by at most the
local distance times the norm of its input. -/
theorem norm_centered_half_transport_sub_conjugation_le (l : List A) (G B : A)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1) (x : ℝ) :
    ‖exp ((-x / 2) • G) * expListProduct l x * B *
        expListProduct l.reverse x * exp ((-x / 2) • G) -
      multiConj (centeredConjugationList l G).get B x‖ ≤
        ‖B‖ * ‖symmetricExpProduct l x - exp (x • G)‖ := by
  let R := multiConj (centeredConjugationList l G).get B x
  let J := exp ((-x / 2) • G) * symmetricExpProduct l x * exp ((-x / 2) • G)
  have heq : exp ((-x / 2) • G) * expListProduct l x * B *
      expListProduct l.reverse x * exp ((-x / 2) • G) = R * J := by
    dsimp [R, J]
    rw [multiConj_centeredConjugationList]
    dsimp only [symmetricExpProduct]
    simp only [mul_assoc]
    rw [← mul_assoc (exp ((x / 2) • G)), exp_smul_mul_exp_smul,
      show x / 2 + -x / 2 = 0 by ring, zero_smul, exp_zero, one_mul]
    rw [← mul_assoc (expListProduct l.reverse (-x)), expListProduct_reverse_neg_mul, one_mul]
  have hn : ‖R‖ = ‖B‖ := norm_multiConj_eq_of_le_one _ B
    (norm_exp_smul_centeredConjugationList_le_one l G hZ hG) x
  rw [heq, show R * J - R = R * (J - 1) by rw [mul_sub, mul_one]]
  exact (norm_mul_le _ _).trans_eq (by rw [hn,
    norm_centered_symmetricExpProduct_sub_one l G hG x])

/-- Transporting the leading defect differs from the untransported element by a
quadratic commutator term and the original local error, with no product of remainders. -/
theorem norm_centered_half_transport_sub_le (l : List A) (G L : A)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1)
    (hsum : l.sum = (1 / 2 : ℝ) • G) (x : ℝ) :
    ‖exp ((-x / 2) • G) * expListProduct l x * L *
      expListProduct l.reverse x * exp ((-x / 2) • G) - L‖ ≤
      x ^ 2 / 2 * centeredConjugationConstant l G L +
        ‖L‖ * ‖symmetricExpProduct l x - exp (x • G)‖ := by
  have htransport := norm_centered_half_transport_sub_conjugation_le l G L hZ hG x
  have hconj := norm_centeredConjugation_sub_le l G L hZ hG hsum x
  rw [← multiConj_centeredConjugationList] at hconj
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    ((add_le_add htransport hconj).trans_eq (add_comm _ _))

end FQFP

namespace FQFP

/-- The Duhamel integrand in the centered frame. -/
def centeredSymmetricDefect {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (l : List A) (G : A) (x : ℝ) : A :=
  exp ((-x / 2) • G) * symmetricDefect l G x * exp ((-x / 2) • G)

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- The centered defect is continuous. -/
lemma continuous_centeredSymmetricDefect (l : List A) (G : A) :
    Continuous (centeredSymmetricDefect l G) := by
  have he : Continuous (fun x : ℝ ↦ exp ((-x / 2) • G)) :=
    (contDiff_exp_smul_const G).continuous.comp ((continuous_id.neg).div_const 2)
  exact (he.mul (continuous_symmetricDefect l G)).mul he

/-- Centered Duhamel identity, obtained directly by differentiating the centered curve. -/
theorem centered_symmetricExpProduct_sub_one_eq_integral (l : List A) (G : A) (h : ℝ) :
    exp ((-h / 2) • G) * symmetricExpProduct l h * exp ((-h / 2) • G) - 1 =
      ∫ x in 0..h, centeredSymmetricDefect l G x := by
  have hd (x : ℝ) : HasDerivAt
      (fun x ↦ exp ((-x / 2) • G) * symmetricExpProduct l x * exp ((-x / 2) • G))
      (centeredSymmetricDefect l G x) x := by
    have hs := hasDerivAt_exp_mul_mul_exp ((1 / 2 : ℝ) • G)
      (((contDiff_symmetricExpProduct l).differentiable (by simp)).differentiableAt.hasDerivAt
        (x := x)) 0
    convert hs using 1 <;> simp only [centeredSymmetricDefect, symmetricDefect,
      zero_sub, smul_smul, smul_mul_assoc, mul_smul_comm, smul_add, neg_div,
      mul_one_div]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hd x)
    ((continuous_centeredSymmetricDefect l G).intervalIntegrable 0 h)]
  simp

/-- The centered defect remainder retains only the paper's original commutator constants. -/
theorem norm_centeredSymmetricDefect_sub_quartic_le (l : List A) (G L : A) (C : ℝ)
    (hC : 0 ≤ C) (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1)
    (hsum : l.sum = (1 / 2 : ℝ) • G)
    (hT : ∀ x : ℝ, ‖halfDefect l G x + halfDefect l G (-x) - (5 * x ^ 4) • L‖ ≤
      7 * C * |x| ^ 6) (x : ℝ) :
    ‖centeredSymmetricDefect l G x - (5 * x ^ 4) • L‖ ≤
      7 * C * |x| ^ 6 + 5 * x ^ 4 *
        (x ^ 2 / 2 * centeredConjugationConstant l G L +
          ‖L‖ * (|x| ^ 5 * ‖L‖ + |x| ^ 7 * C)) := by
  let U := exp ((-x / 2) • G) * expListProduct l x
  let V := expListProduct l.reverse x * exp ((-x / 2) • G)
  have heq : centeredSymmetricDefect l G x - (5 * x ^ 4) • L =
      U * (halfDefect l G x + halfDefect l G (-x) - (5 * x ^ 4) • L) * V +
        (5 * x ^ 4) • (U * L * V - L) := by
    rw [centeredSymmetricDefect, symmetricDefect_eq_halfDefect_add]
    dsimp [U, V]
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
    noncomm_ring
  rw [heq]
  calc
    _ ≤ ‖U * (halfDefect l G x + halfDefect l G (-x) - (5 * x ^ 4) • L) * V‖ +
        ‖(5 * x ^ 4) • (U * L * V - L)‖ := norm_add_le _ _
    _ = ‖halfDefect l G x + halfDefect l G (-x) - (5 * x ^ 4) • L‖ +
        5 * x ^ 4 * ‖U * L * V - L‖ := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ 5 * x ^ 4)]
      congr 1
      dsimp [U, V]
      simp only [← mul_assoc]
      rw [norm_mul_exp_smul_eq_of_le_one G _ hG,
        norm_mul_expListProduct_eq_of_le_one l.reverse _
          (fun Z hz ↦ hZ Z (by simpa using hz)),
        mul_assoc, norm_exp_smul_mul_eq_of_le_one G _ hG,
        norm_expListProduct_mul_eq_of_le_one l _ hZ]
    _ ≤ _ := by
      apply add_le_add (hT x)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [U, V, mul_assoc] using
        (norm_centered_half_transport_sub_le l G L hZ hG hsum x).trans
        (add_le_add_right (mul_le_mul_of_nonneg_left
          (norm_symmetricExpProduct_sub_exp_le l G L C hC hZ hG hT x) (norm_nonneg L)) _)

end FQFP

namespace FQFP

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- **Centered local remainder.** The complete quintic coefficient is retained
inside every commutator and norm, with the paper's seventh-, tenth-, and twelfth-degree terms. -/
theorem norm_centered_symmetricExpProduct_sub_quintic_le (l : List A) (G L : A) (C : ℝ)
    (hC : 0 ≤ C) (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1)
    (hsum : l.sum = (1 / 2 : ℝ) • G)
    (hT : ∀ x : ℝ, ‖halfDefect l G x + halfDefect l G (-x) - (5 * x ^ 4) • L‖ ≤
      7 * C * |x| ^ 6) (h : ℝ) (hh : 0 ≤ h) :
    ‖exp ((-h / 2) • G) * (symmetricExpProduct l h - exp (h • G)) *
        exp ((-h / 2) • G) - h ^ 5 • L‖ ≤
      h ^ 7 * (C + 5 / 14 * centeredConjugationConstant l G L) +
        1 / 2 * h ^ 10 * ‖L‖ ^ 2 + 5 / 12 * h ^ 12 * ‖L‖ * C := by
  let alpha := centeredConjugationConstant l G L
  let P : ℝ → ℝ := fun x ↦ (7 * C + 5 / 2 * alpha) * x ^ 6 +
    5 * ‖L‖ ^ 2 * x ^ 9 + 5 * ‖L‖ * C * x ^ 11
  have hpoly : (∫ x in 0..h, (5 * x ^ 4) • L) = h ^ 5 • L := by
    rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    congr 1
    ring
  have heq : exp ((-h / 2) • G) * (symmetricExpProduct l h - exp (h • G)) *
        exp ((-h / 2) • G) - h ^ 5 • L =
      ∫ x in 0..h, centeredSymmetricDefect l G x - (5 * x ^ 4) • L := by
    rw [intervalIntegral.integral_sub
      ((continuous_centeredSymmetricDefect l G).intervalIntegrable 0 h)
      ((by fun_prop : Continuous (fun x : ℝ ↦ (5 * x ^ 4) • L)).intervalIntegrable 0 h),
      hpoly, ← centered_symmetricExpProduct_sub_one_eq_integral]
    simp only [mul_sub, sub_mul, exp_neg_half_mul_exp_mul_exp_neg_half]
  rw [heq]
  calc
    _ ≤ ∫ x in 0..h, P x := by
      apply intervalIntegral.norm_integral_le_of_norm_le hh _
        ((by fun_prop : Continuous P).intervalIntegrable 0 h)
      filter_upwards with x hx
      have hx0 : 0 ≤ x := le_of_lt hx.1
      have hb := norm_centeredSymmetricDefect_sub_quartic_le l G L C hC hZ hG hsum hT x
      rw [abs_of_nonneg hx0] at hb
      convert hb using 1
      dsimp [P, alpha]
      ring
    _ = _ := by
      dsimp [P]
      rw [intervalIntegral.integral_add
        ((by fun_prop : Continuous (fun x : ℝ ↦ (7 * C + 5 / 2 * alpha) * x ^ 6 +
          5 * ‖L‖ ^ 2 * x ^ 9)).intervalIntegrable 0 h)
        ((by fun_prop : Continuous (fun x : ℝ ↦ 5 * ‖L‖ * C * x ^ 11)).intervalIntegrable 0 h),
        intervalIntegral.integral_add
          ((by fun_prop : Continuous
            (fun x : ℝ ↦ (7 * C + 5 / 2 * alpha) * x ^ 6)).intervalIntegrable 0 h)
          ((by fun_prop : Continuous (fun x : ℝ ↦ 5 * ‖L‖ ^ 2 * x ^ 9)).intervalIntegrable 0 h)]
      simp only [intervalIntegral.integral_const_mul, integral_pow]
      norm_num
      dsimp [alpha]
      ring

end FQFP
