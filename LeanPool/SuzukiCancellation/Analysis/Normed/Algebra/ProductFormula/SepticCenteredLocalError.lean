/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SepticLocalError

/-!
# Centered ninth-order remainder with both leading coefficients

Grouped fourth- and second-order conjugation estimates retain the entire
coefficient polynomials. Integrating the centered defect gives the exact
ninth-, tenth-, twelfth-, fourteenth-, and sixteenth-degree remainder terms.

## Main results

* `norm_multiConj_sub_sum_le_grouped`: grouped bounds for zero kicks.
* `norm_centered_symmetricExpProduct_sub_septic_le`: the centered local estimate.
-/

@[expose] public noncomputable section

open NormedSpace MeasureTheory TrotterError Finset
open scoped RealScalar

namespace TrotterError

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- Grouped Taylor remainders for ordinary conjugation use zero kicks. -/
theorem norm_multiConj_sub_sum_le_grouped {s : ℕ} (Z : Fin s → A) (B : A)
    (hZ : ∀ i (t : ℝ), ‖exp (t • Z i)‖ ≤ 1) (p : ℕ) (hp : 1 ≤ p) (x : ℝ) :
    ‖multiConj Z B x - ∑ k ∈ range p, x ^ k • conjCoeff Z B k‖ ≤
      |x| ^ p * groupedConjBound Z (fun _ ↦ 0) B p := by
  simpa only [groupedConj_zero_kicks_eq_multiConj,
    groupedConjCoeff_zero_kicks_eq_conjCoeff] using
      norm_groupedConj_sub_sum_le Z (fun _ ↦ 0) B hZ p hp x

end TrotterError

namespace FQFP

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- A centered conjugation with vanished odd coefficients has its grouped fourth-order tail. -/
theorem norm_centeredConjugation_sub_quadratic_le (l : List A) (G L B : A)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1)
    (h1 : conjCoeff (centeredConjugationList l G).get L 1 = 0)
    (h2 : conjCoeff (centeredConjugationList l G).get L 2 = B)
    (h3 : conjCoeff (centeredConjugationList l G).get L 3 = 0) (x : ℝ) :
    ‖multiConj (centeredConjugationList l G).get L x - L - x ^ 2 • B‖ ≤
      |x| ^ 4 * groupedConjBound (centeredConjugationList l G).get (fun _ ↦ 0) L 4 := by
  have hb := norm_multiConj_sub_sum_le_grouped (centeredConjugationList l G).get L
    (norm_exp_smul_centeredConjugationList_le_one l G hZ hG) 4 (by norm_num) x
  simpa only [sum_range_succ, sum_range_zero, zero_add, pow_zero, one_smul,
    conjCoeff_zero, h1, h2, h3, smul_zero, add_zero, sub_add_eq_sub_sub] using hb

/-- Vanishing of the linear coefficient gives the grouped quadratic transport bound. -/
theorem norm_centeredConjugation_sub_le_grouped (l : List A) (G M : A)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1)
    (h1 : conjCoeff (centeredConjugationList l G).get M 1 = 0) (x : ℝ) :
    ‖multiConj (centeredConjugationList l G).get M x - M‖ ≤
      |x| ^ 2 * groupedConjBound (centeredConjugationList l G).get (fun _ ↦ 0) M 2 := by
  have hb := norm_multiConj_sub_sum_le_grouped (centeredConjugationList l G).get M
    (norm_exp_smul_centeredConjugationList_le_one l G hZ hG) 2 (by norm_num) x
  simpa only [sum_range_succ, sum_range_zero, zero_add, pow_zero, one_smul,
    conjCoeff_zero, h1, smul_zero, add_zero] using hb

/-- The two centered exterior half-products preserve every input norm. -/
lemma norm_centered_half_transport_eq (l : List A) (G B : A)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1) (x : ℝ) :
    ‖exp ((-x / 2) • G) * expListProduct l x * B *
      expListProduct l.reverse x * exp ((-x / 2) • G)‖ = ‖B‖ := by
  rw [norm_mul_exp_smul_eq_of_le_one G _ hG,
    norm_mul_expListProduct_eq_of_le_one l.reverse _
      (fun Z hz ↦ hZ Z (by simpa using hz)), mul_assoc,
    norm_exp_smul_mul_eq_of_le_one G _ hG,
    norm_expListProduct_mul_eq_of_le_one l _ hZ]

/-- The two transported coefficient polynomials have the combined eighth-order remainder. -/
lemma norm_centeredConjugation_quartic_add_sextic_sub_le (l : List A) (G L M B : A)
    (R4 R2 : ℝ)
    (hL : ∀ x : ℝ, ‖multiConj (centeredConjugationList l G).get L x - L - x ^ 2 • B‖ ≤
      |x| ^ 4 * R4)
    (hM : ∀ x : ℝ, ‖multiConj (centeredConjugationList l G).get M x - M‖ ≤ |x| ^ 2 * R2)
    (x : ℝ) (hx : 0 ≤ x) :
    ‖multiConj (centeredConjugationList l G).get
        ((5 * x ^ 4) • L + (7 * x ^ 6) • M) x -
      ((5 * x ^ 4) • L + (7 * x ^ 6) • (M + (5 / 7 : ℝ) • B))‖ ≤
        (5 * R4 + 7 * R2) * x ^ 8 := by
  have heq : multiConj (centeredConjugationList l G).get
        ((5 * x ^ 4) • L + (7 * x ^ 6) • M) x -
      ((5 * x ^ 4) • L + (7 * x ^ 6) • (M + (5 / 7 : ℝ) • B)) =
      (5 * x ^ 4) • (multiConj (centeredConjugationList l G).get L x - L - x ^ 2 • B) +
        (7 * x ^ 6) • (multiConj (centeredConjugationList l G).get M x - M) := by
    simp only [multiConj, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    module
  rw [heq]
  calc
    _ ≤ ‖(5 * x ^ 4) •
        (multiConj (centeredConjugationList l G).get L x - L - x ^ 2 • B)‖ +
        ‖(7 * x ^ 6) • (multiConj (centeredConjugationList l G).get M x - M)‖ :=
      norm_add_le _ _
    _ ≤ (5 * x ^ 4) * (x ^ 4 * R4) + (7 * x ^ 6) * (x ^ 2 * R2) := by
      simp only [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ 5 * x ^ 4),
        abs_of_nonneg (by positivity : 0 ≤ 7 * x ^ 6)]
      exact add_le_add (mul_le_mul_of_nonneg_left
        (by simpa only [abs_of_nonneg hx] using hL x) (by positivity))
        (mul_le_mul_of_nonneg_left
          (by simpa only [abs_of_nonneg hx] using hM x) (by positivity))
    _ = _ := by ring

/-- The centered integrand remainder before integrating its exact polynomial majorant. -/
theorem norm_centeredSymmetricDefect_sub_sextic_le (l : List A) (G L M B : A)
    (C R4 R2 : ℝ) (hC : 0 ≤ C)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1)
    (hT : ∀ x : ℝ, ‖halfDefect l G x + halfDefect l G (-x) -
      (5 * x ^ 4) • L - (7 * x ^ 6) • M‖ ≤ 9 * C * |x| ^ 8)
    (hL : ∀ x : ℝ, ‖multiConj (centeredConjugationList l G).get L x - L - x ^ 2 • B‖ ≤
      |x| ^ 4 * R4)
    (hM : ∀ x : ℝ, ‖multiConj (centeredConjugationList l G).get M x - M‖ ≤ |x| ^ 2 * R2)
    (x : ℝ) (hx : 0 ≤ x) :
    ‖centeredSymmetricDefect l G x -
      ((5 * x ^ 4) • L + (7 * x ^ 6) • (M + (5 / 7 : ℝ) • B))‖ ≤
      (9 * C + 5 * R4 + 7 * R2) * x ^ 8 +
        (5 * x ^ 4 * ‖L‖ + 7 * x ^ 6 * ‖M‖) * septicStepBound ‖L‖ ‖M‖ C x := by
  let P := (5 * x ^ 4) • L + (7 * x ^ 6) • M
  let Q := (5 * x ^ 4) • L + (7 * x ^ 6) • (M + (5 / 7 : ℝ) • B)
  let H := exp ((-x / 2) • G) * expListProduct l x * P *
    expListProduct l.reverse x * exp ((-x / 2) • G)
  let R := multiConj (centeredConjugationList l G).get P x
  have hP : ‖P‖ ≤ 5 * x ^ 4 * ‖L‖ + 7 * x ^ 6 * ‖M‖ := by
    calc
      _ ≤ ‖(5 * x ^ 4 : ℝ) • L‖ + ‖(7 * x ^ 6 : ℝ) • M‖ := norm_add_le _ _
      _ = _ := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hx]
  have hfirst : ‖centeredSymmetricDefect l G x - H‖ ≤ 9 * C * x ^ 8 := by
    have heq : centeredSymmetricDefect l G x - H =
        exp ((-x / 2) • G) * expListProduct l x *
          (halfDefect l G x + halfDefect l G (-x) - P) *
            expListProduct l.reverse x * exp ((-x / 2) • G) := by
      simp only [centeredSymmetricDefect, symmetricDefect_eq_halfDefect_add, H]
      noncomm_ring
    rw [heq, norm_centered_half_transport_eq l G _ hZ hG]
    simpa only [P, sub_add_eq_sub_sub, abs_of_nonneg hx] using hT x
  have hsecond : ‖H - R‖ ≤
      (5 * x ^ 4 * ‖L‖ + 7 * x ^ 6 * ‖M‖) * septicStepBound ‖L‖ ‖M‖ C x := by
    exact (norm_centered_half_transport_sub_conjugation_le l G P hZ hG x).trans
      (mul_le_mul hP
        (by simpa only [abs_of_nonneg hx] using
          norm_symmetricExpProduct_sub_exp_le_septic l G L M C hC hZ hG hT x)
        (norm_nonneg _) (by positivity))
  have hthird : ‖R - Q‖ ≤ (5 * R4 + 7 * R2) * x ^ 8 :=
    norm_centeredConjugation_quartic_add_sextic_sub_le l G L M B R4 R2 hL hM x hx
  calc
    _ ≤ ‖centeredSymmetricDefect l G x - H‖ + ‖H - R‖ + ‖R - Q‖ :=
      (norm_sub_le_norm_sub_add_norm_sub _ H Q).trans
        (by linarith [norm_sub_le_norm_sub_add_norm_sub H R Q])
    _ ≤ 9 * C * x ^ 8 +
        (5 * x ^ 4 * ‖L‖ + 7 * x ^ 6 * ‖M‖) * septicStepBound ‖L‖ ‖M‖ C x +
          (5 * R4 + 7 * R2) * x ^ 8 := add_le_add (add_le_add hfirst hsecond) hthird
    _ = _ := by ring

/-- Integrating the factored centered majorant gives every coefficient of the
paper's remainder polynomial. -/
lemma integral_septicCentered_majorant (ℓ μ C R4 R2 h : ℝ) :
    (∫ x in 0..h, (9 * C + 5 * R4 + 7 * R2) * x ^ 8 +
      (5 * x ^ 4 * ℓ + 7 * x ^ 6 * μ) * septicStepBound ℓ μ C x) =
        septicCenteredRemainder ℓ μ C (C + 5 * R4 / 9 + 7 * R2 / 9) h := by
  let D := C + 5 * R4 / 9 + 7 * R2 / 9
  let F : ℝ → ℝ := fun u ↦ u ^ 9 * D + u ^ 10 * (ℓ ^ 2 / 2) +
    u ^ 12 * (ℓ * μ) + u ^ 14 * ((5 * ℓ * C + 7 * μ ^ 2) / 14) +
      u ^ 16 * (7 * μ * C / 16)
  have hd (x : ℝ) : HasDerivAt F
      ((9 * C + 5 * R4 + 7 * R2) * x ^ 8 +
        (5 * x ^ 4 * ℓ + 7 * x ^ 6 * μ) * septicStepBound ℓ μ C x) x := by
    convert ((((((hasDerivAt_id x).pow 9).mul_const D).add
      (((hasDerivAt_id x).pow 10).mul_const (ℓ ^ 2 / 2))).add
      (((hasDerivAt_id x).pow 12).mul_const (ℓ * μ))).add
      (((hasDerivAt_id x).pow 14).mul_const ((5 * ℓ * C + 7 * μ ^ 2) / 14))).add
      (((hasDerivAt_id x).pow 16).mul_const (7 * μ * C / 16)) using 1
    · rfl
    · dsimp [D, septicStepBound]
      norm_num
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hd x)
    ((by
      unfold septicStepBound
      fun_prop : Continuous
      (fun x : ℝ ↦ (9 * C + 5 * R4 + 7 * R2) * x ^ 8 +
      (5 * x ^ 4 * ℓ + 7 * x ^ 6 * μ) * septicStepBound ℓ μ C x)).intervalIntegrable 0 h)]
  dsimp [F, D, septicCenteredRemainder]
  ring

/-- **Centered ninth-order local bound.** The complete septic coefficient and
every nonlinear remainder term are retained. -/
theorem norm_centered_symmetricExpProduct_sub_septic_le (l : List A) (G L M B : A)
    (C R4 R2 : ℝ) (hC : 0 ≤ C)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1)
    (hT : ∀ x : ℝ, ‖halfDefect l G x + halfDefect l G (-x) -
      (5 * x ^ 4) • L - (7 * x ^ 6) • M‖ ≤ 9 * C * |x| ^ 8)
    (hL : ∀ x : ℝ, ‖multiConj (centeredConjugationList l G).get L x - L - x ^ 2 • B‖ ≤
      |x| ^ 4 * R4)
    (hM : ∀ x : ℝ, ‖multiConj (centeredConjugationList l G).get M x - M‖ ≤ |x| ^ 2 * R2)
    (h : ℝ) (hh : 0 ≤ h) :
    ‖exp ((-h / 2) • G) * (symmetricExpProduct l h - exp (h • G)) *
        exp ((-h / 2) • G) - h ^ 5 • L - h ^ 7 • (M + (5 / 7 : ℝ) • B)‖ ≤
      septicCenteredRemainder ‖L‖ ‖M‖ C (C + 5 * R4 / 9 + 7 * R2 / 9) h := by
  let N := M + (5 / 7 : ℝ) • B
  let P : ℝ → A := fun x ↦ (5 * x ^ 4) • L + (7 * x ^ 6) • N
  have hi : (∫ x in 0..h, P x) = h ^ 5 • L + h ^ 7 • N := by
    rw [intervalIntegral.integral_add
      ((by fun_prop : Continuous (fun x : ℝ ↦ (5 * x ^ 4) • L)).intervalIntegrable 0 h)
      ((by fun_prop : Continuous (fun x : ℝ ↦ (7 * x ^ 6) • N)).intervalIntegrable 0 h)]
    simp only [intervalIntegral.integral_smul_const, intervalIntegral.integral_const_mul,
      integral_pow]
    norm_num
    congr 1 <;> module
  have heq : exp ((-h / 2) • G) * (symmetricExpProduct l h - exp (h • G)) *
        exp ((-h / 2) • G) - h ^ 5 • L - h ^ 7 • N =
      ∫ x in 0..h, centeredSymmetricDefect l G x - P x := by
    rw [intervalIntegral.integral_sub
      ((continuous_centeredSymmetricDefect l G).intervalIntegrable 0 h)
      ((by fun_prop : Continuous P).intervalIntegrable 0 h), hi,
      ← centered_symmetricExpProduct_sub_one_eq_integral]
    simp only [mul_sub, sub_mul, exp_neg_half_mul_exp_mul_exp_neg_half]
    abel
  rw [heq]
  calc
    _ ≤ ∫ x in 0..h, (9 * C + 5 * R4 + 7 * R2) * x ^ 8 +
        (5 * x ^ 4 * ‖L‖ + 7 * x ^ 6 * ‖M‖) * septicStepBound ‖L‖ ‖M‖ C x := by
      apply intervalIntegral.norm_integral_le_of_norm_le hh _
        ((by
          unfold septicStepBound
          fun_prop : Continuous
          (fun x : ℝ ↦ (9 * C + 5 * R4 + 7 * R2) * x ^ 8 +
          (5 * x ^ 4 * ‖L‖ + 7 * x ^ 6 * ‖M‖) *
            septicStepBound ‖L‖ ‖M‖ C x)).intervalIntegrable 0 h)
      filter_upwards with x hx
      exact norm_centeredSymmetricDefect_sub_sextic_le l G L M B C R4 R2 hC hZ hG hT
        hL hM x (le_of_lt hx.1)
    _ = _ := integral_septicCentered_majorant ..

end FQFP
