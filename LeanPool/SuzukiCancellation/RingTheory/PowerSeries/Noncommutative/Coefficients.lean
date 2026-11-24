/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum

/-!
# Finite algebraic power series

Finite exponential products, powers of positive-degree homogeneous expansions, and logarithm
polynomials in a rational algebra. All operations preserve factor order and need no topology
or completeness. The power truncation itself is defined over an arbitrary semiring.

## Main definitions

* `FQFP.expMulTerm`, `FQFP.expMulMulTerm`: ordered factorial convolutions in degree `n`.
* `FQFP.positivePowerTrunc`: the terms in a positive-degree power below a degree cutoff.
* `FQFP.positivePowerCoeff`: one homogeneous coefficient of a positive-degree power.
* `FQFP.logCoeff`, `FQFP.logPartialSum`: rational logarithm coefficients and finite sums.

## Main results

* `FQFP.expMulTerm_zero`, `FQFP.expMulTerm_one`: constant and linear exponential terms.
* `FQFP.map_positivePowerCoeff`, `FQFP.positivePowerCoeff_smul`: naturality and scaling.
* `FQFP.pow_sub_positivePowerTrunc_succ`: a residual decomposition by the first factor.
* `FQFP.positivePowerTrunc_succ`, `FQFP.sum_smul_positivePowerTrunc_succ`: cutoff increments.
* `FQFP.logPartialSum_succ`: the recurrence for finite logarithm sums.
-/

@[expose] public section

open Finset Finset.Nat

/-! ### Homogeneous exponential products -/

namespace FQFP

/-- The homogeneous term of total degree `n` in `exp a * exp b`. -/
noncomputable def expMulTerm {A : Type*} [Semiring A] [Algebra ℚ A] (a b : A) (n : ℕ) : A :=
  ∑ ij ∈ antidiagonal n, ((Nat.factorial ij.1 : ℚ)⁻¹ • a ^ ij.1) *
    ((Nat.factorial ij.2 : ℚ)⁻¹ • b ^ ij.2)

variable {A : Type*} [Semiring A] [Algebra ℚ A]

/-- The constant homogeneous term is one. -/
@[simp] lemma expMulTerm_zero (a b : A) : expMulTerm a b 0 = 1 := by
  rw [expMulTerm, sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [sum_range_succ, Nat.factorial, smul_mul_smul_comm]

/-- The linear homogeneous term is the sum of the inputs. -/
@[simp] lemma expMulTerm_one (a b : A) : expMulTerm a b 1 = a + b := by
  rw [expMulTerm, sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [sum_range_succ, Nat.factorial, smul_mul_smul_comm, add_comm]

/-- The quadratic homogeneous term consists of the mixed product and two pure powers. -/
lemma expMulTerm_two (a b : A) :
    expMulTerm a b 2 = a * b + (2 : ℚ)⁻¹ • a ^ 2 + (2 : ℚ)⁻¹ • b ^ 2 := by
  rw [expMulTerm, sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [sum_range_succ, Nat.factorial, smul_mul_smul_comm]
  ac_rfl

/-- The exponential product truncated after its linear term. -/
lemma sum_range_expMulTerm_two (a b : A) :
    ∑ i ∈ range 2, expMulTerm a b i = 1 + (a + b) := by
  simp [sum_range_succ]

/-- The total-degree coefficient of an ordered product of three exponentials. -/
noncomputable def expMulMulTerm (a b c : A) (n : ℕ) : A :=
  ∑ ij ∈ antidiagonal n,
    expMulTerm a b ij.1 * ((Nat.factorial ij.2 : ℚ)⁻¹ • c ^ ij.2)

/-- The constant coefficient of a triple exponential product is one. -/
@[simp]
lemma expMulMulTerm_zero (a b c : A) : expMulMulTerm a b c 0 = 1 := by
  simp [expMulMulTerm]

/-- The linear coefficient of a triple exponential product is the sum of its inputs. -/
@[simp]
lemma expMulMulTerm_one (a b c : A) : expMulMulTerm a b c 1 = a + b + c := by
  rw [expMulMulTerm, sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [sum_range_succ]
  ac_rfl

end FQFP

/-! ### Powers of positive homogeneous expansions -/

namespace FQFP

/-- The terms of total degree strictly below `n` in the `k`th power of positive-degree
homogeneous terms `u`. The value `u 0` is never used. -/
def positivePowerTrunc {A : Type*} [Semiring A] (u : ℕ → A) : ℕ → ℕ → A
  | 0, n => if n = 0 then 0 else 1
  | k + 1, n => ∑ i ∈ range (n - (k + 1)),
      u (i + 1) * positivePowerTrunc u k (n - (i + 1))

section PowerCoefficients

variable {A : Type*} [Semiring A]

/-- The degree-`n` coefficient in the `k`th power of positive homogeneous terms.
The value `u 0` is ignored; the zeroth power has coefficient one at degree zero only. -/
def positivePowerCoeff (u : ℕ → A) : ℕ → ℕ → A
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n => ∑ i ∈ range (n - k),
      u (i + 1) * positivePowerCoeff u k (n - (i + 1))

/-- A coefficient of a positive power depends only on the input prefix. -/
lemma positivePowerCoeff_congr (u v : ℕ → A) (n : ℕ)
    (h : ∀ i, 0 < i → i ≤ n → u i = v i) (k : ℕ) :
    positivePowerCoeff u k n = positivePowerCoeff v k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      simp only [positivePowerCoeff]
      apply sum_congr rfl
      intro i hi
      have hi' := mem_range.mp hi
      rw [h (i + 1) (by lia) (by lia), ih _ (fun j hj hjn ↦ h j hj (by lia))]

/-- Algebra homomorphisms preserve the coefficients of positive-degree powers. -/
lemma map_positivePowerCoeff [Algebra ℚ A] {B : Type*} [Semiring B] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (u : ℕ → A) (k n : ℕ) :
    f (positivePowerCoeff u k n) = positivePowerCoeff (fun i ↦ f (u i)) k n := by
  induction k generalizing n with
  | zero => by_cases hn : n = 0 <;> simp [positivePowerCoeff, hn]
  | succ k ih => simp [positivePowerCoeff, map_sum, ih]

/-- Graded scaling is preserved by positive-degree power coefficients. -/
lemma positivePowerCoeff_smul {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
    (u : ℕ → B) (c : R) (k n : ℕ) :
    positivePowerCoeff (fun i ↦ c ^ i • u i) k n = c ^ n • positivePowerCoeff u k n := by
  induction k generalizing n with
  | zero => by_cases hn : n = 0 <;> simp [positivePowerCoeff, hn]
  | succ k ih =>
      simp only [positivePowerCoeff, ih, smul_sum]
      apply sum_congr rfl
      intro i hi
      have hin : i + 1 ≤ n := by
        have := mem_range.mp hi
        lia
      rw [smul_mul_smul_comm, ← pow_add, Nat.add_sub_of_le hin]

/-- Convolution for powers of at least two, keeping linear coefficients as the leaves. -/
lemma positivePowerCoeff_add_two (u : ℕ → A) (k n : ℕ) :
    positivePowerCoeff u (k + 2) n =
      ∑ i ∈ range (n - (k + 1)), u (i + 1) * positivePowerCoeff u (k + 1) (n - (i + 1)) := rfl

/-- No product of `k` positive-degree factors has total degree below `k`. -/
lemma positivePowerTrunc_eq_zero_of_le (u : ℕ → A) (k n : ℕ) (h : n ≤ k) :
    positivePowerTrunc u k n = 0 := by
  cases k with
  | zero => simp [positivePowerTrunc, show n = 0 by lia]
  | succ k => simp [positivePowerTrunc, Nat.sub_eq_zero_of_le h]

/-- The homogeneous coefficient vanishes below the number of positive-degree factors. -/
lemma positivePowerCoeff_eq_zero_of_lt (u : ℕ → A) (k n : ℕ) (h : n < k) :
    positivePowerCoeff u k n = 0 := by
  cases k with
  | zero => lia
  | succ k => simp [positivePowerCoeff, Nat.sub_eq_zero_of_le (show n ≤ k by lia)]

/-- The first power has the original positive-degree homogeneous terms. -/
lemma positivePowerCoeff_one (u : ℕ → A) (n : ℕ) :
    positivePowerCoeff u 1 (n + 1) = u (n + 1) := by
  simp only [positivePowerCoeff, Nat.sub_zero]
  rw [Finset.sum_eq_single n]
  · simp
  · intro i hi hin
    have hi' := mem_range.mp hi
    rw [ite_eq_right (show n + 1 - (i + 1) ≠ 0 by lia), mul_zero]
  · simp

/-- At minimal degree every factor is the linear homogeneous term. -/
lemma positivePowerCoeff_self (u : ℕ → A) (k : ℕ) :
    positivePowerCoeff u k k = u 1 ^ k := by
  induction k with
  | zero => simp [positivePowerCoeff]
  | succ k ih => simp [positivePowerCoeff, ih, pow_succ']

/-- Increasing the cutoff adds exactly the next homogeneous coefficient. -/
lemma positivePowerTrunc_succ (u : ℕ → A) (k n : ℕ) :
    positivePowerTrunc u k (n + 1) =
      positivePowerTrunc u k n + positivePowerCoeff u k n := by
  induction k generalizing n with
  | zero => by_cases h : n = 0 <;> simp [positivePowerTrunc, positivePowerCoeff, h]
  | succ k ih =>
    by_cases h : n ≤ k
    · rw [positivePowerTrunc_eq_zero_of_le u (k + 1) (n + 1) (by lia),
        positivePowerTrunc_eq_zero_of_le u (k + 1) n (by lia),
        positivePowerCoeff_eq_zero_of_lt u (k + 1) n (by lia), zero_add]
    · have hn : k < n := by lia
      have hnsub : n - k = (n - (k + 1)) + 1 := by lia
      simp only [positivePowerTrunc, positivePowerCoeff,
        show n + 1 - (k + 1) = n - k by lia]
      have hsum : (∑ i ∈ range (n - k),
          u (i + 1) * positivePowerTrunc u k (n + 1 - (i + 1))) =
          (∑ i ∈ range (n - k), u (i + 1) * positivePowerTrunc u k (n - (i + 1))) +
          ∑ i ∈ range (n - k), u (i + 1) * positivePowerCoeff u k (n - (i + 1)) := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro i hi
        have hin := mem_range.mp hi
        rw [show n + 1 - (i + 1) = n - (i + 1) + 1 by lia, ih, mul_add]
      rw [hsum]
      congr 1
      rw [hnsub, sum_range_succ]
      simp [positivePowerTrunc_eq_zero_of_le u k _ (show n - (n - (k + 1) + 1) ≤ k by lia)]

/-- A finite positive-degree power truncation is the sum of its homogeneous coefficients. -/
lemma positivePowerTrunc_eq_sum_coeff (u : ℕ → A) (k n : ℕ) :
    positivePowerTrunc u k n = ∑ d ∈ range n, positivePowerCoeff u k d := by
  induction n with
  | zero =>
    rw [positivePowerTrunc_eq_zero_of_le u k 0 (by lia), sum_range_zero]
  | succ n ih =>
    rw [positivePowerTrunc_succ, sum_range_succ, ih]

/-- Increasing the cutoff in a weighted sum of powers adds its next homogeneous component. -/
lemma sum_smul_positivePowerTrunc_succ {R : Type*} [Semiring R] [Module R A]
    (c : ℕ → R) (u : ℕ → A) (n : ℕ) :
    (∑ k ∈ range (n + 1), c k • positivePowerTrunc u k (n + 1)) =
      (∑ k ∈ range n, c k • positivePowerTrunc u k n) +
        ∑ k ∈ range (n + 1), c k • positivePowerCoeff u k n := by
  simp_rw [positivePowerTrunc_succ, smul_add]
  rw [sum_add_distrib, sum_range_succ,
    positivePowerTrunc_eq_zero_of_le u n n le_rfl, smul_zero, add_zero]

end PowerCoefficients

/-- Splitting off the first factor separates the input tail from lower power errors. -/
lemma pow_sub_positivePowerTrunc_succ {A : Type*} [Ring A]
    (u : ℕ → A) (y : A) (k n : ℕ) :
    y ^ (k + 1) - positivePowerTrunc u (k + 1) n =
      (y - ∑ i ∈ range (n - (k + 1)), u (i + 1)) * y ^ k +
        ∑ i ∈ range (n - (k + 1)),
          u (i + 1) * (y ^ k - positivePowerTrunc u k (n - (i + 1))) := by
  simp only [positivePowerTrunc, mul_sub, sub_mul, sum_sub_distrib, sum_mul, pow_succ']
  abel

end FQFP

/-! ### Finite logarithm polynomials -/

namespace FQFP
variable {𝔸 : Type*}

section PartialSum

variable [Ring 𝔸] [Algebra ℚ 𝔸]

/-- The rational coefficients of the formal power series for `log (1 + X)`:
`logCoeff i = (-1)^(i+1)/i`. -/
def logCoeff (i : ℕ) : ℚ := (-1 : ℚ) ^ (i + 1) / i

@[simp] theorem logCoeff_zero : logCoeff 0 = 0 := by norm_num [logCoeff]
@[simp] theorem logCoeff_one : logCoeff 1 = 1 := by norm_num [logCoeff]
@[simp] theorem logCoeff_two : logCoeff 2 = -(2 : ℚ)⁻¹ := by norm_num [logCoeff]
@[simp] theorem logCoeff_three : logCoeff 3 = (3 : ℚ)⁻¹ := by norm_num [logCoeff]

/-- The partial sum `∑_{i<n} logCoeff i • xⁱ` of the log series. The subscript `n` is the degree of
the *first omitted* term, which is what makes it line up with the split point of
`Summable.sum_add_tsum_nat_add`: both `logPartialSum 𝔸 0 x` and `logPartialSum 𝔸 1 x` are zero
(the constant coefficient is `(-1)/0 = 0`), while `logPartialSum 𝔸 2 x = x` and
`logPartialSum 𝔸 3 x = x - x²/2`. -/
def logPartialSum (𝔸 : Type*) [Ring 𝔸] [Algebra ℚ 𝔸] (n : ℕ)
    (x : 𝔸) : 𝔸 :=
  ∑ i ∈ Finset.range n, logCoeff i • x ^ i

@[simp]
theorem logPartialSum_zero (x : 𝔸) : logPartialSum 𝔸 0 x = 0 :=
  Finset.sum_range_zero _

/-- **The next partial sum adds the term of degree `n`.** -/
theorem logPartialSum_succ (n : ℕ) (x : 𝔸) :
    logPartialSum 𝔸 (n + 1) x = logPartialSum 𝔸 n x + logCoeff n • x ^ n :=
  Finset.sum_range_succ _ _

/-- The first partial sum of the log series vanishes: its constant coefficient is `(-1)/0 = 0`. -/
@[simp]
theorem logPartialSum_one (x : 𝔸) : logPartialSum 𝔸 1 x = 0 := by
  simp only [logPartialSum_succ, logPartialSum_zero, logCoeff_zero, zero_smul, add_zero]

/-- The second partial sum of the log series is the linear term `x`. -/
@[simp]
theorem logPartialSum_two (x : 𝔸) : logPartialSum 𝔸 2 x = x := by
  rw [logPartialSum_succ, logPartialSum_one, logCoeff_one, one_smul, pow_one, zero_add]

/-- The third partial sum of the log series is `x - x²/2`. -/
@[simp]
theorem logPartialSum_three (x : 𝔸) :
    logPartialSum 𝔸 3 x = x - (2 : ℚ)⁻¹ • x ^ 2 := by
  rw [logPartialSum_succ, logPartialSum_two, logCoeff_two, neg_smul, sub_eq_add_neg]

/-- The fourth partial sum of the log series is `x - x²/2 + x³/3`. -/
@[simp]
theorem logPartialSum_four (x : 𝔸) :
    logPartialSum 𝔸 4 x = x - (2 : ℚ)⁻¹ • x ^ 2 + (3 : ℚ)⁻¹ • x ^ 3 := by
  rw [logPartialSum_succ, logPartialSum_three, logCoeff_three]

end PartialSum

end FQFP
