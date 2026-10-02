/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang, Moritz Firsching
-/
module
public import LeanPool.Zeta32.Family
public import LeanPool.Zeta32.Arith.Local.Val
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The Bernoulli functional and the binomial basis

* `Lb Q = ∑ Q_n B_n` (`B₁ = -1/2`), `Lbp Q = ∑ Q_n B'_n` (`B'₁ = +1/2`), `Lbp Q = Lb Q + Q_1`;
* `bin k = x(x-1)⋯(x-k+1)/k!`, `Lb (bin k) = (-1)^k/(k+1)`, `derivative_bin`, `newton`;
* `BinRep`: combinations of `bin 0, …, bin k` with coefficients of valuation `≥ r`;
* `VG_polynomialMoment`: if `v_p((X q)(m)) ≥ β` for `0 ≤ m ≤ d`, `deg (X q) ≤ d`, `d + 1 < p²`
  and `r` is `p`-integral, then `v_p(polynomialMoment r q) ≥ β - 2`.
-/

@[expose] public section

-- adapted from mo271/Zeta5@f19a196:Apery/Arith/BinomBasis.lean
-- and .../Apery/Arith/TauBound.lean (mo271/Zeta5 by Moritz Firsching, Apache-2.0).
-- New here: the `bernoulli'` functional `Lbp` and the bound `VG_polynomialMoment` for the
-- polynomial part of our functional `U_r` (the proof notes, §0: `U_r(t^e) = (e+1)B_e + 2rB_{e+1}`).

open Finset Polynomial

namespace Zeta32.Arith.Local

/-- Polynomials over `ℚ` that agree at all natural numbers are equal. -/
lemma poly_eq_of_nat {P Q : ℚ[X]} (h : ∀ n : ℕ, P.eval (n : ℚ) = Q.eval (n : ℚ)) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℚ)) Nat.cast_injective
  intro n
  exact h n

/-! ### The Bernoulli functional -/

/-- `Lb Q = ∑_n Q_n B_n`. -/
noncomputable def Lb (Q : ℚ[X]) : ℚ := Q.sum fun n a => a * _root_.bernoulli n

lemma Lb_add (P Q : ℚ[X]) : Lb (P + Q) = Lb P + Lb Q := by
  unfold Lb
  exact Polynomial.sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)

lemma Lb_smul (c : ℚ) (Q : ℚ[X]) : Lb (c • Q) = c * Lb Q := by
  unfold Lb
  rw [Polynomial.sum_smul_index _ _ _ (fun _ => by simp), Polynomial.sum, Polynomial.sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => by ring

lemma Lb_C_mul (c : ℚ) (Q : ℚ[X]) : Lb (C c * Q) = c * Lb Q := by
  rw [← smul_eq_C_mul, Lb_smul]

lemma Lb_monomial (n : ℕ) (a : ℚ) : Lb (monomial n a) = a * _root_.bernoulli n := by
  unfold Lb
  rw [Polynomial.sum_monomial_index _ _ (by simp)]

lemma Lb_X_pow (n : ℕ) : Lb (X ^ n) = _root_.bernoulli n := by
  rw [← monomial_one_right_eq_X_pow, Lb_monomial, one_mul]

lemma Lb_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    Lb (∑ i ∈ s, f i) = ∑ i ∈ s, Lb (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Lb]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Lb_add, ih]

/-- **Shift identity**: `Lb (Q(x+1)) - Lb Q = Q'(0)`. -/
theorem Lb_shift (Q : ℚ[X]) : Lb (Q.comp (X + 1)) - Lb Q = Q.derivative.eval 0 := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [add_comp, Lb_add, Lb_add, derivative_add, eval_add, ← hP, ← hQ]; ring
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, Lb_C_mul, Lb_C_mul, Lb_X_pow,
      derivative_C_mul_X_pow, eval_C_mul, eval_pow, eval_X]
    rw [add_pow, Lb_sum]
    simp only [one_pow, mul_one]
    have e : ∀ k ∈ range (n + 1), Lb (X ^ k * (n.choose k : ℚ[X])) =
        (n.choose k : ℚ) * _root_.bernoulli k := by
      intro k _
      rw [show (X ^ k * (n.choose k : ℚ[X])) = C (n.choose k : ℚ) * X ^ k by
        rw [mul_comm]; simp, Lb_C_mul, Lb_X_pow]
    rw [Finset.sum_congr rfl e, Finset.sum_range_succ, _root_.sum_bernoulli, Nat.choose_self]
    rcases n with _ | n
    · simp
    · rcases n with _ | n
      · simp; ring
      · simp

/-- `Lbp Q = ∑_n Q_n B'_n` (the convention `B'₁ = +1/2` of `Zeta32.moment`). -/
noncomputable def Lbp (Q : ℚ[X]) : ℚ := Q.sum fun n a => a * bernoulli' n

lemma Lbp_add (P Q : ℚ[X]) : Lbp (P + Q) = Lbp P + Lbp Q := by
  unfold Lbp
  exact Polynomial.sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)

lemma Lbp_monomial (n : ℕ) (a : ℚ) : Lbp (monomial n a) = a * bernoulli' n := by
  unfold Lbp
  rw [Polynomial.sum_monomial_index _ _ (by simp)]

/-- `Lbp Q = Lb Q + Q_1`. -/
lemma Lbp_eq (Q : ℚ[X]) : Lbp Q = Lb Q + Q.coeff 1 := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => rw [Lbp_add, Lb_add, coeff_add, hP, hQ]; ring
  | monomial n a =>
    rw [Lbp_monomial, Lb_monomial, coeff_monomial]
    by_cases hn : n = 1
    · subst hn; rw [bernoulli'_one, bernoulli_one]; simp; ring
    · rw [ite_eq_right hn, bernoulli_eq_bernoulli'_of_ne_one hn]; ring

/-! ### The binomial basis -/

/-- `bin k = x(x-1)⋯(x-k+1)/k!`. -/
noncomputable def bin (k : ℕ) : ℚ[X] := C ((k.factorial : ℚ)⁻¹) * descPochhammer ℚ k

lemma bin_eval_nat (k m : ℕ) : (bin k).eval (m : ℚ) = (m.choose k : ℚ) := by
  unfold bin
  rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

lemma bin_zero : bin 0 = 1 := by simp [bin]

lemma bin_eval_zero {k : ℕ} (hk : 1 ≤ k) : (bin k).eval 0 = 0 := by
  have := bin_eval_nat k 0
  simp only [Nat.cast_zero] at this
  rw [this, Nat.choose_eq_zero_of_lt hk]; simp

/-- **Pascal**: `bin (k+1) (x+1) = bin (k+1) x + bin k x`. -/
lemma bin_comp_add_one (k : ℕ) : (bin (k + 1)).comp (X + 1) = bin (k + 1) + bin k := by
  apply poly_eq_of_nat
  intro m
  rw [eval_comp, eval_add, eval_X, eval_one, eval_add, show (m : ℚ) + 1 = ((m + 1 : ℕ) : ℚ) by
    push_cast; ring, bin_eval_nat, bin_eval_nat, bin_eval_nat, Nat.choose_succ_succ']
  push_cast; ring

lemma descPochhammer_eval_neg_one (n : ℕ) :
    (descPochhammer ℚ n).eval (-1) = (-1) ^ n * n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [descPochhammer_succ_right, eval_mul, ih, eval_sub, eval_X, eval_natCast,
      Nat.factorial_succ]
    push_cast; ring

/-- `bin_{k+1}'(0) = (-1)^k/(k+1)`. -/
lemma bin_derivative_eval_zero (k : ℕ) :
    (bin (k + 1)).derivative.eval 0 = (-1) ^ k / (k + 1 : ℚ) := by
  unfold bin
  rw [derivative_C_mul, eval_mul, eval_C, descPochhammer_succ_left, derivative_mul, derivative_X,
    one_mul, eval_add, eval_mul, eval_X, zero_mul, add_zero, eval_comp, eval_sub, eval_X,
    eval_one, zero_sub, descPochhammer_eval_neg_one, Nat.factorial_succ]
  push_cast
  field_simp

/-- `Lb (bin k) = (-1)^k/(k+1)`. -/
theorem Lb_bin (k : ℕ) : Lb (bin k) = (-1) ^ k / (k + 1 : ℚ) := by
  have h := Lb_shift (bin (k + 1))
  rw [bin_comp_add_one, Lb_add, bin_derivative_eval_zero] at h
  linarith

/-- A polynomial invariant under `x ↦ x + 1` is constant. -/
lemma eq_C_of_comp_add_one {Q : ℚ[X]} (h : Q.comp (X + 1) = Q) : Q = C (Q.eval 0) := by
  apply poly_eq_of_nat
  intro m
  rw [eval_C]
  induction m with
  | zero => simp
  | succ m ih =>
    have := congrArg (eval (m : ℚ)) h
    rw [eval_comp, eval_add, eval_X, eval_one] at this
    push_cast; rw [this, ih]

/-- The coefficients of the derivative in the binomial basis. -/
noncomputable def dcoef (j : ℕ) : ℚ := (-1) ^ (j - 1) / (j : ℚ)

/-- **Derivative of the binomial polynomials**. -/
theorem derivative_bin (k : ℕ) :
    (bin k).derivative = ∑ j ∈ Icc 1 k, C (dcoef j) * bin (k - j) := by
  induction k with
  | zero => simp [bin]
  | succ k ih =>
    set D := (bin (k + 1)).derivative - ∑ j ∈ Icc 1 (k + 1), C (dcoef j) * bin (k + 1 - j)
      with hD
    suffices hD0 : D = 0 by rw [hD] at hD0; exact sub_eq_zero.mp hD0
    have hcomp : D.comp (X + 1) = D := by
      rw [hD, sub_comp, Polynomial.sum_comp]
      have h1 : (bin (k + 1)).derivative.comp (X + 1) =
          (bin (k + 1)).derivative + (bin k).derivative := by
        have := congrArg derivative (bin_comp_add_one k)
        rw [derivative_comp, derivative_add, derivative_X, derivative_one, add_zero, one_mul,
          derivative_add] at this
        exact this
      rw [h1, ih]
      have h2 : ∀ j ∈ Icc 1 (k + 1), (C (dcoef j) * bin (k + 1 - j)).comp (X + 1) =
          C (dcoef j) * bin (k + 1 - j) + (if j ≤ k then C (dcoef j) * bin (k - j) else 0) := by
        intro j hj
        rw [mul_comp, C_comp]
        rw [Finset.mem_Icc] at hj
        split_ifs with hjk
        · obtain ⟨i, hi⟩ : ∃ i, k + 1 - j = i + 1 := ⟨k - j, by omega⟩
          rw [hi, bin_comp_add_one, show k - j = i by omega]; ring
        · have : k + 1 - j = 0 := by omega
          rw [this, bin_zero, one_comp]; simp
      rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib]
      have h3 : ∑ j ∈ Icc 1 (k + 1), (if j ≤ k then C (dcoef j) * bin (k - j) else 0) =
          ∑ j ∈ Icc 1 k, C (dcoef j) * bin (k - j) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
        congr 1
        ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
      rw [h3]; ring
    have h0 : D.eval 0 = 0 := by
      rw [hD, eval_sub, eval_finsetSum, bin_derivative_eval_zero,
        ← Finset.sum_erase_add _ _ (show k + 1 ∈ Icc 1 (k + 1) by simp)]
      rw [Finset.sum_eq_zero]
      · simp [bin_zero, dcoef]
      · intro j hj
        rw [Finset.mem_erase, Finset.mem_Icc] at hj
        rw [eval_mul, bin_eval_zero (by omega), mul_zero]
    rw [eq_C_of_comp_add_one hcomp, h0, C_0]

/-- **Newton expansion** of a polynomial in the binomial basis. -/
theorem newton (P : ℚ[X]) {d : ℕ} (hd : P.natDegree ≤ d) :
    P = ∑ k ∈ range (d + 1), C ((fwdDiff 1)^[k] P.eval 0) * bin k := by
  apply poly_eq_of_nat
  intro m
  have h := shift_eq_sum_fwdDiff_iter (h := (1 : ℚ)) P.eval m 0
  simp only [zero_add, nsmul_eq_mul, mul_one] at h
  rw [h, eval_finsetSum]
  simp only [eval_mul, eval_C, bin_eval_nat]
  have hz : ∀ k, d < k → (fwdDiff 1)^[k] P.eval 0 = 0 := fun k hk => by
    rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (by omega)]; rfl
  have hz' : ∀ k, m < k → (m.choose k : ℚ) = 0 := fun k hk => by
    rw [Nat.choose_eq_zero_of_lt hk]; simp
  have e1 : ∑ k ∈ range (m + 1), (m.choose k : ℚ) * (fwdDiff 1)^[k] P.eval 0 =
      ∑ k ∈ range (m + d + 1), (m.choose k : ℚ) * (fwdDiff 1)^[k] P.eval 0 := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro k hk hk'
    rw [Finset.mem_range] at hk hk'
    rw [hz' k (by omega), zero_mul]
  have e2 : ∑ k ∈ range (d + 1), (fwdDiff 1)^[k] P.eval 0 * (m.choose k : ℚ) =
      ∑ k ∈ range (m + d + 1), (fwdDiff 1)^[k] P.eval 0 * (m.choose k : ℚ) := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro k hk hk'
    rw [Finset.mem_range] at hk hk'
    rw [hz k (by omega), zero_mul]
  rw [e1, e2]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-! ### Valuations in the binomial basis -/

variable {p : ℕ} [hp : Fact p.Prime]

/-- `Q` is a combination of `bin 0, …, bin k` with coefficients of valuation `≥ r`. -/
def BinRep (p : ℕ) (k : ℕ) (r : ℚ) (Q : ℚ[X]) : Prop :=
  ∃ e : ℕ → ℚ, Q = ∑ m ∈ range (k + 1), C (e m) * bin m ∧ ∀ m ≤ k, VG p (e m) r

lemma derivative_bin' {k m : ℕ} (hm : m ≤ k) :
    (bin m).derivative =
      ∑ n ∈ range (k + 1), C (if n < m then dcoef (m - n) else 0) * bin n := by
  rw [derivative_bin]
  symm
  rw [← Finset.sum_filter_add_sum_filter_not (range (k + 1)) (fun n => n < m)]
  rw [Finset.sum_eq_zero (s := (range (k + 1)).filter fun n => ¬ n < m)
    (fun n hn => by rw [Finset.mem_filter] at hn; rw [ite_eq_right hn.2, C_0, zero_mul]), add_zero]
  apply Finset.sum_nbij' (fun n => m - n) (fun j => m - j)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    simp only [Finset.mem_Icc]; omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    simp only [Finset.mem_filter, Finset.mem_range]; omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn; omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj; omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    rw [ite_eq_left hn.2, show m - (m - n) = n by omega]

lemma VG_dcoef {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) : VG p (dcoef j) (-(Nat.log p k : ℚ)) := by
  unfold dcoef
  rw [div_eq_mul_inv]
  have h1 : VG p ((-1 : ℚ) ^ (j - 1)) 0 := by
    rcases neg_one_pow_eq_or ℚ (j - 1) with h | h <;> rw [h]
    · exact VG.one
    · exact VG.one.neg
  simpa using h1.mul (VG.inv_nat hj hjk)

/-- Differentiation loses at most `⌊log_p k⌋` in the binomial basis. -/
theorem BinRep.derivative {k : ℕ} {r : ℚ} {Q : ℚ[X]} (h : BinRep p k r Q) :
    BinRep p k (r - Nat.log p k) Q.derivative := by
  obtain ⟨e, rfl, he⟩ := h
  refine ⟨fun n => ∑ m ∈ range (k + 1), e m * (if n < m then dcoef (m - n) else 0), ?_, ?_⟩
  · rw [Polynomial.derivative_sum]
    simp_rw [derivative_mul, derivative_C, zero_mul, zero_add]
    rw [Finset.sum_congr rfl fun m hm => by
      rw [derivative_bin' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)), Finset.mul_sum]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [C_mul]; ring
  · intro n _
    apply VG.sum
    intro m hm
    have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    split_ifs with hnm
    · have := (he m hmk).mul (VG_dcoef (p := p) (j := m - n) (k := k) (by omega) (by omega))
      simpa [sub_eq_add_neg] using this
    · rw [mul_zero]; exact VG.zero _

/-- The Bernoulli functional loses at most `⌊log_p (k+1)⌋`. -/
theorem BinRep.Lb {k : ℕ} {r : ℚ} {Q : ℚ[X]} (h : BinRep p k r Q) :
    VG p (Lb Q) (r - Nat.log p (k + 1)) := by
  obtain ⟨e, rfl, he⟩ := h
  rw [Lb_sum]
  apply VG.sum
  intro m hm
  have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [Lb_C_mul, Lb_bin, div_eq_mul_inv]
  have h1 : VG p ((-1 : ℚ) ^ m) 0 := by
    rcases neg_one_pow_eq_or ℚ m with h | h <;> rw [h]
    · exact VG.one
    · exact VG.one.neg
  have h2 : VG p (((m : ℚ) + 1)⁻¹) (-(Nat.log p (k + 1) : ℚ)) := by
    have := VG.inv_nat (p := p) (j := m + 1) (n := k + 1) (by omega) (by omega)
    simpa using this
  have := (he m hmk).mul (h1.mul h2)
  simpa [sub_eq_add_neg] using this

omit hp in
lemma BinRep.mono {k : ℕ} {r s : ℚ} {Q : ℚ[X]} (h : BinRep p k r Q) (hs : s ≤ r) :
    BinRep p k s Q := by
  obtain ⟨e, he, hv⟩ := h
  exact ⟨e, he, fun m hm => (hv m hm).mono hs⟩

/-- The value at `0` of a binomial representation is its `0`-th coefficient. -/
lemma BinRep.eval_zero {k : ℕ} {r : ℚ} {Q : ℚ[X]} (h : BinRep p k r Q) : VG p (Q.eval 0) r := by
  obtain ⟨e, rfl, he⟩ := h
  rw [eval_finsetSum]
  apply VG.sum
  intro m hm
  have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [eval_mul, eval_C]
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; rw [bin_zero, eval_one, mul_one]; exact he 0 hmk
  · rw [bin_eval_zero h0, mul_zero]; exact VG.zero _

/-- Values at `0, …, d` give a binomial representation. -/
theorem binRep_of_values {P : ℚ[X]} {d : ℕ} (hd : P.natDegree ≤ d) {β : ℚ}
    (hv : ∀ m ≤ d, VG p (P.eval (m : ℚ)) β) : BinRep p d β P := by
  refine ⟨fun k => (fwdDiff 1)^[k] P.eval 0, newton P hd, fun k hk => ?_⟩
  change VG p ((fwdDiff 1)^[k] P.eval 0) β
  rw [fwdDiff_iter_eq_sum_shift]
  apply VG.sum
  intro j hj
  have hjd : j ≤ d := by have := Finset.mem_range.mp hj; omega
  rw [zero_add, zsmul_eq_mul, nsmul_eq_mul, mul_one]
  have h1 : VG p (((-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) : ℤ) : ℚ) 0 := VG.intCast _
  have := h1.mul (hv j hjd)
  simpa using this

/-! ### The polynomial part of `U_r` -/

/-- `polynomialMoment r q = Lbp ((X q)') + 2 r Lbp (X q)`. -/
lemma polynomialMoment_eq (r : ℚ) (q : ℚ[X]) :
    polynomialMoment r q = Lbp (derivative (X * q)) + 2 * r * Lbp (X * q) := by
  induction q using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have hadd : polynomialMoment r (P + Q) = polynomialMoment r P + polynomialMoment r Q := by
      unfold polynomialMoment
      exact Polynomial.sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)
    rw [hadd, hP, hQ, mul_add, derivative_add, Lbp_add, Lbp_add]; ring
  | monomial n a =>
    have h1 : polynomialMoment r (monomial n a) = a * moment r n := by
      unfold polynomialMoment
      rw [Polynomial.sum_monomial_index _ _ (by simp)]
    rw [h1, X_mul_monomial, derivative_monomial, Lbp_monomial, Lbp_monomial,
      show n + 1 - 1 = n by omega, moment]
    push_cast; ring

omit hp in
lemma nat_log_le_one {d : ℕ} (hdp : d + 1 < p ^ 2) : Nat.log p (d + 1) ≤ 1 :=
  Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) hdp)

/-- **Polynomial part**: loss at most `2`. -/
theorem VG_polynomialMoment {r : ℚ} (hr : VG p r 0) {q : ℚ[X]} {d : ℕ}
    (hd : (X * q).natDegree ≤ d) (hdp : d + 1 < p ^ 2) {β : ℚ}
    (hv : ∀ m ≤ d, VG p ((X * q).eval (m : ℚ)) β) :
    VG p (polynomialMoment r q) (β - 2) := by
  have hl1 : (Nat.log p (d + 1) : ℚ) ≤ 1 := by exact_mod_cast nat_log_le_one hdp
  have hl0 : (Nat.log p d : ℚ) ≤ 1 := by
    have : Nat.log p d ≤ Nat.log p (d + 1) := Nat.log_mono_right (Nat.le_succ d)
    have h2 := nat_log_le_one (p := p) hdp
    exact_mod_cast this.trans h2
  have h0 : BinRep p d β (X * q) := binRep_of_values hd hv
  have h1 : BinRep p d (β - 1) (derivative (X * q)) := h0.derivative.mono (by linarith)
  have h2 : BinRep p d (β - 2) (derivative (derivative (X * q))) :=
    h1.derivative.mono (by linarith)
  -- `Lbp` of the derivative
  have hA : VG p (Lbp (derivative (X * q))) (β - 2) := by
    rw [Lbp_eq]
    refine VG.add (h1.Lb.mono (by linarith)) ?_
    have := h2.eval_zero
    rw [← coeff_zero_eq_eval_zero, coeff_derivative] at this
    simpa using this
  have hB : VG p (Lbp (X * q)) (β - 1) := by
    rw [Lbp_eq]
    refine VG.add (h0.Lb.mono (by linarith)) ?_
    have := h1.eval_zero
    rw [← coeff_zero_eq_eval_zero, coeff_derivative] at this
    simpa using this
  have h2r : VG p (2 * r) 0 := by
    have := (VG.natCast (p := p) 2).mul hr
    simpa using this
  rw [polynomialMoment_eq]
  refine hA.add ?_
  have := h2r.mul hB
  exact this.mono (by linarith)

end Zeta32.Arith.Local

end
