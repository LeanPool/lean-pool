/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.RingTheory.Polynomial.Vieta


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Spectral estimates from power sums

Bounds spectral roots through Newton identities and Cauchy’s root bound, following
Harcos (2015), §3 and equations (2)–(3).
-/

@[expose] public section

namespace KloostermanWeil.Stepanov

open scoped BigOperators

open Finset

noncomputable section

theorem aeval_psum_complex {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (k : ℕ) :
    MvPolynomial.aeval z (MvPolynomial.psum ι ℂ k) = ∑ i, z i ^ k := by
  simp [MvPolynomial.psum]

theorem evaluated_newton_identity {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (k : ℕ) :
    (k : ℂ) * (Finset.univ.val.map z).esymm k =
      (-1 : ℂ) ^ (k + 1) *
        ∑ a ∈ Finset.antidiagonal k with a.1 < k,
          (-1 : ℂ) ^ a.1 * (Finset.univ.val.map z).esymm a.1 *
            ∑ i, z i ^ a.2 := by
  have h := congrArg (MvPolynomial.eval z)
    (MvPolynomial.mul_esymm_eq_sum ι ℂ k)
  simpa [MvPolynomial.esymm, MvPolynomial.psum,
    Finset.esymm_map_val] using h

theorem card_newton_antidiagonal (k : ℕ) :
    #{a ∈ Finset.antidiagonal k | a.1 < k} = k := by
  have heq : {a ∈ Finset.antidiagonal k | a.1 < k} =
      (Finset.antidiagonal k).erase (k, 0) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨ha, hak⟩
      exact ⟨by
        intro hae
        subst a
        simp at hak, ha⟩
    · rintro ⟨hane, ha⟩
      refine ⟨ha, ?_⟩
      have hasum : a.1 + a.2 = k := Finset.mem_antidiagonal.mp ha
      have hale : a.1 ≤ k := by omega
      exact lt_of_le_of_ne hale (by
        intro hae
        apply hane
        apply Prod.ext
        · exact hae
        · omega)
  rw [heq, Finset.card_erase_of_mem]
  · simp
  · exact Finset.mem_antidiagonal.mpr (by simp)

/-- Newton's identities bound every elementary symmetric function of the
powered family uniformly in the outer power. -/
theorem norm_esymm_power_le {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (C : ℝ) (hC : 1 ≤ C)
    (hpower : ∀ n : ℕ, 0 < n → ‖∑ i, z i ^ n‖ ≤ C)
    (N k : ℕ) (hN : 0 < N) :
    ‖(Finset.univ.val.map fun i => z i ^ N).esymm k‖ ≤ C ^ k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk : k = 0
      · subst k
        rw [Finset.esymm_map_val]
        simp
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hnewton := evaluated_newton_identity (fun i => z i ^ N) k
      have hterm : ∀ a ∈ Finset.antidiagonal k, a.1 < k →
          ‖(-1 : ℂ) ^ a.1 *
              (Finset.univ.val.map fun i => z i ^ N).esymm a.1 *
                ∑ i, (z i ^ N) ^ a.2‖ ≤ C ^ k := by
        intro a ha hak
        have hasum : a.1 + a.2 = k := Finset.mem_antidiagonal.mp ha
        have ha2 : 0 < a.2 := by omega
        have hpow : ‖∑ i, z i ^ (N * a.2)‖ ≤ C :=
          hpower (N * a.2) (Nat.mul_pos hN ha2)
        have hesymm := ih a.1 hak
        simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        rw [show (∑ i, (z i ^ N) ^ a.2) = ∑ i, z i ^ (N * a.2) by
          apply Finset.sum_congr rfl
          intro i _
          rw [← pow_mul]]
        calc
          ‖(Finset.univ.val.map fun i => z i ^ N).esymm a.1‖ *
              ‖∑ i, z i ^ (N * a.2)‖
              ≤ C ^ a.1 * C := mul_le_mul hesymm hpow (norm_nonneg _) (by positivity)
          _ = C ^ (a.1 + 1) := by rw [pow_succ]
          _ ≤ C ^ k := by
            exact pow_le_pow_right₀ hC (by omega)
      have hsum :
          ‖∑ a ∈ Finset.antidiagonal k with a.1 < k,
              (-1 : ℂ) ^ a.1 *
                (Finset.univ.val.map fun i => z i ^ N).esymm a.1 *
                  ∑ i, (z i ^ N) ^ a.2‖ ≤ k * C ^ k := by
        calc
          ‖∑ a ∈ Finset.antidiagonal k with a.1 < k,
              (-1 : ℂ) ^ a.1 *
                (Finset.univ.val.map fun i => z i ^ N).esymm a.1 *
                  ∑ i, (z i ^ N) ^ a.2‖
              ≤ ∑ a ∈ Finset.antidiagonal k with a.1 < k,
                  ‖(-1 : ℂ) ^ a.1 *
                    (Finset.univ.val.map fun i => z i ^ N).esymm a.1 *
                      ∑ i, (z i ^ N) ^ a.2‖ := by
                exact norm_sum_le _ _
          _ ≤ ∑ _a ∈ Finset.antidiagonal k with _a.1 < k, C ^ k := by
                exact Finset.sum_le_sum fun a ha => hterm a
                  (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
          _ = k * C ^ k := by
                simp [card_newton_antidiagonal]
      have hleft :
          (k : ℝ) * ‖(Finset.univ.val.map fun i => z i ^ N).esymm k‖ ≤
            k * C ^ k := by
        calc
          (k : ℝ) * ‖(Finset.univ.val.map fun i => z i ^ N).esymm k‖ =
              ‖(k : ℂ) * (Finset.univ.val.map fun i => z i ^ N).esymm k‖ := by
                simp
          _ = ‖(-1 : ℂ) ^ (k + 1) *
                ∑ a ∈ Finset.antidiagonal k with a.1 < k,
                  (-1 : ℂ) ^ a.1 *
                    (Finset.univ.val.map fun i => z i ^ N).esymm a.1 *
                      ∑ i, (z i ^ N) ^ a.2‖ := by rw [hnewton]
          _ = ‖∑ a ∈ Finset.antidiagonal k with a.1 < k,
                  (-1 : ℂ) ^ a.1 *
                    (Finset.univ.val.map fun i => z i ^ N).esymm a.1 *
                      ∑ i, (z i ^ N) ^ a.2‖ := by simp
          _ ≤ k * C ^ k := hsum
      have hkreal : (0 : ℝ) < k := Nat.cast_pos.mpr hkpos
      nlinarith

/-- A finite complex family with uniformly bounded positive power sums lies
in the closed unit disk. -/
theorem norm_le_one_of_power_sums_bounded {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (C : ℝ) (hC : 1 ≤ C)
    (hpower : ∀ n : ℕ, 0 < n → ‖∑ i, z i ^ n‖ ≤ C)
    (i : ι) : ‖z i‖ ≤ 1 := by
  let d := Fintype.card ι
  have hCnonneg : 0 ≤ C := zero_le_one.trans hC
  have hpowered : ∀ N : ℕ, 0 < N → ‖z i‖ ^ N < C ^ d + 1 := by
    intro N hN
    let pN : Polynomial ℂ :=
      ∏ j : ι, (Polynomial.X - Polynomial.C (z j ^ N))
    have hpNmonic : pN.Monic := by
      simpa [pN] using
        Polynomial.monic_prod_X_sub_C (fun j => z j ^ N) Finset.univ
    have hpNne : pN ≠ 0 := hpNmonic.ne_zero
    have hpNdegree : pN.natDegree = d := by
      simpa [pN, d] using
        (Polynomial.natDegree_finsetProd_X_sub_C_eq_card
          (R := ℂ) Finset.univ (fun j : ι => z j ^ N))
    have hroot : pN.IsRoot (z i ^ N) := by
      rw [Polynomial.IsRoot.def]
      rw [show pN = ∏ j : ι,
        (Polynomial.X - Polynomial.C (z j ^ N)) by rfl]
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp
    have hcoeff : ∀ k ∈ Finset.range pN.natDegree,
        ‖pN.coeff k‖₊ ≤ ⟨C ^ d, pow_nonneg hCnonneg d⟩ := by
      intro k hk
      have hkd : k < d := by simpa [hpNdegree] using hk
      have hkcard : k ≤
          (Finset.univ.val.map fun j : ι => z j ^ N).card := by
        simpa using hkd.le
      have hvieta : pN.coeff k =
          (-1 : ℂ) ^ (Fintype.card ι - k) *
            (Finset.univ.val.map fun j => z j ^ N).esymm
              (Fintype.card ι - k) := by
        simpa [pN] using
          (Multiset.prod_X_sub_C_coeff
            (Finset.univ.val.map fun j => z j ^ N) hkcard)
      rw [hvieta]
      simp only [nnnorm_mul, nnnorm_pow, nnnorm_neg, nnnorm_one, one_pow, one_mul]
      exact_mod_cast (calc
          ‖(Finset.univ.val.map fun j => z j ^ N).esymm
                (Fintype.card ι - k)‖
              ≤ C ^ (Fintype.card ι - k) :=
                norm_esymm_power_le z C hC hpower N _ hN
          _ ≤ C ^ d := pow_le_pow_right₀ hC (by simp [d]))
    have hcauchy : pN.cauchyBound ≤
        1 + ⟨C ^ d, pow_nonneg hCnonneg d⟩ := by
      rw [Polynomial.cauchyBound, hpNmonic.leadingCoeff, nnnorm_one, div_one]
      simpa [add_comm] using add_le_add_right (Finset.sup_le hcoeff) 1
    have hrootBound := Polynomial.IsRoot.norm_lt_cauchyBound hpNne hroot
    have hnormpow : ‖z i ^ N‖₊ <
        1 + ⟨C ^ d, pow_nonneg hCnonneg d⟩ := hrootBound.trans_le hcauchy
    have hnormpowR :
        (‖z i ^ N‖₊ : ℝ) <
          ((1 + ⟨C ^ d, pow_nonneg hCnonneg d⟩ : NNReal) : ℝ) :=
      (NNReal.coe_lt_coe).2 hnormpow
    change ‖z i ^ N‖ < 1 + C ^ d at hnormpowR
    simpa [norm_pow, add_comm] using hnormpowR
  by_contra hi
  have hi1 : 1 < ‖z i‖ := lt_of_not_ge hi
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (C ^ d + 1) hi1
  have hNpos : 0 < N := by
    by_contra hNzero
    have : N = 0 := Nat.eq_zero_of_not_pos hNzero
    subst N
    simp only [pow_zero] at hN
    nlinarith [pow_nonneg hCnonneg d]
  exact (hpowered N hNpos).asymm hN

/-- It is enough that the power-sum bound hold from one exponent onward. -/
theorem norm_le_one_of_power_sums_eventually {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (C : ℝ) (hC : 1 ≤ C) (n₀ : ℕ)
    (hpower : ∀ n : ℕ, n₀ ≤ n → ‖∑ i, z i ^ n‖ ≤ C)
    (i : ι) : ‖z i‖ ≤ 1 := by
  let K := n₀ + 1
  have hK : 0 < K := by simp [K]
  have hpowK : ‖z i ^ K‖ ≤ 1 :=
    norm_le_one_of_power_sums_bounded (fun j => z j ^ K) C hC (by
      intro n hn
      rw [show (∑ j, (z j ^ K) ^ n) = ∑ j, z j ^ (K * n) by
        apply Finset.sum_congr rfl
        intro j _
        rw [← pow_mul]]
      apply hpower
      have : K ≤ K * n := by
        nth_rewrite 1 [← mul_one K]
        exact Nat.mul_le_mul_left K hn
      exact n₀.le_succ.trans this) i
  rw [norm_pow] at hpowK
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hK.ne').mp hpowK

/-- Radius-scaled version of the eventual finite power-sum criterion. -/
theorem norm_le_radius_of_power_sums_eventually {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (r C : ℝ) (hr : 0 < r) (hC : 1 ≤ C) (n₀ : ℕ)
    (hpower : ∀ n : ℕ, n₀ ≤ n → ‖∑ i, z i ^ n‖ ≤ C * r ^ n)
    (i : ι) : ‖z i‖ ≤ r := by
  let w : ι → ℂ := fun j => z j / (r : ℂ)
  have hw : ‖w i‖ ≤ 1 := norm_le_one_of_power_sums_eventually w C hC n₀ (by
    intro n hn
    have hrpow : 0 < r ^ n := pow_pos hr n
    rw [show (∑ j, w j ^ n) = (∑ j, z j ^ n) / (r : ℂ) ^ n by
      simp only [w, div_pow, Finset.sum_div]]
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact (div_le_iff₀ hrpow).2 (hpower n hn)) i
  rw [show w i = z i / (r : ℂ) by rfl, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr] at hw
  exact (div_le_one hr).mp hw

end

end KloostermanWeil.Stepanov
