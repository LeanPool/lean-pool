/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Data.Nat.Choose.Lucas


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Hasse derivatives and multiplicities

Proves the Hasse-derivative root criterion, multiplicity bounds, and degree control
for auxiliary-polynomial derivatives. Reference: Harcos (2015), §4, equations
(14)–(15) and Lemmas 8–10; Stepanov (1972).
-/

@[expose] public section

open scoped BigOperators

namespace KloostermanWeil.Stepanov

open Polynomial

/-- A point has multiplicity at least `l` exactly when its first `l` Hasse
derivatives vanish.  This is Stepanov's Hasse-derivative criterion. -/
theorem hasseRootMultiplicityCriterion {F : Type*} [Field F]
    (h : F[X]) (x : F) (l : ℕ) :
    (X - C x) ^ l ∣ h ↔
      ∀ k < l, (hasseDeriv k h).eval x = 0 := by
  rw [X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
  constructor
  · intro hd k hk
    have := hd k hk
    simpa only [← taylor_apply, taylor_coeff] using this
  · intro hd k hk
    simpa only [← taylor_apply, taylor_coeff] using hd k hk

/-- If every point in `S` is a root of multiplicity at least `l` of a
nonzero polynomial, then `l * #S` is at most its degree.  This is the exact
counting step in Stepanov inequality (14). -/
theorem card_mul_le_natDegree_of_uniform_rootMultiplicity
    {F : Type*} [Field F] (h : F[X]) (hh : h ≠ 0)
    (S : Finset F) {l : ℕ} (hl : 0 < l)
    (hS : ∀ x ∈ S, (X - C x) ^ l ∣ h) :
    l * S.card ≤ h.natDegree := by
  classical
  have hmult : ∀ x ∈ S, l ≤ h.roots.count x := by
    intro x hx
    rw [count_roots]
    exact (le_rootMultiplicity_iff hh).2 (hS x hx)
  have hsubset : S ⊆ h.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset]
    rw [← Multiset.count_pos]
    exact hl.trans_le (hmult x hx)
  calc
    l * S.card = ∑ _x ∈ S, l := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ S, h.roots.count x := by
      exact Finset.sum_le_sum fun x hx => hmult x hx
    _ ≤ ∑ x ∈ h.roots.toFinset, h.roots.count x := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by omega)
    _ = h.roots.card := Multiset.toFinset_sum_count_eq h.roots
    _ ≤ h.natDegree := card_roots' h

/-- The `k`th Hasse derivative of `g * f^n` retains at least `n-k`
factors of `f`.  This is the divisibility part of Stepanov's Lemma 10. -/
theorem pow_sub_dvd_hasseDeriv_mul_pow {F : Type*} [Field F]
    (f g : F[X]) {n k : ℕ} (hk : k ≤ n) :
    f ^ (n - k) ∣ hasseDeriv k (g * f ^ n) := by
  induction n generalizing k g with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      simp
  | succ n ih =>
      rw [show g * f ^ (n + 1) = (g * f ^ n) * f by ring]
      rw [hasseDeriv_mul]
      apply Finset.dvd_sum
      intro ij hij
      rw [Finset.mem_antidiagonal] at hij
      by_cases hi : ij.1 ≤ n
      · obtain ⟨u, hu⟩ := ih (g := g) hi
        rw [hu]
        by_cases hj : ij.2 = 0
        · simp only [hj, add_zero] at *
          simp only [hasseDeriv_zero']
          have hsub : n + 1 - ij.1 = (n - ij.1) + 1 := by omega
          rw [← hij]
          rw [hsub, pow_succ]
          refine ⟨u, ?_⟩
          ring
        · have hjpos : 0 < ij.2 := Nat.pos_of_ne_zero hj
          have hle : n + 1 - k ≤ n - ij.1 := by omega
          exact dvd_mul_of_dvd_left
            (dvd_mul_of_dvd_left (pow_dvd_pow f hle) u)
            (hasseDeriv ij.2 f)
      · have hi' : ij.1 = n + 1 := by omega
        have hk' : k = n + 1 := by omega
        simp [hk']

/-- Cancellation-safe form of the degree conclusion in Stepanov's Lemma 10.
The displayed inequality is equivalent to
`deg u ≤ deg g + k * deg f - k`. -/
theorem hasseDeriv_mul_pow_factor_degree {F : Type*} [Field F]
    (f g : F[X]) (hf : f ≠ 0) (hfdeg : 0 < f.natDegree)
    {n k : ℕ} (hk : k ≤ n) :
    ∃ u : F[X],
      hasseDeriv k (g * f ^ n) = f ^ (n - k) * u ∧
        u.natDegree + k ≤ g.natDegree + k * f.natDegree := by
  by_cases hD : hasseDeriv k (g * f ^ n) = 0
  · refine ⟨0, ?_, ?_⟩
    · rw [hD]
      simp
    simp only [natDegree_zero, zero_add]
    nlinarith
  · obtain ⟨u, hu⟩ := pow_sub_dvd_hasseDeriv_mul_pow f g hk
    have hu0 : u ≠ 0 := by
      intro hu0
      apply hD
      rw [hu, hu0, mul_zero]
    have hg0 : g ≠ 0 := by
      intro hg0
      apply hD
      simp [hg0]
    have hsource : k ≤ (g * f ^ n).natDegree := by
      by_contra hkn
      have hlt : (g * f ^ n).natDegree < k := Nat.lt_of_not_ge hkn
      exact hD (hasseDeriv_eq_zero_of_lt_natDegree _ _ hlt)
    have hdegree0 := natDegree_hasseDeriv_le (g * f ^ n) k
    have hdegree : (hasseDeriv k (g * f ^ n)).natDegree + k ≤
        (g * f ^ n).natDegree := by omega
    rw [hu, natDegree_mul (pow_ne_zero _ hf) hu0, natDegree_pow,
      natDegree_mul hg0 (pow_ne_zero _ hf), natDegree_pow] at hdegree
    have hn : n = (n - k) + k := by omega
    have hnmul : n * f.natDegree =
        (n - k) * f.natDegree + k * f.natDegree := by
      exact (congrArg (fun a : ℕ => a * f.natDegree) hn).trans
        (Nat.add_mul (n - k) k f.natDegree)
    rw [hnmul] at hdegree
    refine ⟨u, hu, ?_⟩
    omega

/-- Canonical quotient after removing the guaranteed factor `f^(n-k)` from
the Hasse derivative. -/
noncomputable def hassePowerQuotient {F : Type*} [Field F]
    (f : F[X]) {n k : ℕ} (hk : k ≤ n) (g : F[X]) : F[X] :=
  Classical.choose (pow_sub_dvd_hasseDeriv_mul_pow f g hk)

/-- Exact factorization defining `hassePowerQuotient`. -/
theorem hassePowerQuotient_spec {F : Type*} [Field F]
    (f : F[X]) {n k : ℕ} (hk : k ≤ n) (g : F[X]) :
    hasseDeriv k (g * f ^ n) =
      f ^ (n - k) * hassePowerQuotient f hk g :=
  Classical.choose_spec (pow_sub_dvd_hasseDeriv_mul_pow f g hk)

/-- For fixed `f`, `n`, and `k`, the quotient in Stepanov's Lemma 10 depends
linearly on `g`. -/
noncomputable def hassePowerQuotientLinearMap {F : Type*} [Field F]
    (f : F[X]) (hf : f ≠ 0) {n k : ℕ} (hk : k ≤ n) :
    F[X] →ₗ[F] F[X] where
  toFun := hassePowerQuotient f hk
  map_add' g h := by
    apply mul_left_cancel₀ (pow_ne_zero (n - k) hf)
    rw [← hassePowerQuotient_spec f hk]
    rw [show (g + h) * f ^ n = g * f ^ n + h * f ^ n by ring]
    rw [map_add]
    rw [hassePowerQuotient_spec f hk,
      hassePowerQuotient_spec f hk]
    ring
  map_smul' c g := by
    apply mul_left_cancel₀ (pow_ne_zero (n - k) hf)
    rw [← hassePowerQuotient_spec f hk]
    rw [show (c • g) * f ^ n = c • (g * f ^ n) by
      simp [smul_eq_C_mul]
      ring]
    rw [map_smul]
    rw [hassePowerQuotient_spec f hk]
    simp only [smul_eq_C_mul]
    rw [RingHom.id_apply]
    ring

/-- Degree bound for the canonical quotient, in the cancellation-safe form
of Stepanov's inequality (16). -/
theorem hassePowerQuotient_natDegree {F : Type*} [Field F]
    (f g : F[X]) (hf : f ≠ 0) (hfdeg : 0 < f.natDegree)
    {n k : ℕ} (hk : k ≤ n) :
    (hassePowerQuotient f hk g).natDegree + k ≤
      g.natDegree + k * f.natDegree := by
  obtain ⟨u, hu, hdeg⟩ := hasseDeriv_mul_pow_factor_degree f g hf hfdeg hk
  have heq : hassePowerQuotient f hk g = u := by
    apply mul_left_cancel₀ (pow_ne_zero (n - k) hf)
    rw [← hassePowerQuotient_spec f hk, ← hu]
  simpa only [heq] using hdeg

/-- Lucas-theorem divisibility needed to show that the `k`th Hasse
derivative does not see an `X^(j*q)` block when `q` is a prime power and
`0 < k < q`. -/
theorem prime_dvd_choose_mul_prime_pow
    {p : ℕ} (hp : p.Prime) (n j k : ℕ)
    (hk0 : 0 < k) (hk : k < p ^ n) :
    p ∣ (j * p ^ n).choose k := by
  induction n generalizing j k with
  | zero => simp at hk; omega
  | succ n ih =>
      let : Fact p.Prime := ⟨hp⟩
      have hp0 : 0 < p := hp.pos
      have hmod := @Choose.choose_modEq_choose_mod_mul_choose_div_nat
        (j * p ^ (n + 1)) k p inferInstance
      have hNmod : j * p ^ (n + 1) % p = 0 := by
        apply Nat.dvd_iff_mod_eq_zero.mp
        rw [pow_succ]
        simpa [mul_assoc] using dvd_mul_left p (j * p ^ n)
      rw [hNmod] at hmod
      by_cases hkmod : k % p = 0
      · have hpk : p ∣ k := Nat.dvd_of_mod_eq_zero hkmod
        have hkdiv0 : 0 < k / p :=
          Nat.div_pos (Nat.le_of_dvd hk0 hpk) hp0
        have hkdiv : k / p < p ^ n := by
          apply (Nat.div_lt_iff_lt_mul hp0).2
          simpa [pow_succ] using hk
        have hNdiv : j * p ^ (n + 1) / p = j * p ^ n := by
          calc
            j * p ^ (n + 1) / p = (j * p ^ n) * p / p := by
              simp only [pow_succ, mul_assoc]
            _ = j * p ^ n := by
              rw [mul_comm]
              exact Nat.mul_div_cancel_left _ hp0
        have hd := ih (j := j) (k := k / p) hkdiv0 hkdiv
        rw [hkmod, Nat.choose_zero_right, one_mul, hNdiv] at hmod
        exact Nat.modEq_zero_iff_dvd.mp
          (hmod.trans (Nat.modEq_zero_iff_dvd.mpr hd))
      · have hkmodpos : 0 < k % p := Nat.pos_of_ne_zero hkmod
        have hchoose : (0 : ℕ).choose (k % p) = 0 :=
          Nat.choose_eq_zero_of_lt hkmodpos
        rw [hchoose, zero_mul] at hmod
        exact Nat.modEq_zero_iff_dvd.mp hmod

/-- A positive Hasse derivative below `q=p^n` annihilates every Frobenius
block `X^(j*q)`. -/
theorem hasseDeriv_X_mul_prime_pow_eq_zero
    {F : Type*} [Field F] {p n j k : ℕ}
    [Fact p.Prime] [CharP F p] (hk0 : 0 < k) (hk : k < p ^ n) :
    hasseDeriv k (X ^ (j * p ^ n) : F[X]) = 0 := by
  rw [X_pow_eq_monomial, hasseDeriv_monomial]
  have hdvd : p ∣ (j * p ^ n).choose k :=
    prime_dvd_choose_mul_prime_pow Fact.out n j k hk0 hk
  have hcast : ((j * p ^ n).choose k : F) = 0 :=
    (CharP.cast_eq_zero_iff F p _).2 hdvd
  rw [hcast, zero_mul, monomial_zero_right]

/-- Below the prime-power block size, Hasse differentiation acts only on
the coefficient polynomial in `g * X^(j*q)`.  This is the exact identity
used to pass from equation (18) to equation (20). -/
theorem hasseDeriv_mul_X_mul_prime_pow
    {F : Type*} [Field F] {p n j k : ℕ}
    [Fact p.Prime] [CharP F p] (hk : k < p ^ n) (g : F[X]) :
    hasseDeriv k (g * X ^ (j * p ^ n)) =
      hasseDeriv k g * X ^ (j * p ^ n) := by
  rw [hasseDeriv_mul]
  rw [Finset.sum_eq_single (k, 0)]
  · simp
  · intro a ha hane
    rw [Finset.mem_antidiagonal] at ha
    by_cases ha2 : a.2 = 0
    · exfalso
      apply hane
      ext <;> omega
    · have ha2pos : 0 < a.2 := Nat.pos_of_ne_zero ha2
      have ha2lt : a.2 < p ^ n := by omega
      rw [hasseDeriv_X_mul_prime_pow_eq_zero ha2pos ha2lt, mul_zero]
  · simp

end KloostermanWeil.Stepanov
