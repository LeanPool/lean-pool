/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Hasse derivatives in prime characteristic

Over a ring of prime characteristic `p`, the Hasse derivatives `hasseDeriv k f` of orders
`0 < k < p ^ e` all vanish if and only if `f` is a polynomial in `X ^ (p ^ e)`. The input from
combinatorics is that `p ^ e ∣ n` if and only if `p` divides `choose n k` for all `0 < k < p ^ e`.

## Main statements

* `Choose.pow_dvd_iff_forall_dvd_choose`: `p ^ e ∣ n ↔ ∀ k, 0 < k → k < p ^ e → p ∣ choose n k`.
* `Polynomial.hasseDeriv_eq_zero_iff`, `Polynomial.hasseDeriv_mul_of_forall_hasseDeriv_eq_zero`.
* `Polynomial.forall_hasseDeriv_eq_zero_iff`: the Hasse derivatives of `f` of orders
  `0 < k < p ^ e` vanish if and only if `p ^ e` divides every exponent of `f`.
* `Polynomial.forall_hasseDeriv_eq_zero_iff_exists_expand`: the same condition holds if and only if
  `f = expand R (p ^ e) g` for some `g`.
* `Polynomial.hasseDeriv_X_pow_mul`, `Polynomial.hasseDeriv_expand_mul`: for `k < p ^ e`,
  `hasseDeriv k` is linear over polynomials in `X ^ (p ^ e)`.
-/

public section

noncomputable section

namespace Polynomial

open Nat

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

/-- `hasseDeriv k f` vanishes iff `(n.choose k) * f.coeff n = 0` for every `n`. -/
theorem hasseDeriv_eq_zero_iff : hasseDeriv k f = 0 ↔ ∀ n, (n.choose k : R) * f.coeff n = 0 := by
  refine ⟨fun h n ↦ ?_,
    fun h ↦ AddMonoidAlgebra.ext <| Finsupp.ext fun n ↦ by
      rw [hasseDeriv_coeff, coeff_zero, h]⟩
  rcases lt_or_ge n k with hn | hn
  · simp [Nat.choose_eq_zero_of_lt hn]
  · simpa [hasseDeriv_coeff, Nat.sub_add_cancel hn] using congr(AddMonoidAlgebra.coeff $h (n - k))

/-- If the Hasse derivatives of `f` of orders `0 < i ≤ k` vanish, then
`hasseDeriv k (f * g) = f * hasseDeriv k g`. -/
theorem hasseDeriv_mul_of_forall_hasseDeriv_eq_zero
    (hf : ∀ i, 0 < i → i ≤ k → hasseDeriv i f = 0) (g : R[X]) :
    hasseDeriv k (f * g) = f * hasseDeriv k g := by
  rw [hasseDeriv_mul, Finset.sum_eq_single (0, k)]
  · rw [hasseDeriv_zero']
  · rintro ⟨i, j⟩ hij hne
    replace hij : i + j = k := by simpa using hij
    have hi : i ≠ 0 := by rintro rfl; simp_all
    rw [hf i (Nat.pos_of_ne_zero hi) (by lia), zero_mul]
  · simp

end Polynomial

end

namespace Choose

open Nat

variable {n p : ℕ} [Fact p.Prime]

/-- For primes `p`, `p ^ e` divides `n` if and only if `p` divides `choose n k` for all
`0 < k < p ^ e`. -/
theorem pow_dvd_iff_forall_dvd_choose {e : ℕ} :
    p ^ e ∣ n ↔ ∀ k, 0 < k → k < p ^ e → p ∣ choose n k := by
  have hp : p.Prime := Fact.out
  constructor
  · induction e generalizing n with
    | zero => intro _ k hk hk'; lia
    | succ e ih =>
      intro hn k hk hk'
      have hpn : p ∣ n := (dvd_pow_self p e.succ_ne_zero).trans hn
      rw [(choose_modEq_choose_mod_mul_choose_div_nat (p := p)).dvd_iff dvd_rfl,
        Nat.mod_eq_zero_of_dvd hpn]
      by_cases hkp : k % p = 0
      · obtain ⟨n, rfl⟩ := hpn
        obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero hkp
        rw [Nat.pow_succ', Nat.mul_dvd_mul_iff_left hp.pos] at hn
        rw [Nat.pow_succ', Nat.mul_lt_mul_left hp.pos] at hk'
        rw [Nat.mul_div_cancel_left _ hp.pos, Nat.mul_div_cancel_left _ hp.pos]
        exact dvd_mul_of_dvd_right (ih hn k (Nat.pos_of_mul_pos_left hk) hk') _
      · simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hkp)]
  · intro h
    by_contra hn
    obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := n)
      (by rintro rfl; exact hn (dvd_zero _)) p hp.ne_one
    have hv : v < e := lt_of_not_ge fun hv ↦ hn ((Nat.pow_dvd_pow p hv).trans (dvd_mul_right _ _))
    have := (choose_pow_mul_pow_mul_modEq_choose_nat (p := p) (k := v) (a := m) (b := 1)).dvd_iff
      dvd_rfl
    rw [mul_one, choose_one_right] at this
    exact hm (this.1 (h _ (pow_pos hp.pos v) (Nat.pow_lt_pow_right hp.one_lt hv)))

end Choose

namespace Polynomial

variable {R : Type*} (p : ℕ) [hp : Fact p.Prime]

section Ring

variable [Ring R] [CharP R p]

/-- In characteristic `p`, the Hasse derivatives of `f` of orders `0 < k < p ^ e` vanish if and
only if `p ^ e` divides every exponent of `f`. -/
theorem forall_hasseDeriv_eq_zero_iff {e : ℕ} {f : R[X]} :
    (∀ k, 0 < k → k < p ^ e → hasseDeriv k f = 0) ↔ ∀ n, f.coeff n ≠ 0 → p ^ e ∣ n := by
  have key (c : ℕ) (a : R) : (c : R) * a = 0 ↔ p ∣ c ∨ a = 0 := by
    by_cases hc : p ∣ c
    · simp [hc, (CharP.cast_eq_zero_iff R p c).2 hc]
    · simp [hc, ((CharP.isUnit_natCast_iff (R := R) hp.out).2 hc).mul_right_eq_zero]
  simp_rw [hasseDeriv_eq_zero_iff, key, Choose.pow_dvd_iff_forall_dvd_choose (p := p)]
  exact ⟨fun h n hn k hk hk' ↦ (h k hk hk' n).resolve_right hn,
    fun h k hk hk' n ↦ or_iff_not_imp_right.2 fun hn ↦ h n hn k hk hk'⟩

theorem hasseDeriv_X_pow_mul {e k : ℕ} (hk : k < p ^ e) (g : R[X]) :
    hasseDeriv k (X ^ p ^ e * g) = X ^ p ^ e * hasseDeriv k g := by
  refine hasseDeriv_mul_of_forall_hasseDeriv_eq_zero _ _ (fun i hi hik ↦ ?_) g
  refine (forall_hasseDeriv_eq_zero_iff p (e := e)).2 (fun n hn ↦ ?_) i hi (by lia)
  rw [coeff_X_pow, ne_eq, ite_eq_right_iff, not_forall] at hn
  rw [hn.1]

end Ring

section CommRing

variable [CommRing R] [CharP R p]

/-- In characteristic `p`, the Hasse derivatives of `f` of orders `0 < k < p ^ e` vanish if and
only if `f` is a polynomial in `X ^ (p ^ e)`. -/
theorem forall_hasseDeriv_eq_zero_iff_exists_expand {e : ℕ} {f : R[X]} :
    (∀ k, 0 < k → k < p ^ e → hasseDeriv k f = 0) ↔ ∃ g, expand R (p ^ e) g = f := by
  have hpe : 0 < p ^ e := pow_pos hp.out.pos e
  rw [forall_hasseDeriv_eq_zero_iff]
  refine ⟨fun h ↦ ⟨contract (p ^ e) f, AddMonoidAlgebra.ext (Finsupp.ext fun n ↦ ?_)⟩, ?_⟩
  · rw [coeff_expand hpe, coeff_contract hpe.ne']
    split_ifs with hn
    · rw [Nat.div_mul_cancel hn]
    · exact (not_imp_comm.1 (h n) hn).symm
  · rintro ⟨g, rfl⟩ n hn
    rw [coeff_expand hpe] at hn
    exact of_not_not fun h' ↦ hn (by simp [h'])

/-- In characteristic `p`, `hasseDeriv k` is linear over polynomials in `X ^ (p ^ e)` for
`k < p ^ e`. -/
theorem hasseDeriv_expand_mul {e k : ℕ} (hk : k < p ^ e) (f g : R[X]) :
    hasseDeriv k (expand R (p ^ e) f * g) = expand R (p ^ e) f * hasseDeriv k g :=
  hasseDeriv_mul_of_forall_hasseDeriv_eq_zero _ _ (fun i hi hik ↦
    (forall_hasseDeriv_eq_zero_iff_exists_expand p).2 ⟨f, rfl⟩ i hi (by lia)) g

end CommRing

end Polynomial
