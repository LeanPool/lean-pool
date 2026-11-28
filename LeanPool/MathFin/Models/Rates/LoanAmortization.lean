/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.CouponBonds

/-!
# Loan amortization schedules: bullet, equal-principal and level-payment

All three schedules share the same per-period interest accrual on the outstanding
balance `B_{n-1}`,

  `I_n = B_{n-1} · i`,

and the same balance recurrence given the period's principal payment `P_n`,

  `B_n = B_{n-1} - P_n`.

They differ only in how `P_n` is chosen:

* **Bullet** (interest-only): `P_n = 0` for `n < N`, `P_N = B_0` — the whole
  principal is repaid in a single final installment. Closed form:
  `B_n = B_0` for `n < N`, `B_N = 0`.
* **Equal-principal**: `P_n = B_0 / N` every period — a constant principal
  payment. Closed form: `B_n = B_0 · (1 - n / N)`.
* **Level payment** (mortgage-style): the same payment `A` every period, its
  principal part `P_n = A - I_n` being what is left after interest, so
  `B_n = B_{n-1}·(1 + i) - A`. Priced against `annuityValue`
  (`MathFin/Models/Rates/CouponBonds.lean`), the present value of `N` payments
  `A` discounted continuously at rate `r` over periods of length `Δt`: if the
  loan's principal is that annuity's value and the period rate is
  `i = e^{rΔt} - 1`, then after `n ≤ N` payments the outstanding balance is
  the value of the `N - n` payments still to come, and the loan is paid off
  at `N`.

The bullet and equal-principal closed forms are proved by induction on the
shared `balance` recurrence; the level-payment one, by induction on
`levelPaymentBalance` directly, through the one-period annuity identity
`annuityValue_succ_mul_exp_sub` (`CouponBonds.lean`).

## Main definitions

* `balance`: the outstanding balance after `n` periods, given an initial balance `B₀` and a
  principal-payment schedule `P : ℕ → ℝ`.
* `bulletPrincipal`: the bullet schedule, with the entire balance repaid in period `N`.
* `equalPrincipalPayment`: the equal-principal schedule, a constant payment `B₀ / N` every period.
* `levelPaymentBalance`: the level-payment balance, with interest at period rate `i` accruing on
  the outstanding balance before the payment `A` is made.

## Main results

* `balance_bullet_lt`, `balance_bullet_eq` — the bullet closed form.
* `balance_equalPrincipal` — the equal-principal closed form
  `B_n = B_0 · (1 - n / N)`.
* `levelPaymentBalance`, `balance_levelPayment` — the level-payment balance,
  and that it is `balance` with principal `A - I_n`.
* `levelPaymentBalance_eq_annuityValue`, `levelPaymentBalance_eq_zero` — the
  balance after `n` level payments is `annuityValue (N - n) A r Δt`, and zero
  at `N`.

## References

* [Fabozzi, *Bond Markets, Analysis and Strategies*][FabozziBMAS]

## Tags

loan amortization, mortgage, bullet loan, level payment, equal principal, outstanding balance,
annuity, MSC 91G30, JEL G21
-/

@[expose] public section

namespace MathFin

/-- The outstanding balance after `n` periods, given an initial balance `B₀`
and a principal-payment schedule `P : ℕ → ℝ` (period `k`'s payment is `P k`
for `k = 1, …, n`). Defined by the shared recurrence `B_n = B_{n-1} - P_n`. -/
def balance (B0 : ℝ) (P : ℕ → ℝ) : ℕ → ℝ
  | 0 => B0
  | n + 1 => balance B0 P n - P (n + 1)

/-- The bullet schedule: no principal is repaid before maturity `N`, and the
entire balance is repaid in period `N`. -/
def bulletPrincipal (B0 : ℝ) (N : ℕ) : ℕ → ℝ :=
  fun n ↦ if n = N then B0 else 0

/-- Under the bullet schedule, the balance is unchanged before maturity. -/
theorem balance_bullet_lt {B0 : ℝ} {N n : ℕ} (hn : n < N) :
    balance B0 (bulletPrincipal B0 N) n = B0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [balance, bulletPrincipal, ih (Nat.lt_of_succ_lt hn), hn.ne]

/-- Under the bullet schedule, the balance is exactly zero at maturity `N ≥ 1`
(at `N = 0` maturity is not a payment period, and the balance stays `B₀`). -/
theorem balance_bullet_eq {B0 : ℝ} {N : ℕ} (hN : 0 < N) :
    balance B0 (bulletPrincipal B0 N) N = 0 := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  simp [balance, bulletPrincipal, balance_bullet_lt (Nat.lt_succ_self M)]

/-- The equal-principal schedule: a constant payment `B₀ / N` every period. -/
noncomputable def equalPrincipalPayment (B0 : ℝ) (N : ℕ) : ℕ → ℝ := fun _ ↦ B0 / N

/-- Closed form for the equal-principal schedule: `B_n = B₀ · (1 - n / N)`,
proved by induction on the balance recurrence. (At `N = 0` both sides reduce
to `B₀` under the `x / 0 = 0` convention, so no `N ≠ 0` hypothesis is needed.) -/
theorem balance_equalPrincipal {B0 : ℝ} {N : ℕ} (n : ℕ) :
    balance B0 (equalPrincipalPayment B0 N) n = B0 * (1 - (n : ℝ) / N) := by
  induction n with
  | zero => simp [balance]
  | succ k ih =>
    simp only [balance, equalPrincipalPayment, ih]
    push_cast
    ring

/-- The level-payment balance: interest at period rate `i` accrues on the
outstanding balance, then the payment `A` is made, `B_{n+1} = B_n·(1 + i) - A`. -/
def levelPaymentBalance (B0 A i : ℝ) : ℕ → ℝ
  | 0 => B0
  | n + 1 => levelPaymentBalance B0 A i n * (1 + i) - A

/-- The level-payment schedule is the shared recurrence `balance` with the
principal part of period `n + 1`'s payment being `A` less the interest
`B_n · i` on the outstanding balance. -/
theorem balance_levelPayment (B0 A i : ℝ) (n : ℕ) :
    balance B0 (fun m ↦ A - levelPaymentBalance B0 A i (m - 1) * i) n =
      levelPaymentBalance B0 A i n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [balance, levelPaymentBalance, ih, Nat.add_sub_cancel]
    ring

/-- **Level-payment schedule against `annuityValue`.** A loan whose principal
`B₀` is the value `annuityValue N A r Δt` of `N` level payments `A`, at period
rate `i = e^{rΔt} - 1`, has outstanding balance after `n ≤ N` payments equal to
the value of the `N - n` payments still to come. -/
theorem levelPaymentBalance_eq_annuityValue {B0 A r Δt : ℝ} {N : ℕ}
    (hB0 : annuityValue N A r Δt = B0) {n : ℕ} (hn : n ≤ N) :
    levelPaymentBalance B0 A (Real.exp (r * Δt) - 1) n = annuityValue (N - n) A r Δt := by
  induction n with
  | zero => exact hB0.symm
  | succ k ih =>
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hn
    rw [levelPaymentBalance, ih (Nat.le_of_succ_le hn), add_sub_cancel,
      show N - k = m + 1 by omega, show N - (k + 1) = m by omega,
      annuityValue_succ_mul_exp_sub]

/-- **A level-payment loan is paid off at maturity**: with `B₀` the value of the
`N` payments, the balance after the `N`-th is zero. -/
theorem levelPaymentBalance_eq_zero {B0 A r Δt : ℝ} {N : ℕ}
    (hB0 : annuityValue N A r Δt = B0) :
    levelPaymentBalance B0 A (Real.exp (r * Δt) - 1) N = 0 := by
  rw [levelPaymentBalance_eq_annuityValue hB0 le_rfl, Nat.sub_self, annuityValue,
    Finset.sum_range_zero]

end MathFin
