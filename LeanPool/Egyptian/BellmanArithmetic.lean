/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Bellman

/-! The scaling identity (B1) and the cleared-product identity of §3.2. -/

@[expose] public section

namespace Egyptian.Control

/-- Scale the numerator and denominator of the remainder by the same factor. -/
def scale (c : ℕ) (s : State) : State := ⟨c * s.p, c * s.q, s.last⟩

theorem scale_step (c x : ℕ) (s : State) : step (scale c s) x = scale c (step s x) := by
  simp [step, scale, Nat.mul_sub, Nat.mul_assoc]

theorem scale_finish (c : ℕ) (s : State) (xs : List ℕ) :
    finish (scale c s) xs = scale c (finish s xs) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => rw [finish, scale_step, ih]; rfl

theorem scale_legal (σ : Convention) {c : ℕ} (hc : 0 < c) (s : State) (x : ℕ) :
    Legal σ (scale c s) x ↔ Legal σ s x := by
  simp [Legal, scale, Nat.mul_assoc, Nat.mul_lt_mul_left hc]

theorem scale_controls (σ : Convention) {c : ℕ} (hc : 0 < c) (s : State) (xs : List ℕ) :
    Controls σ (scale c s) xs ↔ Controls σ s xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp only [Controls, scale_legal σ hc, scale_step, ih]

theorem scale_canStop {c : ℕ} (hc : 0 < c) (s : State) (T : ℕ) :
    CanStop (scale c s) T ↔ CanStop s T := by
  simp [CanStop, scale, Nat.mul_assoc, hc.ne']

theorem scale_terminal (σ : Convention) {c : ℕ} (hc : 0 < c)
    (s : State) (xs : List ℕ) (T : ℕ) :
    Terminal σ (scale c s) xs T ↔ Terminal σ s xs T := by
  simp only [Terminal, scale_controls σ hc, scale_finish, scale_canStop hc]

theorem scale_value (σ : Convention) (H : ℕ → ℝ) {c : ℕ} (hc : 0 < c) (s : State) :
    value σ H (scale c s) = value σ H s := by
  simp only [value, scale_terminal σ hc]

theorem finish_denominator (s : State) (xs : List ℕ) :
    (finish s xs).q = s.q * xs.prod := by
  induction xs generalizing s with
  | nil => simp [finish]
  | cons x xs ih => simp [finish, ih, step, Nat.mul_assoc]

/-- Clearing all denominators along a legal finite trajectory yields a positive
integer, the first coordinate of its final state. -/
theorem cleared_product {σ s xs} (hv : Valid s) (hc : Controls σ s xs) :
    (s.p : ℚ) / s.q - recipSum xs =
      ((finish s xs).p : ℚ) / (s.q * (xs.prod : ℕ) : ℚ) := by
  rw [← finish_fraction hv hc, finish_denominator, Nat.cast_mul]

theorem first_fall_interior {s : State} {x P : ℕ} (hx : 0 < x)
    (hsmall : s.p ≤ s.q) (hprev : P ≤ s.p) (hfall : (step s x).p < P) :
    Interior (step s x) :=
  (step_interior_iff hx).mpr (hfall.trans_le (hprev.trans hsmall))

end Egyptian.Control
