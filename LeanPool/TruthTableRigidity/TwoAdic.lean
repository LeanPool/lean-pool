/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted from bjoernkjoshanssen/tt-auto, RequestProject/TT.
This development was edited with Aristotle (Harmonic). Its oracle program
infrastructure is reused from the Apache-2.0 OpenAI degree-rigidity port.
-/

module

public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.TruthTableRigidity.Closure

/-!
# The 2-adic group structure on Cantor space

We identify `X : ℕ → Bool` with the 2-adic integer `∑ X(n) 2^n`.  The group operations are
defined through the truncations `trunc X k = ∑_{i<k} X(i) 2^i`, which determine `X`, and
which are additive modulo `2^k`.  The type synonym `Z2` carries the `AddCommGroup`
structure (we do not put it on `ℕ → Bool` itself, which already carries the pointwise
Boolean ring structure).
-/

@[expose] public section

namespace TT

open OAI.TuringRigidity

/-- Cantor space viewed as the 2-adic integers. -/
@[implicit_reducible] def Z2 : Type := Oracle

/-- `trunc X k = ∑_{i<k} X(i) 2^i`. -/
def trunc (X : Oracle) (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, bv (X i) * 2 ^ i

theorem bv_le_one (b : Bool) : bv b ≤ 1 := by cases b <;> simp [bv]

@[simp] theorem trunc_zero (X : Oracle) : trunc X 0 = 0 := by simp [trunc]

theorem trunc_succ (X : Oracle) (k : ℕ) : trunc X (k + 1) = trunc X k + bv (X k) * 2 ^ k := by
  simp [trunc, Finset.sum_range_succ]

theorem trunc_lt (X : Oracle) (k : ℕ) : trunc X k < 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [trunc_succ, pow_succ]
    have : bv (X k) * 2 ^ k ≤ 2 ^ k := by
      simpa only [one_mul] using Nat.mul_le_mul_right (2 ^ k) (bv_le_one (X k))
    omega

theorem trunc_succ_div (X : Oracle) (k : ℕ) : trunc X (k + 1) / 2 ^ k = bv (X k) := by
  rw [trunc_succ, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (trunc_lt X k), zero_add]

theorem trunc_succ_mod (X : Oracle) (k : ℕ) : trunc X (k + 1) % 2 ^ k = trunc X k := by
  rw [trunc_succ, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (trunc_lt X k)]

theorem trunc_mod (X : Oracle) {m k : ℕ} (h : m ≤ k) : trunc X k % 2 ^ m = trunc X m := by
  induction k with
  | zero => obtain rfl : m = 0 := by omega
            simp
  | succ k ih =>
    rcases Nat.lt_or_ge m (k + 1) with hm | hm
    · rw [← ih (by omega), ← trunc_succ_mod X k, Nat.mod_mod_of_dvd]
      exact pow_dvd_pow 2 (by omega)
    · obtain rfl : m = k + 1 := by omega
      exact Nat.mod_eq_of_lt (trunc_lt X _)

theorem bv_injective : Function.Injective bv := by
  intro a b h; cases a <;> cases b <;> simp_all [bv]

theorem eq_of_trunc_eq {X Y : Oracle} {k : ℕ} (h : trunc X k = trunc Y k) {i : ℕ} (hi : i < k) :
    X i = Y i := by
  apply bv_injective
  rw [← trunc_succ_div, ← trunc_succ_div, ← trunc_mod X (show i + 1 ≤ k by omega),
    ← trunc_mod Y (show i + 1 ≤ k by omega), h]

theorem trunc_eq_of_eq {X Y : Oracle} {k : ℕ} (h : ∀ i < k, X i = Y i) : trunc X k = trunc Y k := by
  simp only [trunc]
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]

theorem ext_trunc {X Y : Oracle} (h : ∀ k, trunc X k = trunc Y k) : X = Y := by
  funext i
  exact eq_of_trunc_eq (h (i + 1)) (Nat.lt_succ_self i)

/-- The oracle with prescribed truncations. -/
def ofSeq (s : ℕ → ℕ) : Oracle := fun k => decide (s (k + 1) / 2 ^ k = 1)

theorem trunc_ofSeq {s : ℕ → ℕ} (hlt : ∀ k, s k < 2 ^ k) (hcoh : ∀ k, s (k + 1) % 2 ^ k = s k)
    (k : ℕ) : trunc (ofSeq s) k = s k := by
  induction k with
  | zero => have := hlt 0; simp at this; simp [this]
  | succ k ih =>
    rw [trunc_succ, ih]
    have hq : s (k + 1) / 2 ^ k ≤ 1 := by
      exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by simpa only [pow_succ] using hlt (k + 1)))
    have hdecomp := Nat.mod_add_div' (s (k + 1)) (2 ^ k)
    rw [hcoh k] at hdecomp
    have hb : bv (ofSeq s k) = s (k + 1) / 2 ^ k := by
      simp only [ofSeq, bv]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with h | h <;> simp [h]
    rw [hb]
    exact hdecomp

/-- 2-adic addition. -/
def zadd (X Y : Oracle) : Oracle := ofSeq fun k => (trunc X k + trunc Y k) % 2 ^ k

/-- 2-adic negation. -/
def zneg (X : Oracle) : Oracle := ofSeq fun k => (2 ^ k - trunc X k) % 2 ^ k

theorem trunc_zadd (X Y : Oracle) (k : ℕ) :
    trunc (zadd X Y) k = (trunc X k + trunc Y k) % 2 ^ k := by
  apply trunc_ofSeq (fun k => Nat.mod_lt _ (by positivity))
  intro k
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (Nat.le_succ k)), Nat.add_mod, trunc_succ_mod,
    trunc_succ_mod]

theorem trunc_zneg (X : Oracle) (k : ℕ) :
    trunc (zneg X) k = (2 ^ k - trunc X k) % 2 ^ k := by
  apply trunc_ofSeq (fun k => Nat.mod_lt _ (by positivity))
  intro k
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (Nat.le_succ k)), trunc_succ, pow_succ]
  have hlt := trunc_lt X k
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (bv_le_one (X k)) with h | h <;> rw [h]
  · rw [show 2 ^ k * 2 - (trunc X k + 0 * 2 ^ k) = (2 ^ k - trunc X k) + 2 ^ k by omega,
      Nat.add_mod_right]
  · rw [show 2 ^ k * 2 - (trunc X k + 1 * 2 ^ k) = 2 ^ k - trunc X k by omega]

/-- The zero element `0^ω`. -/
def zzero : Oracle := fun _ => false

@[simp] theorem trunc_zzero (k : ℕ) : trunc zzero k = 0 := by simp [trunc, zzero, bv]

instance : Add Z2 := ⟨zadd⟩
instance : Zero Z2 := ⟨zzero⟩
instance : Neg Z2 := ⟨zneg⟩

instance : AddCommGroup Z2 where
  add_assoc X Y Z := by
    apply ext_trunc; intro k
    change trunc (zadd (zadd X Y) Z) k = trunc (zadd X (zadd Y Z)) k
    simp only [trunc_zadd, Nat.mod_add_mod, Nat.add_mod_mod, add_assoc]
  zero_add X := by
    apply ext_trunc; intro k
    change trunc (zadd zzero X) k = trunc X k
    simp [trunc_zadd, Nat.mod_eq_of_lt (trunc_lt X k)]
  add_zero X := by
    apply ext_trunc; intro k
    change trunc (zadd X zzero) k = trunc X k
    simp [trunc_zadd, Nat.mod_eq_of_lt (trunc_lt X k)]
  add_comm X Y := by
    apply ext_trunc; intro k
    change trunc (zadd X Y) k = trunc (zadd Y X) k
    simp only [trunc_zadd, add_comm]
  neg_add_cancel X := by
    apply ext_trunc; intro k
    change trunc (zadd (zneg X) X) k = trunc zzero k
    have := trunc_lt X k
    simp only [trunc_zadd, trunc_zneg, Nat.mod_add_mod, trunc_zzero]
    rw [Nat.sub_add_cancel this.le, Nat.mod_self]
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- View an oracle as a 2-adic integer. -/
def Z2.of (X : Oracle) : Z2 := X

@[simp] theorem Z2.of_apply (X : Oracle) (n : ℕ) : Z2.of X n = X n := rfl

theorem Z2.add_def (X Y : Z2) : X + Y = zadd X Y := rfl
theorem Z2.neg_def (X : Z2) : -X = zneg X := rfl
theorem Z2.zero_def : (0 : Z2) = zzero := rfl

theorem Z2.trunc_add (X Y : Z2) (k : ℕ) : trunc (X + Y) k = (trunc X k + trunc Y k) % 2 ^ k :=
  trunc_zadd X Y k

theorem Z2.trunc_neg (X : Z2) (k : ℕ) : trunc (-X) k = (2 ^ k - trunc X k) % 2 ^ k :=
  trunc_zneg X k

/-! ### Low bits: the subgroups `N_{0^k}` -/

/-- `T ∈ N_{0^k}`: the first `k` bits of `T` vanish. -/
def LowZero (k : ℕ) (T : Oracle) : Prop := ∀ i < k, T i = false

theorem lowZero_iff_trunc {k : ℕ} {T : Oracle} : LowZero k T ↔ trunc T k = 0 := by
  constructor
  · intro h
    rw [show (0 : ℕ) = trunc zzero k by simp]
    exact trunc_eq_of_eq h
  · intro h i hi
    rw [show (0 : ℕ) = trunc zzero k by simp] at h
    exact eq_of_trunc_eq h hi

theorem Z2.add_low {k : ℕ} {T : Z2} (hT : LowZero k T) (X : Z2) {i : ℕ} (hi : i < k) :
    (X + T : Z2) i = X i := by
  apply eq_of_trunc_eq (k := k) _ hi
  rw [Z2.trunc_add, lowZero_iff_trunc.mp hT, add_zero, Nat.mod_eq_of_lt (trunc_lt X k)]

theorem Z2.lowZero_add {k : ℕ} {S T : Z2} (hS : LowZero k S) (hT : LowZero k T) :
    LowZero k (S + T : Z2) := by
  rw [lowZero_iff_trunc] at *
  rw [Z2.trunc_add, hS, hT]; simp

theorem Z2.lowZero_neg {k : ℕ} {T : Z2} (hT : LowZero k T) : LowZero k (-T : Z2) := by
  rw [lowZero_iff_trunc] at *
  rw [Z2.trunc_neg, hT]; simp

theorem Z2.lowZero_sub {k : ℕ} {S T : Z2} (hS : LowZero k S) (hT : LowZero k T) :
    LowZero k (S - T : Z2) := by
  rw [sub_eq_add_neg]; exact Z2.lowZero_add hS (Z2.lowZero_neg hT)

theorem LowZero.mono {k l : ℕ} {T : Oracle} (h : LowZero l T) (hkl : k ≤ l) : LowZero k T :=
  fun i hi => h i (by omega)

/-! ### Sums without carries -/

theorem bv_or (a b : Bool) (h : a = false ∨ b = false) : bv (a || b) = bv a + bv b := by
  cases a <;> cases b <;> simp_all [bv]

theorem trunc_or {X Y : Oracle} (h : ∀ i, X i = false ∨ Y i = false) (k : ℕ) :
    trunc (fun i => X i || Y i) k = trunc X k + trunc Y k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [trunc_succ, ih, bv_or _ _ (h k)]
    ring

/-- Adding two 2-adic integers with disjoint supports produces no carries. -/
theorem Z2.add_of_disjoint {X Y : Z2} (h : ∀ i, X i = false ∨ Y i = false) :
    (X + Y : Z2) = (fun i => X i || Y i : Oracle) := by
  apply ext_trunc; intro k
  rw [Z2.trunc_add, ← trunc_or h, Nat.mod_eq_of_lt (trunc_lt _ k)]

/-! ### Doubling and halving -/

/-- The shift `S(X)(n) = X(n+1)`; on `N_{0^1}` this is halving. -/
def shift (X : Oracle) : Oracle := fun n => X (n + 1)

/-- `b⌢X`. -/
def cons (b : Bool) (X : Oracle) : Oracle := fun n => if n = 0 then b else X (n - 1)

theorem trunc_cons_false (X : Oracle) (k : ℕ) : trunc (cons false X) (k + 1) = 2 * trunc X k := by
  induction k with
  | zero => simp [trunc_succ, cons, bv]
  | succ k ih =>
    rw [trunc_succ, ih, trunc_succ]
    simp [cons, pow_succ]
    ring

theorem Z2.add_self (X : Z2) : (X + X : Z2) = cons false X := by
  apply ext_trunc; intro k
  rw [Z2.trunc_add]
  rcases k with _ | k
  · simp
  · rw [trunc_cons_false, ← two_mul, pow_succ, mul_comm (2 ^ k) 2, ← trunc_succ_mod X k,
      Nat.mul_mod_mul_left]

theorem cons_shift {T : Oracle} (h : T 0 = false) : cons false (shift T) = T := by
  funext n
  rcases n with _ | n
  · simp [cons, h]
  · simp [cons, shift]

/-- `2 (T/2) = T` for `T ∈ N_{0^1}`. -/
theorem Z2.shift_add_shift {T : Z2} (h : T 0 = false) :
    Z2.of (shift T) + Z2.of (shift T) = T := by
  rw [Z2.add_self]
  exact cons_shift h

theorem lowZero_shift {k : ℕ} {T : Oracle} (h : LowZero (k + 1) T) : LowZero k (shift T) :=
  fun i hi => h (i + 1) (by omega)

theorem lowZero_cons {k : ℕ} {T : Oracle} (h : LowZero k T) : LowZero (k + 1) (cons false T) := by
  intro i hi
  rcases i with _ | i
  · rfl
  · simp only [cons, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    exact h i (by omega)

end TT
