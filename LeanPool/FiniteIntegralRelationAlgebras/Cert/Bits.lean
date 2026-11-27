/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Ring

/-!
# A bit toolkit for kernel-evaluated truth tables

Truth tables of Boolean functions of `b` variables are stored as natural numbers below
`2 ^ 2 ^ b`: bit `p < 2 ^ b` is the value of the function at the assignment `i ↦ p.testBit i`.
This file provides

* `RACert.ones b`: the all-ones table,
* `RACert.pat b i`: the table of the `i`-th variable (and its complement `RACert.maskLo b i`),
* `RACert.popcount b x`: a SWAR population count using `O(b)` big-number operations,

together with their specifications (`testBit_ones`, `testBit_maskLo`, `testBit_pat`,
`popcount_eq`, `popcount_eq_card_filter_fun`).

All computational definitions are written with the raw functions `Nat.land`, `Nat.shiftRight`,
`Nat.add`, ... (rather than notation) so that kernel reduction reaches the GMP-accelerated
primitives in as few steps as possible.
-/

@[expose] public section

namespace RACert

/-! ### All-ones constants and variable patterns -/

/-- All-ones on `2^b` bits. -/
def ones (b : Nat) : Nat := Nat.sub (Nat.pow 2 (Nat.pow 2 b)) 1

/-- Bit `p < 2^b` is set iff bit `i` of `p` is clear: `ones b / (2^(2^i) + 1)`. -/
def maskLo (b i : Nat) : Nat := Nat.div (ones b) (Nat.add (Nat.pow 2 (Nat.pow 2 i)) 1)

/-- Truth-table column of variable `i` among `b` variables: bit `p < 2^b` is set iff
`p.testBit i`. -/
def pat (b i : Nat) : Nat := Nat.xor (ones b) (maskLo b i)

theorem ones_eq (b : Nat) : ones b = 2 ^ 2 ^ b - 1 := rfl

theorem maskLo_eq (b i : Nat) : maskLo b i = ones b / (2 ^ 2 ^ i + 1) := rfl

theorem pat_eq (b i : Nat) : pat b i = ones b ^^^ maskLo b i := rfl

theorem testBit_ones (b p : Nat) : (ones b).testBit p = decide (p < 2 ^ b) := by
  rw [ones_eq, Nat.testBit_two_pow_sub_one]

theorem ones_lt (b : Nat) : ones b < 2 ^ 2 ^ b := by
  have := Nat.two_pow_pos (2 ^ b)
  rw [ones_eq]
  omega

theorem ones_succ (b : Nat) : ones (b + 1) = ones b * (2 ^ 2 ^ b + 1) := by
  have h : 2 ^ 2 ^ (b + 1) = 2 ^ 2 ^ b * 2 ^ 2 ^ b := by
    rw [← pow_add, pow_succ, Nat.mul_two]
  have hpos := Nat.two_pow_pos (2 ^ b)
  rw [ones_eq, ones_eq, h]
  generalize 2 ^ 2 ^ b = N at hpos
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  apply Nat.sub_eq_of_eq_add
  simp only [Nat.add_sub_cancel]
  ring

theorem dvd_ones {b i : Nat} (hi : i < b) : (2 ^ 2 ^ i + 1) ∣ ones b := by
  induction b with
  | zero => omega
  | succ b ih =>
    rw [ones_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
    · exact Dvd.dvd.mul_right (ih h) _
    · exact Nat.dvd_mul_left _ _

theorem maskLo_self (i : Nat) : maskLo (i + 1) i = ones i := by
  rw [maskLo_eq, ones_succ, Nat.mul_div_cancel _ (Nat.succ_pos _)]

theorem maskLo_succ {b i : Nat} (hi : i < b) :
    maskLo (b + 1) i = maskLo b i * (2 ^ 2 ^ b + 1) := by
  rw [maskLo_eq, maskLo_eq, ones_succ, Nat.mul_comm, Nat.mul_div_assoc _ (dvd_ones hi),
    Nat.mul_comm]

theorem maskLo_le (b i : Nat) : maskLo b i ≤ ones b := Nat.div_le_self _ _

theorem maskLo_lt (b i : Nat) : maskLo b i < 2 ^ 2 ^ b :=
  Nat.lt_of_le_of_lt (maskLo_le b i) (ones_lt b)

theorem pat_lt (b i : Nat) : pat b i < 2 ^ 2 ^ b :=
  Nat.xor_lt_two_pow (ones_lt b) (maskLo_lt b i)

theorem pat_le (b i : Nat) : pat b i ≤ ones b := by
  have := pat_lt b i
  rw [ones_eq]
  omega

theorem testBit_sub_two_pow {b i p : Nat} (hi : i < b) (hp : 2 ^ b ≤ p) :
    (p - 2 ^ b).testBit i = p.testBit i := by
  have h : p = 2 ^ b + (p - 2 ^ b) := by omega
  conv_rhs => rw [h, Nat.testBit_two_pow_add_gt hi]

theorem testBit_maskLo {b i : Nat} (hi : i < b) (p : Nat) :
    (maskLo b i).testBit p = (decide (p < 2 ^ b) && !p.testBit i) := by
  induction b, hi using Nat.le_induction generalizing p with
  | base =>
    have hpow : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; omega
    rw [maskLo_self, testBit_ones]
    by_cases h1 : p < 2 ^ i
    · have h2 : p < 2 ^ (i + 1) := by omega
      simp [h1, h2, Nat.testBit_lt_two_pow h1]
    · by_cases h2 : p < 2 ^ (i + 1)
      · have h3 : p = 2 ^ i + (p - 2 ^ i) := by omega
        have h4 : p - 2 ^ i < 2 ^ i := by omega
        have h5 : p.testBit i = true := by
          rw [h3, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow h4]; rfl
        simp [h1, h2, h5]
      · simp [h1, h2]
  | succ b hb ih =>
    have hpow : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [pow_succ]; omega
    rw [maskLo_succ hb, Nat.mul_add, Nat.mul_one, Nat.mul_comm,
      Nat.testBit_two_pow_mul_add _ (maskLo_lt b i)]
    split
    · next h =>
      have h' : p < 2 ^ (b + 1) := by omega
      rw [ih]; simp [h, h']
    · next h =>
      rw [ih, testBit_sub_two_pow hb (by omega)]
      congr 1
      simp only [decide_eq_decide]
      omega

theorem testBit_pat {b i : Nat} (hi : i < b) (p : Nat) :
    (pat b i).testBit p = (decide (p < 2 ^ b) && p.testBit i) := by
  rw [pat_eq, Nat.testBit_xor, testBit_ones, testBit_maskLo hi]
  cases decide (p < 2 ^ b) <;> cases p.testBit i <;> rfl

/-! ### Bitwise operations in raw form

Restatements of core lemmas for the raw functions `Nat.land`, `Nat.lor`, `Nat.xor` used in
kernel-evaluated definitions (these are definitionally `&&&`, `|||`, `^^^`). -/

theorem land_eq (x y : Nat) : Nat.land x y = x &&& y := rfl

theorem lor_eq (x y : Nat) : Nat.lor x y = x ||| y := rfl

theorem xor_eq (x y : Nat) : Nat.xor x y = x ^^^ y := rfl

theorem shiftRight_eq (x n : Nat) : Nat.shiftRight x n = x >>> n := rfl

theorem testBit_land (x y p : Nat) : (Nat.land x y).testBit p = (x.testBit p && y.testBit p) :=
  Nat.testBit_and x y p

theorem testBit_lor (x y p : Nat) : (Nat.lor x y).testBit p = (x.testBit p || y.testBit p) :=
  Nat.testBit_or x y p

theorem testBit_xor (x y p : Nat) : (Nat.xor x y).testBit p = (x.testBit p ^^ y.testBit p) :=
  Nat.testBit_xor x y p

theorem land_lt {x y N : Nat} (hy : y < 2 ^ N) : Nat.land x y < 2 ^ N :=
  Nat.and_lt_two_pow x hy

theorem land_lt_left {x y N : Nat} (hx : x < 2 ^ N) : Nat.land x y < 2 ^ N :=
  Nat.lt_of_le_of_lt Nat.and_le_left hx

theorem lor_lt {x y N : Nat} (hx : x < 2 ^ N) (hy : y < 2 ^ N) : Nat.lor x y < 2 ^ N :=
  Nat.or_lt_two_pow hx hy

theorem xor_lt {x y N : Nat} (hx : x < 2 ^ N) (hy : y < 2 ^ N) : Nat.xor x y < 2 ^ N :=
  Nat.xor_lt_two_pow hx hy

/-! ### Digit strings in base `2 ^ w` -/

/-- The number with base-`2^w` digits `f 0, …, f (n - 1)` (little-endian). -/
def digitVal (w n : Nat) (f : Nat → Nat) : Nat := ∑ k ∈ Finset.range n, f k * 2 ^ (w * k)

theorem digitVal_succ (w n : Nat) (f : Nat → Nat) :
    digitVal w (n + 1) f = 2 ^ (w * n) * f n + digitVal w n f := by
  rw [digitVal, Finset.sum_range_succ, ← digitVal, Nat.add_comm, Nat.mul_comm]

theorem digitVal_lt {w : Nat} {f : Nat → Nat} (hf : ∀ k, f k < 2 ^ w) (n : Nat) :
    digitVal w n f < 2 ^ (w * n) := by
  induction n with
  | zero => simp [digitVal]
  | succ n ih =>
    have h1 : 2 ^ (w * n) * (f n + 1) ≤ 2 ^ (w * n) * 2 ^ w := Nat.mul_le_mul_left _ (hf n)
    rw [digitVal_succ, Nat.mul_succ, pow_add]
    rw [Nat.mul_add, Nat.mul_one] at h1
    omega

theorem testBit_digitVal {w : Nat} (hw : 0 < w) {f : Nat → Nat} (hf : ∀ k, f k < 2 ^ w)
    (n p : Nat) :
    (digitVal w n f).testBit p = (decide (p / w < n) && (f (p / w)).testBit (p % w)) := by
  induction n with
  | zero => simp [digitVal]
  | succ n ih =>
    rw [digitVal_succ, Nat.testBit_two_pow_mul_add _ (digitVal_lt hf n)]
    split
    · next h =>
      have h1 : p / w < n := Nat.div_lt_of_lt_mul h
      have h2 : p / w < n + 1 := by omega
      rw [ih]; simp [h1, h2]
    · next h =>
      have h1 : n ≤ p / w := by
        rw [Nat.le_div_iff_mul_le hw, Nat.mul_comm]; omega
      rcases Nat.eq_or_lt_of_le h1 with h2 | h2
      · have h3 : p - w * n = p % w := by
          have := Nat.div_add_mod p w
          rw [← h2] at this
          omega
        rw [h3, ← h2]; simp
      · have h3 : (n + 1) * w ≤ p := (Nat.le_div_iff_mul_le hw).mp h2
        have h4 : w ≤ p - w * n := by
          rw [Nat.add_mul, Nat.mul_comm] at h3; omega
        have h5 : ¬ p / w < n + 1 := by omega
        rw [Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le (hf n) (Nat.pow_le_pow_right (by omega) h4))]
        simp [h5]

/-- Masking a digit string with `maskLo` (after shifting by `e ≤ 1` digits) keeps every other
digit, widening the digits from `2^j` to `2^(j+1)` bits. -/
theorem digitVal_shiftRight_and_maskLo {b j m e : Nat} (hb : 2 ^ (j + 1) * m = 2 ^ b)
    (hj : j < b) (he : e ≤ 1) {f : Nat → Nat} (hf : ∀ k, f k < 2 ^ 2 ^ j) :
    (digitVal (2 ^ j) (2 * m) f >>> (2 ^ j * e)) &&& maskLo b j =
      digitVal (2 ^ (j + 1)) m (fun k => f (2 * k + e)) := by
  have hw : 0 < 2 ^ j := Nat.two_pow_pos j
  have hw2 : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
  have hf' : ∀ k, f (2 * k + e) < 2 ^ 2 ^ (j + 1) := fun k =>
    Nat.lt_of_lt_of_le (hf _) (Nat.pow_le_pow_right (by omega) (by omega))
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_maskLo hj,
    testBit_digitVal hw hf, testBit_digitVal (Nat.two_pow_pos _) hf',
    Nat.mul_add_div hw, Nat.mul_add_mod, Nat.testBit_eq_decide_div_mod_eq (x := p) (i := j),
    ← hb, hw2, ← Nat.div_div_eq_div_mul, Nat.mod_mul]
  have h1 : decide (p < 2 ^ j * 2 * m) = decide (p / 2 ^ j / 2 < m) := by
    simp only [decide_eq_decide]
    rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (by omega), Nat.mul_comm m]
  rw [h1]
  generalize p / 2 ^ j = q
  generalize p % 2 ^ j = r
  rcases Nat.mod_two_eq_zero_or_one q with h | h
  · have h2 : 2 * (q / 2) + e = e + q := by omega
    have h3 : decide (e + q < 2 * m) = decide (q / 2 < m) := by
      simp only [decide_eq_decide]; omega
    rw [h2, h3, h, Nat.mul_zero, Nat.add_zero]
    cases decide (q / 2 < m) <;> cases (f (e + q)).testBit r <;> rfl
  · have h2 : (f (2 * (q / 2) + e)).testBit (r + 2 ^ j * 1) = false :=
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le (hf _) (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [h, h2]
    simp

theorem sum_range_two_mul (f : Nat → Nat) (m : Nat) :
    ∑ k ∈ Finset.range (2 * m), f k = ∑ k ∈ Finset.range m, (f (2 * k) + f (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Nat.add_assoc]

theorem mod_two_pow_eq_digitVal (x n : Nat) :
    x % 2 ^ n = digitVal 1 n (fun k => (x.testBit k).toNat) := by
  induction n with
  | zero => simp [digitVal, Nat.mod_one]
  | succ n ih =>
    rw [digitVal_succ, ← ih, pow_succ, Nat.mod_mul, Nat.toNat_testBit, Nat.one_mul, Nat.add_comm]

/-! ### SWAR population count -/

/-- One SWAR round: add neighbouring `2^j`-bit fields into `2^(j+1)`-bit fields. -/
def swarStep (b j y : Nat) : Nat :=
  Nat.add (Nat.land y (maskLo b j)) (Nat.land (Nat.shiftRight y (Nat.pow 2 j)) (maskLo b j))

/-- `fuel` SWAR rounds starting at field width `2^j`. -/
def popAux (b : Nat) : (fuel j : Nat) → Nat → Nat
  | 0, _, y => y
  | fuel + 1, j, y => popAux b fuel (Nat.succ j) (swarStep b j y)

/-- SWAR population count of `x < 2^(2^b)`. -/
def popcount (b x : Nat) : Nat := popAux b b 0 x

theorem swarStep_eq (b j y : Nat) :
    swarStep b j y = (y &&& maskLo b j) + ((y >>> 2 ^ j) &&& maskLo b j) := rfl

theorem swarStep_digitVal {b j m : Nat} (hb : 2 ^ (j + 1) * m = 2 ^ b) (hj : j < b)
    {f : Nat → Nat} (hf : ∀ k, f k < 2 ^ 2 ^ j) :
    swarStep b j (digitVal (2 ^ j) (2 * m) f) =
      digitVal (2 ^ (j + 1)) m (fun k => f (2 * k) + f (2 * k + 1)) := by
  have h0 := digitVal_shiftRight_and_maskLo hb hj (e := 0) (by omega) hf
  have h1 := digitVal_shiftRight_and_maskLo hb hj (e := 1) (by omega) hf
  simp only [Nat.mul_zero, Nat.shiftRight_zero, Nat.mul_one, Nat.add_zero] at h0 h1
  rw [swarStep_eq, h0, h1]
  simp only [digitVal, ← Finset.sum_add_distrib, Nat.add_mul]

theorem popAux_digitVal {b : Nat} : ∀ (fuel j : Nat) (f : Nat → Nat), j + fuel = b →
    (∀ k, f k < 2 ^ 2 ^ j) →
    popAux b fuel j (digitVal (2 ^ j) (2 ^ fuel) f) = ∑ k ∈ Finset.range (2 ^ fuel), f k
  | 0, j, f, _, _ => by simp [popAux, digitVal]
  | fuel + 1, j, f, h, hf => by
    have hb : 2 ^ (j + 1) * 2 ^ fuel = 2 ^ b := by rw [← pow_add]; congr 1; omega
    have hg : ∀ k, f (2 * k) + f (2 * k + 1) < 2 ^ 2 ^ (j + 1) := fun k => by
      have h1 := hf (2 * k)
      have h2 := hf (2 * k + 1)
      have h3 : 2 ^ 2 ^ (j + 1) = 2 ^ 2 ^ j * 2 ^ 2 ^ j := by
        rw [← pow_add, pow_succ, Nat.mul_two]
      have h4 : 2 ^ 1 ≤ 2 ^ 2 ^ j := Nat.pow_le_pow_right (by omega) (Nat.two_pow_pos j)
      have h5 : 2 ^ 1 * 2 ^ 2 ^ j ≤ 2 ^ 2 ^ j * 2 ^ 2 ^ j := Nat.mul_le_mul_right _ h4
      rw [h3]
      omega
    rw [popAux, pow_succ' 2 fuel, swarStep_digitVal hb (by omega) hf,
      popAux_digitVal fuel (j + 1) _ (by omega) hg, sum_range_two_mul]

theorem popcount_eq {b x : Nat} (hx : x < 2 ^ 2 ^ b) :
    popcount b x = ((Finset.range (2 ^ b)).filter (fun p => x.testBit p)).card := by
  have h := popAux_digitVal (b := b) b 0 (fun k => (x.testBit k).toNat) (by omega)
    (fun k => by cases x.testBit k <;> simp)
  rw [pow_zero, ← mod_two_pow_eq_digitVal, Nat.mod_eq_of_lt hx] at h
  rw [popcount, h, Finset.card_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  cases x.testBit k <;> rfl

/-- Counting set bits of a truth table is counting satisfying Boolean assignments. -/
theorem popcount_eq_card_filter_fun {b x : Nat} (hx : x < 2 ^ 2 ^ b) (P : (Fin b → Bool) → Bool)
    (h : ∀ p < 2 ^ b, x.testBit p = P (fun i => p.testBit i)) :
    popcount b x = (Finset.univ.filter (fun v : Fin b → Bool => P v = true)).card := by
  rw [popcount_eq hx]
  refine Finset.card_bij (fun p _ => fun i : Fin b => p.testBit i) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [← h p hp.1]; exact hp.2⟩
  · intro p hp q hq hpq
    rw [Finset.mem_filter, Finset.mem_range] at hp hq
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < b
    · exact congrFun hpq ⟨i, hi⟩
    · have hle : 2 ^ b ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hp.1 hle),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hq.1 hle)]
  · intro v hv
    rw [Finset.mem_filter] at hv
    have hlt := Nat.ofBits_lt_two_pow v
    have hv' : (fun i : Fin b => (Nat.ofBits v).testBit i) = v := by
      funext i
      exact Nat.testBit_ofBits_lt v i i.isLt
    refine ⟨Nat.ofBits v, ?_, hv'⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hlt, by rw [h _ hlt, hv']; exact hv.2⟩

end RACert
