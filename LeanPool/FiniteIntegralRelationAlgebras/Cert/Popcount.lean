/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Bits

/-!
# A faster verified population count

`RACert.popcount b x` uses `b` SWAR rounds of four big-number operations each. For kernel
evaluation on truth tables with `2 ^ b` bits (`b` around 20) this is a noticeable cost, so this
file provides `RACert.popcountF`, which agrees with `popcount` (`popcountF_eq`) but uses only
15 big operations and one reduction modulo a one-limb constant when `5 ≤ b ≤ 31`:

* round 0 (`swarStep0`, 3 operations): `x - ((x >>> 1) &&& m₀)`, giving 2-bit fields `≤ 2`;
* round 1 (`swarStep`, 4 operations), giving 4-bit fields `≤ 4`;
* round 2 (`swarStepC`, 3 operations): `(y + (y >>> 4)) &&& m₂`, giving 8-bit fields `≤ 8`
  (no carry can cross a field any more, so a single mask after the addition suffices);
* two unmasked additions `y + (y >>> 8)` and `y + (y >>> 16)` (`addShift`, 2 operations each),
  after which every byte holds the sum of four consecutive bytes (`≤ 32`);
* one mask with `0x000000FF…` (`mask32`), keeping one byte in every 32-bit field;
* `% (2 ^ 32 - 1)`, which adds up all the 32-bit fields because `2 ^ 32 ≡ 1`, and the sum is
  at most `2 ^ b < 2 ^ 32 - 1`.

Outside the range `5 ≤ b ≤ 31` the function `popcountF` falls back to `popcount`.
-/

@[expose] public section

namespace RACert

/-! ### More digit-string lemmas -/

theorem digitVal_add (w n : Nat) (f g : Nat → Nat) :
    digitVal w n f + digitVal w n g = digitVal w n (fun k => f k + g k) := by
  simp only [digitVal, ← Finset.sum_add_distrib, Nat.add_mul]

theorem digitVal_const_mul (w n a : Nat) (f : Nat → Nat) :
    digitVal w n (fun k => a * f k) = a * digitVal w n f := by
  induction n with
  | zero => simp [digitVal]
  | succ n ih => rw [digitVal_succ, digitVal_succ, ih]; ring

/-- Regrouping the digits in pairs. -/
theorem digitVal_two_mul (w m : Nat) (f : Nat → Nat) :
    digitVal w (2 * m) f = digitVal (2 * w) m (fun k => f (2 * k) + 2 ^ w * f (2 * k + 1)) := by
  rw [digitVal, sum_range_two_mul, digitVal]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show w * (2 * k + 1) = 2 * w * k + w by ring, show w * (2 * k) = 2 * w * k by ring, pow_add]
  ring

/-- The digit string with all digits `2 ^ w - 1` is all-ones. -/
theorem digitVal_ones (w n : Nat) : digitVal w n (fun _ => 2 ^ w - 1) = 2 ^ (w * n) - 1 := by
  induction n with
  | zero => simp [digitVal]
  | succ n ih =>
    have h1 := Nat.two_pow_pos w
    have h2 := Nat.two_pow_pos (w * n)
    have h3 : 2 ^ (w * n) ≤ 2 ^ (w * n) * 2 ^ w := Nat.le_mul_of_pos_right _ h1
    rw [digitVal_succ, ih, Nat.mul_succ, pow_add, Nat.mul_sub, Nat.mul_one]
    omega

/-- Shifting a digit string (whose digits vanish from position `n` on) by `e` digits. -/
theorem digitVal_shiftRight {w n : Nat} (hw : 0 < w) {f : Nat → Nat} (hf : ∀ k, f k < 2 ^ w)
    (h0 : ∀ k, n ≤ k → f k = 0) (e : Nat) :
    digitVal w n f >>> (w * e) = digitVal w n (fun k => f (k + e)) := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_shiftRight, testBit_digitVal hw hf, testBit_digitVal hw (fun k => hf _),
    Nat.mul_add_div hw, Nat.mul_add_mod, Nat.add_comm e]
  by_cases h : p / w + e < n
  · have h' : p / w < n := by omega
    simp [h, h']
  · rw [h0 _ (by omega)]
    simp

/-- Reducing a digit string modulo `2 ^ w - 1` adds up its digits. -/
theorem digitVal_mod_two_pow_sub_one (w n : Nat) (f : Nat → Nat) :
    digitVal w n f % (2 ^ w - 1) = (∑ k ∈ Finset.range n, f k) % (2 ^ w - 1) := by
  have hpow : ∀ k, 2 ^ (w * k) % (2 ^ w - 1) = 1 % (2 ^ w - 1) := fun k => by
    have h1 : 2 ^ w % (2 ^ w - 1) = 1 % (2 ^ w - 1) := by
      have h2 : (2 ^ w - 1 + 1) % (2 ^ w - 1) = 1 % (2 ^ w - 1) := Nat.add_mod_left _ _
      have h3 := Nat.two_pow_pos w
      rwa [show 2 ^ w - 1 + 1 = 2 ^ w by omega] at h2
    rw [pow_mul, Nat.pow_mod, h1, ← Nat.pow_mod, one_pow]
  induction n with
  | zero => simp [digitVal]
  | succ n ih =>
    rw [digitVal_succ, Finset.sum_range_succ, Nat.add_mod, Nat.mul_mod, hpow, ← Nat.mul_mod, ih,
      ← Nat.add_mod, Nat.one_mul, Nat.add_comm]

/-- Masking a string of bytes with `0x000000FF…` keeps every fourth byte. -/
theorem digitVal_and_mask32 {n : Nat} {f : Nat → Nat} (hf : ∀ k, f k < 2 ^ 8) :
    digitVal 8 (4 * n) f &&& digitVal 32 n (fun _ => 255) =
      digitVal 32 n (fun k => f (4 * k)) := by
  have hf' : ∀ k, f (4 * k) < 2 ^ 32 := fun k =>
    Nat.lt_of_lt_of_le (hf _) (Nat.pow_le_pow_right (by omega) (by omega))
  have h255 : ∀ q, (255 : Nat).testBit q = decide (q < 8) := fun q =>
    Nat.testBit_two_pow_sub_one 8 q
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_and, testBit_digitVal (by omega) hf,
    testBit_digitVal (by omega) (fun _ => by omega), testBit_digitVal (by omega) hf', h255]
  by_cases h : p % 32 < 8
  · have h1 : p / 8 = 4 * (p / 32) := by omega
    have h2 : p % 8 = p % 32 := by omega
    have h3 : decide (4 * (p / 32) < 4 * n) = decide (p / 32 < n) := by
      simp only [decide_eq_decide]; omega
    rw [h1, h2, h3, decide_eq_true h]
    cases decide (p / 32 < n) <;> cases (f (4 * (p / 32))).testBit (p % 32) <;> rfl
  · have h1 : (f (4 * (p / 32))).testBit (p % 32) = false :=
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le (hf _) (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [h, h1]

theorem sum_range_four_mul (f : Nat → Nat) (m : Nat) :
    ∑ k ∈ Finset.range (4 * m), f k =
      ∑ k ∈ Finset.range m, (f (4 * k) + f (4 * k + 1) + (f (4 * k + 2) + f (4 * k + 3))) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, ih]
    omega

/-! ### Sums of neighbouring digits -/

/-- The digit function after one SWAR round: sums of neighbouring digits. -/
def pairSum (f : Nat → Nat) : Nat → Nat := fun k => f (2 * k) + f (2 * k + 1)

theorem pairSum_le {f : Nat → Nat} {c : Nat} (hf : ∀ k, f k ≤ c) (k : Nat) :
    pairSum f k ≤ 2 * c := by
  have h1 := hf (2 * k)
  have h2 := hf (2 * k + 1)
  rw [pairSum]
  omega

theorem pairSum_eq_zero {f : Nat → Nat} {n : Nat} (h0 : ∀ k, 2 * n ≤ k → f k = 0) (k : Nat)
    (hk : n ≤ k) : pairSum f k = 0 := by
  rw [pairSum, h0 _ (by omega), h0 _ (by omega)]

theorem sum_pairSum (f : Nat → Nat) (m : Nat) :
    ∑ k ∈ Finset.range m, pairSum f k = ∑ k ∈ Finset.range (2 * m), f k :=
  (sum_range_two_mul f m).symm

/-! ### Cheaper SWAR rounds -/

/-- The first SWAR round in three operations: `x - ((x >>> 1) &&& 0x5555…)`. -/
def swarStep0 (b x : Nat) : Nat := Nat.sub x (Nat.land (Nat.shiftRight x 1) (maskLo b 0))

theorem swarStep0_digitVal {b m : Nat} (hb : 2 * m = 2 ^ b) (hj : 0 < b) {f : Nat → Nat}
    (hf : ∀ k, f k < 2) :
    swarStep0 b (digitVal 1 (2 * m) f) = digitVal 2 m (pairSum f) := by
  have h1 := digitVal_shiftRight_and_maskLo (b := b) (j := 0) (m := m) (e := 1)
    (by rw [Nat.zero_add, pow_one]; exact hb) hj (Nat.le_refl 1) (f := f) (by simpa using hf)
  simp only [pow_zero, Nat.zero_add, pow_one, Nat.mul_one] at h1
  change digitVal 1 (2 * m) f - ((digitVal 1 (2 * m) f >>> 1) &&& maskLo b 0) = _
  rw [h1]
  apply Nat.sub_eq_of_eq_add
  rw [digitVal_add, digitVal_two_mul]
  simp only [pairSum, Nat.mul_one, pow_one]
  congr 1
  funext k
  omega

/-- A SWAR round in three operations, `(y + (y >>> 2^j)) &&& maskLo b j`, valid as soon as the
sum of two neighbouring `2^j`-bit fields still fits into `2^j` bits. -/
def swarStepC (b j y : Nat) : Nat :=
  Nat.land (Nat.add y (Nat.shiftRight y (Nat.pow 2 j))) (maskLo b j)

theorem swarStepC_digitVal {b j m : Nat} (hb : 2 ^ (j + 1) * m = 2 ^ b) (hj : j < b)
    {f : Nat → Nat} (hf : ∀ k, f k + f (k + 1) < 2 ^ 2 ^ j) (h0 : ∀ k, 2 * m ≤ k → f k = 0) :
    swarStepC b j (digitVal (2 ^ j) (2 * m) f) = digitVal (2 ^ (j + 1)) m (pairSum f) := by
  have hf' : ∀ k, f k < 2 ^ 2 ^ j := fun k => Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (hf k)
  have hs := digitVal_shiftRight (Nat.two_pow_pos j) hf' h0 1
  rw [Nat.mul_one] at hs
  have h := digitVal_shiftRight_and_maskLo hb hj (e := 0) (Nat.zero_le 1) hf
  simp only [Nat.mul_zero, Nat.shiftRight_zero, Nat.add_zero] at h
  change (digitVal (2 ^ j) (2 * m) f + (digitVal (2 ^ j) (2 * m) f >>> 2 ^ j)) &&& maskLo b j = _
  rw [hs, digitVal_add]
  exact h

/-- `y + (y >>> w)`: every `w`-bit field receives the sum of itself and its upper neighbour. -/
def addShift (w y : Nat) : Nat := Nat.add y (Nat.shiftRight y w)

theorem addShift_digitVal {w n : Nat} (hw : 0 < w) {f : Nat → Nat} (hf : ∀ k, f k < 2 ^ w)
    (h0 : ∀ k, n ≤ k → f k = 0) (e : Nat) :
    addShift (w * e) (digitVal w n f) = digitVal w n (fun k => f k + f (k + e)) := by
  change digitVal w n f + (digitVal w n f >>> (w * e)) = _
  rw [digitVal_shiftRight hw hf h0, digitVal_add]

/-- The mask `0x000000FF…` on `2^b` bits (`5 ≤ b`): `ones b / 0x01010101`. -/
def mask32 (b : Nat) : Nat := Nat.div (ones b) 16843009

theorem mask32_eq (c : Nat) : mask32 (c + 5) = digitVal 32 (2 ^ c) (fun _ => 255) := by
  have h1 : ones (c + 5) = 16843009 * digitVal 32 (2 ^ c) (fun _ => 255) := by
    rw [← digitVal_const_mul, ones_eq, pow_add, Nat.mul_comm (2 ^ c)]
    exact (digitVal_ones 32 (2 ^ c)).symm
  change ones (c + 5) / 16843009 = _
  rw [h1, Nat.mul_div_cancel_left _ (by omega)]

/-! ### The fast population count -/

/-- Population count of `x < 2^(2^b)` for `5 ≤ b ≤ 31`: three SWAR rounds (to bytes), two
unmasked additions, one mask and one reduction modulo `2^32 - 1`. -/
def popFast (b x : Nat) : Nat :=
  Nat.mod
    (Nat.land (addShift 16 (addShift 8 (swarStepC b 2 (swarStep b 1 (swarStep0 b x)))))
      (mask32 b))
    4294967295

theorem popFast_eq {c x : Nat} (hc : c ≤ 26) (hx : x < 2 ^ 2 ^ (c + 5)) :
    popFast (c + 5) x = popcount (c + 5) x := by
  -- the bits of `x`
  obtain ⟨f0, hf0⟩ : ∃ f0 : Nat → Nat, f0 = fun k => (x.testBit k).toNat := ⟨_, rfl⟩
  have hb0 : ∀ k, f0 k ≤ 1 := fun k => by rw [hf0]; exact Bool.toNat_le _
  have hz0 : ∀ k, 2 ^ (c + 5) ≤ k → f0 k = 0 := fun k hk => by
    rw [hf0]
    simp only [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hk)),
      Bool.toNat_false]
  have hx0 : x = digitVal 1 (2 ^ (c + 5)) f0 := by
    rw [hf0, ← mod_two_pow_eq_digitVal, Nat.mod_eq_of_lt hx]
  -- the slow count is the sum of the bits, which is at most `2 ^ b < 2 ^ 32 - 1`
  have hpop : popcount (c + 5) x = ∑ k ∈ Finset.range (2 ^ (c + 5)), f0 k := by
    have h := popAux_digitVal (b := c + 5) (c + 5) 0 f0 (by omega)
      (fun k => Nat.lt_of_le_of_lt (hb0 k) (by simp))
    rw [pow_zero, ← hx0] at h
    exact h
  have hlt : popcount (c + 5) x < 4294967295 := by
    have h1 : popcount (c + 5) x ≤ 2 ^ (c + 5) := by
      rw [popcount_eq hx]
      exact Nat.le_trans (Finset.card_filter_le _ _) (Nat.le_of_eq (Finset.card_range _))
    have h2 : 2 ^ (c + 5) ≤ 2 ^ 31 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hm := mask32_eq c
  have hpow : 2 ^ (c + 5) = 2 * (2 * (2 * (4 * 2 ^ c))) := by rw [pow_add]; omega
  generalize 2 ^ c = n at hpow hm
  rw [hpow] at hz0 hx0 hpop
  -- the digits after one, two and three SWAR rounds
  obtain ⟨f1, hf1⟩ : ∃ f1 : Nat → Nat, f1 = pairSum f0 := ⟨_, rfl⟩
  obtain ⟨f2, hf2⟩ : ∃ f2 : Nat → Nat, f2 = pairSum f1 := ⟨_, rfl⟩
  obtain ⟨f3, hf3⟩ : ∃ f3 : Nat → Nat, f3 = pairSum f2 := ⟨_, rfl⟩
  have hb1 : ∀ k, f1 k ≤ 2 := by rw [hf1]; exact pairSum_le hb0
  have hz1 : ∀ k, 2 * (2 * (4 * n)) ≤ k → f1 k = 0 := by rw [hf1]; exact pairSum_eq_zero hz0
  have hb2 : ∀ k, f2 k ≤ 4 := by rw [hf2]; exact pairSum_le hb1
  have hz2 : ∀ k, 2 * (4 * n) ≤ k → f2 k = 0 := by rw [hf2]; exact pairSum_eq_zero hz1
  have hb3 : ∀ k, f3 k ≤ 8 := by rw [hf3]; exact pairSum_le hb2
  have hz3 : ∀ k, 4 * n ≤ k → f3 k = 0 := by rw [hf3]; exact pairSum_eq_zero hz2
  have h1 : swarStep0 (c + 5) x = digitVal 2 (2 * (2 * (4 * n))) f1 := by
    rw [hx0, hf1]
    exact swarStep0_digitVal hpow.symm (by omega) (fun k => Nat.lt_succ_of_le (hb0 k))
  have h2 : swarStep (c + 5) 1 (digitVal 2 (2 * (2 * (4 * n))) f1) =
      digitVal 4 (2 * (4 * n)) f2 := by
    rw [hf2]
    exact swarStep_digitVal (j := 1) (by rw [hpow]; omega) (by omega)
      (fun k => Nat.lt_of_le_of_lt (hb1 k) (by decide))
  have h3 : swarStepC (c + 5) 2 (digitVal 4 (2 * (4 * n)) f2) = digitVal 8 (4 * n) f3 := by
    rw [hf3]
    exact swarStepC_digitVal (j := 2) (by rw [hpow]; omega) (by omega)
      (fun k => Nat.lt_of_le_of_lt (Nat.add_le_add (hb2 k) (hb2 (k + 1))) (by decide)) hz2
  -- two unmasked additions: every byte becomes the sum of four consecutive bytes
  have h4 : addShift 8 (digitVal 8 (4 * n) f3) =
      digitVal 8 (4 * n) (fun k => f3 k + f3 (k + 1)) :=
    addShift_digitVal (w := 8) (by omega) (fun k => Nat.lt_of_le_of_lt (hb3 k) (by decide)) hz3 1
  have h5 : addShift 16 (digitVal 8 (4 * n) (fun k => f3 k + f3 (k + 1))) =
      digitVal 8 (4 * n) (fun k => f3 k + f3 (k + 1) + (f3 (k + 2) + f3 (k + 2 + 1))) :=
    addShift_digitVal (w := 8) (by omega)
      (fun k => Nat.lt_of_le_of_lt (Nat.add_le_add (hb3 k) (hb3 (k + 1))) (by decide))
      (fun k hk => by rw [hz3 k hk, hz3 (k + 1) (by omega)]) 2
  -- keep one byte per 32-bit field and add the fields up
  have h6 : digitVal 8 (4 * n) (fun k => f3 k + f3 (k + 1) + (f3 (k + 2) + f3 (k + 2 + 1))) &&&
      mask32 (c + 5) =
      digitVal 32 n (fun k => f3 (4 * k) + f3 (4 * k + 1) + (f3 (4 * k + 2) + f3 (4 * k + 3))) := by
    rw [hm]
    exact digitVal_and_mask32 (fun k => Nat.lt_of_le_of_lt
      (Nat.add_le_add (Nat.add_le_add (hb3 k) (hb3 (k + 1)))
        (Nat.add_le_add (hb3 (k + 2)) (hb3 (k + 2 + 1)))) (by decide))
  have h7 := digitVal_mod_two_pow_sub_one 32 n
    (fun k => f3 (4 * k) + f3 (4 * k + 1) + (f3 (4 * k + 2) + f3 (4 * k + 3)))
  rw [show 2 ^ 32 - 1 = 4294967295 by decide, ← sum_range_four_mul, hf3, sum_pairSum, hf2,
    sum_pairSum, hf1, sum_pairSum, ← hpop, ← hf1, ← hf2, ← hf3] at h7
  change (addShift 16 (addShift 8 (swarStepC (c + 5) 2 (swarStep (c + 5) 1
    (swarStep0 (c + 5) x)))) &&& mask32 (c + 5)) % 4294967295 = _
  rw [h1, h2, h3, h4, h5, h6, h7, Nat.mod_eq_of_lt hlt]

/-- Population count of `x < 2^(2^b)` with few big operations. -/
def popcountF (b x : Nat) : Nat :=
  bif Bool.and (Nat.ble 5 b) (Nat.ble b 31) then popFast b x else popcount b x

theorem popcountF_eq {b x : Nat} (hx : x < 2 ^ 2 ^ b) : popcountF b x = popcount b x := by
  rw [popcountF]
  cases h : Bool.and (Nat.ble 5 b) (Nat.ble b 31)
  · rfl
  · rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 5 := ⟨b - 5, by omega⟩
    exact popFast_eq (by omega) hx

theorem popcountF_eq_card_filter {b x : Nat} (hx : x < 2 ^ 2 ^ b) :
    popcountF b x = ((Finset.range (2 ^ b)).filter (fun p => x.testBit p)).card := by
  rw [popcountF_eq hx, popcount_eq hx]

/-- Counting set bits of a truth table is counting satisfying Boolean assignments. -/
theorem popcountF_eq_card_filter_fun {b x : Nat} (hx : x < 2 ^ 2 ^ b)
    (P : (Fin b → Bool) → Bool) (h : ∀ p < 2 ^ b, x.testBit p = P (fun i => p.testBit i)) :
    popcountF b x = (Finset.univ.filter (fun v : Fin b → Bool => P v = true)).card := by
  rw [popcountF_eq hx, popcount_eq_card_filter_fun hx P h]

end RACert
