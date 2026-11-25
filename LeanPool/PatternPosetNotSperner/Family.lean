/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler B. Hughes
-/

module

public import Mathlib.Order.Interval.Finset.Nat
public import LeanPool.PatternPosetNotSperner.Defs
public import LeanPool.PatternPosetNotSperner.BoxChains

import Mathlib.Tactic.Linarith

/-!
# Infinite Family `τ_k` with Exact Sperner Deficiency `k`

Formalizes the two-leader infinite family `τ_k` (`k ≥ 1`) of length `6k + 4`:
- `tau k`: first entry `4k + 2` (`4k + 3` 1-indexed), second entry `2k` (`2k + 1` 1-indexed),
  followed by all remaining entries in strictly decreasing order.
- Complete disjoint classification of `Downset (tau k)` into:
  1. Valley patterns `patP x y z` (`0 ≤ x, y ≤ 2k + 1`, `0 ≤ z ≤ 2k`, `x + y ≥ 1`);
  2. One-leader valley-free patterns `patQ p q` (`p ≥ 1`, either `p ≤ 2k + 1 ∧ q ≤ 4k + 1`
     or `p ≤ 4k + 2 ∧ q ≤ 2k`);
  3. Decreasing patterns `patD l` (`l ≤ 6k + 2`).
- Explicit antichain of size `3k^2 + 9k + 5` inside `Downset (tau k)`.
- Explicit matching cover by `3k^2 + 9k + 5` chains (`3k^2 + 5k + 2` symmetric box chains
  plus `4k + 3` valley-free chains), proving `width (Downset (tau k)) = 3k^2 + 9k + 5`.
- Exact largest rank proof `largestRank (Downset (tau k)) = 3k^2 + 8k + 5`.
- Exact Sperner deficiency `width (Downset (tau k)) = largestRank (Downset (tau k)) + k`
  and `¬ IsSperner (Downset (tau k))` for all `k ≥ 1`.
-/

@[expose] public section

namespace PatternPoset

/-! ### Canonical Pattern Families `P(x, y, z)`, `Q(p, q)`, `D(l)`, and `τ_k` -/

/-- Plain `ℕ` value formula for `patP x y z` at position `i` (0-indexed). -/
def patPVal (x y z i : ℕ) : ℕ :=
  if i = 0 then y + z + 1
  else if i = 1 then z
  else if i < x + 2 then x + y + z + 3 - i
  else if i < x + y + 2 then x + y + z + 2 - i
  else x + y + z + 1 - i

/-- Plain `ℕ` inverse formula for `patP x y z` at value `v` (0-indexed). -/
def patPInvVal (x y z v : ℕ) : ℕ :=
  if v = y + z + 1 then 0
  else if v = z then 1
  else if y + z + 2 ≤ v then x + y + z + 3 - v
  else if z + 1 ≤ v then x + y + z + 2 - v
  else x + y + z + 1 - v

/-- Forward entry map of `patP x y z` on `Fin (x + y + z + 2)` (0-indexed). -/
def patPFun (x y z : ℕ) (i : Fin (x + y + z + 2)) : Fin (x + y + z + 2) :=
  ⟨patPVal x y z i.val, by unfold patPVal; split_ifs <;> omega⟩

/-- Inverse entry map of `patP x y z` on `Fin (x + y + z + 2)` (0-indexed). -/
def patPInv (x y z : ℕ) (v : Fin (x + y + z + 2)) : Fin (x + y + z + 2) :=
  ⟨patPInvVal x y z v.val, by unfold patPInvVal; split_ifs <;> omega⟩

/-- Two-leader pattern `P(x, y, z)` of length `x + y + z + 2` keeping both leaders,
`x` tail entries above the first leader, `y` between the leaders, and `z` below the second. -/
def patP (x y z : ℕ) : Perm where
  len := x + y + z + 2
  perm :=
    { toFun := patPFun x y z
      invFun := patPInv x y z
      left_inv := fun i => Fin.ext (by
        change patPInvVal x y z (patPVal x y z i.val) = i.val
        have hi : i.val < x + y + z + 2 := i.isLt
        unfold patPVal
        split_ifs <;> (unfold patPInvVal; split_ifs <;> omega))
      right_inv := fun v => Fin.ext (by
        change patPVal x y z (patPInvVal x y z v.val) = v.val
        have hv : v.val < x + y + z + 2 := v.isLt
        unfold patPInvVal
        split_ifs <;>
          (simp only [patPVal, ↓reduceIte, Nat.one_ne_zero]; try split_ifs) <;> omega) }

/-- The infinite family `τ_k` of length `6k + 4`: first entry `4k + 2` (`4k + 3` in 1-indexing),
second entry `2k` (`2k + 1` in 1-indexing), followed by the remaining values decreasing. -/
def tau (k : ℕ) : Perm := patP (2 * k + 1) (2 * k + 1) (2 * k)

theorem tau_len (k : ℕ) : (tau k).len = 6 * k + 4 := by
  change (2 * k + 1) + (2 * k + 1) + 2 * k + 2 = 6 * k + 4
  omega

/-- First entry of `tau k` is `4k + 2` (i.e., `4k + 3` in 1-indexed notation). -/
theorem tau_entry_zero (k : ℕ) :
    ((tau k).perm ⟨0, by rw [tau_len]; omega⟩).val = 4 * k + 2 := by
  change patPVal (2 * k + 1) (2 * k + 1) (2 * k) 0 = 4 * k + 2
  simp only [patPVal, ↓reduceIte]
  omega

/-- Second entry of `tau k` is `2k` (i.e., `2k + 1` in 1-indexed notation). -/
theorem tau_entry_one (k : ℕ) :
    ((tau k).perm ⟨1, by rw [tau_len]; omega⟩).val = 2 * k := by
  change patPVal (2 * k + 1) (2 * k + 1) (2 * k) 1 = 2 * k
  simp only [patPVal, ↓reduceIte, Nat.one_ne_zero]

/-- All entries of `tau k` from index `2` onward are strictly decreasing. -/
theorem tau_tail_strictAnti (k : ℕ) (i j : Fin (tau k).len)
    (hi : 2 ≤ i.val) (hij : i < j) : (tau k).perm j < (tau k).perm i := by
  change patPVal (2 * k + 1) (2 * k + 1) (2 * k) j.val <
    patPVal (2 * k + 1) (2 * k + 1) (2 * k) i.val
  have hi_lt : i.val < (2 * k + 1) + (2 * k + 1) + 2 * k + 2 := i.isLt
  have hj_lt : j.val < (2 * k + 1) + (2 * k + 1) + 2 * k + 2 := j.isLt
  have hlt : i.val < j.val := hij
  unfold patPVal
  split_ifs <;> omega

/-- Plain `ℕ` value formula for `patQ p q` at position `i` (0-indexed). -/
def patQVal (p q i : ℕ) : ℕ :=
  if i = 0 then q
  else if i < p + 1 then p + q + 1 - i
  else p + q - i

/-- Plain `ℕ` inverse formula for `patQ p q` at value `v` (0-indexed). -/
def patQInvVal (p q v : ℕ) : ℕ :=
  if v = q then 0
  else if q + 1 ≤ v then p + q + 1 - v
  else p + q - v

/-- Forward entry map of `patQ p q` on `Fin (p + q + 1)` (0-indexed). -/
def patQFun (p q : ℕ) (i : Fin (p + q + 1)) : Fin (p + q + 1) :=
  ⟨patQVal p q i.val, by unfold patQVal; split_ifs <;> omega⟩

/-- Inverse entry map of `patQ p q` on `Fin (p + q + 1)` (0-indexed). -/
def patQInv (p q : ℕ) (v : Fin (p + q + 1)) : Fin (p + q + 1) :=
  ⟨patQInvVal p q v.val, by unfold patQInvVal; split_ifs <;> omega⟩

/-- One-leader valley-free pattern `Q(p, q)` of length `p + q + 1`:
first entry `q` (`q + 1` in 1-indexing), followed by `p` entries above it and `q` below it
in strictly decreasing order. -/
def patQ (p q : ℕ) : Perm where
  len := p + q + 1
  perm :=
    { toFun := patQFun p q
      invFun := patQInv p q
      left_inv := fun i => Fin.ext (by
        change patQInvVal p q (patQVal p q i.val) = i.val
        have hi : i.val < p + q + 1 := i.isLt
        unfold patQInvVal patQVal
        split_ifs <;> omega)
      right_inv := fun v => Fin.ext (by
        change patQVal p q (patQInvVal p q v.val) = v.val
        have hv : v.val < p + q + 1 := v.isLt
        unfold patQVal patQInvVal
        split_ifs <;> omega) }

/-- Strictly decreasing permutation `D(l) = (l, l-1, …, 1)` of length `l`. -/
def patD (l : ℕ) : Perm where
  len := l
  perm :=
    { toFun := fun i => ⟨l - 1 - i.val, by omega⟩
      invFun := fun i => ⟨l - 1 - i.val, by omega⟩
      left_inv := fun i => Fin.ext (by dsimp; omega)
      right_inv := fun i => Fin.ext (by dsimp; omega) }

/-! ### Special Cases, Valleys, Injectivity, and Disjointness -/

theorem patP_zero_zero (z : ℕ) : patP 0 0 z = patD (z + 2) := by
  apply Perm.ext_val (by dsimp [patP, patD]; omega)
  intro i
  change patPVal 0 0 z i.val = z + 2 - 1 - i.val
  have hi : i.val < 0 + 0 + z + 2 := i.isLt
  unfold patPVal
  split_ifs <;> omega

theorem patQ_zero (q : ℕ) : patQ 0 q = patD (q + 1) := by
  apply Perm.ext_val (by dsimp [patQ, patD]; omega)
  intro i
  change patQVal 0 q i.val = q + 1 - 1 - i.val
  have hi : i.val < 0 + q + 1 := i.isLt
  unfold patQVal
  split_ifs <;> omega

private theorem perm_val_eq_of_eq {σ τ : Perm} (h : σ = τ) {k : ℕ}
    (h1 : k < σ.len) (h2 : k < τ.len) :
    (σ.perm ⟨k, h1⟩).val = (τ.perm ⟨k, h2⟩).val := by
  subst h; rfl

/-- `P(x, y, z)` has a valley whenever `x + y ≥ 1`. -/
theorem patP_hasValley {x y z : ℕ} (h : 1 ≤ x + y) : HasValley (patP x y z) := by
  refine ⟨⟨0, by dsimp [patP]; omega⟩, ⟨1, by dsimp [patP]; omega⟩,
    ⟨2, by dsimp [patP]; omega⟩, ?_, ?_, ?_, ?_⟩
  · exact Nat.zero_lt_one
  · exact Nat.one_lt_two
  · change patPVal x y z 1 < patPVal x y z 0
    simp only [patPVal, ↓reduceIte, Nat.one_ne_zero]
    omega
  · change patPVal x y z 1 < patPVal x y z 2
    simp only [patPVal, ↓reduceIte, Nat.one_ne_zero, show (2 : ℕ) ≠ 0 by decide,
      show (2 : ℕ) ≠ 1 by decide]
    split_ifs <;> omega

/-- `Q(p, q)` is valley-free. -/
theorem patQ_not_hasValley (p q : ℕ) : ¬ HasValley (patQ p q) := by
  rintro ⟨i, j, k, hij, hjk, _, hjk'⟩
  have hj1 : 1 ≤ j.val := by omega
  have hlt : j.val < k.val := hjk
  have hk : k.val < p + q + 1 := k.isLt
  change patQVal p q j.val < patQVal p q k.val at hjk'
  unfold patQVal at hjk'
  split_ifs at hjk' <;> omega

/-- `D(l)` is valley-free. -/
theorem patD_not_hasValley (l : ℕ) : ¬ HasValley (patD l) := by
  rintro ⟨_, j, k, _, hjk, _, hjk'⟩
  change l - 1 - j.val < l - 1 - k.val at hjk'
  have hlt : j.val < k.val := hjk
  have hk : k.val < l := k.isLt
  omega

/-- `patP` is injective in `(x, y, z)`. -/
theorem patP_injective {x₁ y₁ z₁ x₂ y₂ z₂ : ℕ}
    (h : patP x₁ y₁ z₁ = patP x₂ y₂ z₂) :
    x₁ = x₂ ∧ y₁ = y₂ ∧ z₁ = z₂ := by
  have hlen : x₁ + y₁ + z₁ + 2 = x₂ + y₂ + z₂ + 2 := congrArg Perm.len h
  have h0 := perm_val_eq_of_eq h (k := 0) (by dsimp [patP]; omega) (by dsimp [patP]; omega)
  have h1 := perm_val_eq_of_eq h (k := 1) (by dsimp [patP]; omega) (by dsimp [patP]; omega)
  change patPVal x₁ y₁ z₁ 0 = patPVal x₂ y₂ z₂ 0 at h0
  change patPVal x₁ y₁ z₁ 1 = patPVal x₂ y₂ z₂ 1 at h1
  simp only [patPVal, ↓reduceIte, Nat.one_ne_zero] at h0 h1
  omega

/-- `patQ` is injective in `(p, q)`. -/
theorem patQ_injective {p₁ q₁ p₂ q₂ : ℕ}
    (h : patQ p₁ q₁ = patQ p₂ q₂) : p₁ = p₂ ∧ q₁ = q₂ := by
  have hlen : p₁ + q₁ + 1 = p₂ + q₂ + 1 := congrArg Perm.len h
  have h0 := perm_val_eq_of_eq h (k := 0) (by dsimp [patQ]; omega) (by dsimp [patQ]; omega)
  change patQVal p₁ q₁ 0 = patQVal p₂ q₂ 0 at h0
  simp only [patQVal, ↓reduceIte] at h0
  omega

/-- `patD` is injective in `l`. -/
theorem patD_injective {l₁ l₂ : ℕ} (h : patD l₁ = patD l₂) : l₁ = l₂ :=
  congrArg Perm.len h

theorem patP_ne_patQ {x y z p q : ℕ} (hxy : 1 ≤ x + y) : patP x y z ≠ patQ p q := by
  intro h
  exact patQ_not_hasValley p q (h ▸ patP_hasValley hxy)

theorem patP_ne_patD {x y z l : ℕ} (hxy : 1 ≤ x + y) : patP x y z ≠ patD l := by
  intro h
  exact patD_not_hasValley l (h ▸ patP_hasValley hxy)

theorem patQ_ne_patD {p q l : ℕ} (hp : 1 ≤ p) : patQ p q ≠ patD l := by
  intro h
  have hlen : p + q + 1 = l := congrArg Perm.len h
  have h0 := perm_val_eq_of_eq h (k := 0) (by dsimp [patQ]; omega) (by dsimp [patD]; omega)
  change patQVal p q 0 = l - 1 - 0 at h0
  simp only [patQVal, ↓reduceIte] at h0
  omega

/-! ### Value-Order Band Lemmas and Monotonicity -/

private def patPBand (x y i : ℕ) : ℕ :=
  if i = 0 then 3
  else if i = 1 then 1
  else if i < x + 2 then 4
  else if i < x + y + 2 then 2
  else 0

private def patQBand (p i : ℕ) : ℕ :=
  if i = 0 then 1
  else if i < p + 1 then 2
  else 0

private theorem patPVal_lt_iff {x y z a b : ℕ}
    (ha : a < x + y + z + 2) (hb : b < x + y + z + 2) :
    patPVal x y z a < patPVal x y z b ↔
    patPBand x y a < patPBand x y b ∨ (patPBand x y a = patPBand x y b ∧ b < a) := by
  unfold patPVal patPBand
  split_ifs <;> omega

private theorem patQVal_lt_iff {p q a b : ℕ}
    (ha : a < p + q + 1) (hb : b < p + q + 1) :
    patQVal p q a < patQVal p q b ↔
    patQBand p a < patQBand p b ∨ (patQBand p a = patQBand p b ∧ b < a) := by
  unfold patQVal patQBand
  split_ifs <;> omega

private def patPNo1Band (x i : ℕ) : ℕ :=
  if i = 0 then 1
  else if i < x + 2 then 2
  else 0

private theorem patPVal_lt_iff_no1 {x y z a b : ℕ}
    (ha : a < x + y + z + 2) (hb : b < x + y + z + 2) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    patPVal x y z a < patPVal x y z b ↔
    patPNo1Band x a < patPNo1Band x b ∨ (patPNo1Band x a = patPNo1Band x b ∧ b < a) := by
  unfold patPVal patPNo1Band
  split_ifs <;> omega

private def patPNo0Band (x y i : ℕ) : ℕ :=
  if i = 1 then 1
  else if i < x + y + 2 then 2
  else 0

private theorem patPVal_lt_iff_no0 {x y z a b : ℕ}
    (ha : a < x + y + z + 2) (hb : b < x + y + z + 2) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    patPVal x y z a < patPVal x y z b ↔
    patPNo0Band x y a < patPNo0Band x y b ∨
      (patPNo0Band x y a = patPNo0Band x y b ∧ b < a) := by
  unfold patPVal patPNo0Band
  split_ifs <;> omega

private theorem patPVal_lt_iff_tail {x y z a b : ℕ}
    (ha : a < x + y + z + 2) (hb : b < x + y + z + 2) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) :
    patPVal x y z a < patPVal x y z b ↔ b < a := by
  unfold patPVal
  split_ifs <;> omega

theorem patP_le_patP {x₁ y₁ z₁ x₂ y₂ z₂ : ℕ}
    (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) (hz : z₁ ≤ z₂) :
    patP x₁ y₁ z₁ ≤ patP x₂ y₂ z₂ := by
  rw [le_iff_contains]
  let fVal : ℕ → ℕ := fun i =>
    if i < x₁ + 2 then i
    else if i < x₁ + y₁ + 2 then i + (x₂ - x₁)
    else i + (x₂ - x₁) + (y₂ - y₁)
  let f : Fin (x₁ + y₁ + z₁ + 2) → Fin (x₂ + y₂ + z₂ + 2) :=
    fun i => ⟨fVal i.val, by have := i.isLt; dsimp only [fVal]; split_ifs <;> omega⟩
  have hf_sm : StrictMono f := by
    intro a b hab
    change fVal a.val < fVal b.val
    have : a.val < b.val := hab
    dsimp only [fVal]
    split_ifs <;> omega
  have hband : ∀ i : Fin (x₁ + y₁ + z₁ + 2),
      patPBand x₂ y₂ (fVal i.val) = patPBand x₁ y₁ i.val := by
    intro i
    dsimp only [patPBand, fVal]
    split_ifs <;> omega
  refine ⟨OrderEmbedding.ofStrictMono f hf_sm, ?_⟩
  intro i j
  change patPVal x₁ y₁ z₁ i.val < patPVal x₁ y₁ z₁ j.val ↔
    patPVal x₂ y₂ z₂ (fVal i.val) < patPVal x₂ y₂ z₂ (fVal j.val)
  have hi : i.val < x₁ + y₁ + z₁ + 2 := i.isLt
  have hj : j.val < x₁ + y₁ + z₁ + 2 := j.isLt
  have hfi : fVal i.val < x₂ + y₂ + z₂ + 2 := (f i).isLt
  have hfj : fVal j.val < x₂ + y₂ + z₂ + 2 := (f j).isLt
  rw [patPVal_lt_iff hi hj, patPVal_lt_iff hfi hfj, hband i, hband j]
  have hgt : j.val < i.val ↔ fVal j.val < fVal i.val := by
    constructor
    · intro h; exact hf_sm h
    · intro h; exact hf_sm.lt_iff_lt.mp h
  rw [hgt]

theorem patQ_le_patQ {p₁ q₁ p₂ q₂ : ℕ} (hp : p₁ ≤ p₂) (hq : q₁ ≤ q₂) :
    patQ p₁ q₁ ≤ patQ p₂ q₂ := by
  rw [le_iff_contains]
  let fVal : ℕ → ℕ := fun i => if i < p₁ + 1 then i else i + (p₂ - p₁)
  let f : Fin (p₁ + q₁ + 1) → Fin (p₂ + q₂ + 1) :=
    fun i => ⟨fVal i.val, by have := i.isLt; dsimp only [fVal]; split_ifs <;> omega⟩
  have hf_sm : StrictMono f := by
    intro a b hab
    change fVal a.val < fVal b.val
    have : a.val < b.val := hab
    dsimp only [fVal]
    split_ifs <;> omega
  have hband : ∀ i : Fin (p₁ + q₁ + 1), patQBand p₂ (fVal i.val) = patQBand p₁ i.val := by
    intro i
    dsimp only [patQBand, fVal]
    split_ifs <;> omega
  refine ⟨OrderEmbedding.ofStrictMono f hf_sm, ?_⟩
  intro i j
  change patQVal p₁ q₁ i.val < patQVal p₁ q₁ j.val ↔
    patQVal p₂ q₂ (fVal i.val) < patQVal p₂ q₂ (fVal j.val)
  have hi : i.val < p₁ + q₁ + 1 := i.isLt
  have hj : j.val < p₁ + q₁ + 1 := j.isLt
  have hfi : fVal i.val < p₂ + q₂ + 1 := (f i).isLt
  have hfj : fVal j.val < p₂ + q₂ + 1 := (f j).isLt
  rw [patQVal_lt_iff hi hj, patQVal_lt_iff hfi hfj, hband i, hband j]
  have hgt : j.val < i.val ↔ fVal j.val < fVal i.val := hf_sm.lt_iff_lt.symm
  rw [hgt]

theorem patD_le_patD {l₁ l₂ : ℕ} (hl : l₁ ≤ l₂) : patD l₁ ≤ patD l₂ := by
  rw [le_iff_contains]
  let f : Fin l₁ → Fin l₂ := fun i => ⟨i.val, by omega⟩
  have hf_sm : StrictMono f := fun _ _ hab => hab
  refine ⟨OrderEmbedding.ofStrictMono f hf_sm, ?_⟩
  intro i j
  change l₁ - 1 - i.val < l₁ - 1 - j.val ↔ l₂ - 1 - i.val < l₂ - 1 - j.val
  have hi : i.val < l₁ := i.isLt
  have hj : j.val < l₁ := j.isLt
  omega

theorem patP_le_tau {k x y z : ℕ}
    (hx : x ≤ 2 * k + 1) (hy : y ≤ 2 * k + 1) (hz : z ≤ 2 * k) :
    patP x y z ≤ tau k :=
  patP_le_patP hx hy hz

theorem patQ_le_tau_leaderA (k : ℕ) : patQ (2 * k + 1) (4 * k + 1) ≤ tau k := by
  rw [le_iff_contains]
  let fVal : ℕ → ℕ := fun i => if i = 0 then 0 else i + 1
  let f : Fin ((2 * k + 1) + (4 * k + 1) + 1) →
      Fin ((2 * k + 1) + (2 * k + 1) + 2 * k + 2) :=
    fun i => ⟨fVal i.val, by have := i.isLt; dsimp only [fVal]; split_ifs <;> omega⟩
  have hf_sm : StrictMono f := by
    intro a b hab
    change fVal a.val < fVal b.val
    have : a.val < b.val := hab
    dsimp only [fVal]
    split_ifs <;> omega
  have hband : ∀ i : Fin ((2 * k + 1) + (4 * k + 1) + 1),
      patPNo1Band (2 * k + 1) (fVal i.val) = patQBand (2 * k + 1) i.val := by
    intro i
    by_cases h0 : i.val = 0
    · simp [patPNo1Band, patQBand, fVal, h0]
    · have hfval : fVal i.val = i.val + 1 := by simp [fVal, h0]
      rw [hfval]
      unfold patPNo1Band patQBand
      by_cases hlt : i.val < (2 * k + 1) + 1
      · have hlt2 : i.val + 1 < (2 * k + 1) + 2 := by omega
        simp [h0, hlt, hlt2]
      · have hlt2 : ¬ i.val + 1 < (2 * k + 1) + 2 := by omega
        simp [h0, hlt, hlt2]
  refine ⟨OrderEmbedding.ofStrictMono f hf_sm, ?_⟩
  intro i j
  change patQVal (2 * k + 1) (4 * k + 1) i.val < patQVal (2 * k + 1) (4 * k + 1) j.val ↔
    patPVal (2 * k + 1) (2 * k + 1) (2 * k) (fVal i.val) <
    patPVal (2 * k + 1) (2 * k + 1) (2 * k) (fVal j.val)
  have hi : i.val < (2 * k + 1) + (4 * k + 1) + 1 := i.isLt
  have hj : j.val < (2 * k + 1) + (4 * k + 1) + 1 := j.isLt
  have hfi : fVal i.val < (2 * k + 1) + (2 * k + 1) + 2 * k + 2 := (f i).isLt
  have hfj : fVal j.val < (2 * k + 1) + (2 * k + 1) + 2 * k + 2 := (f j).isLt
  have hfi1 : fVal i.val ≠ 1 := by dsimp only [fVal]; split_ifs <;> omega
  have hfj1 : fVal j.val ≠ 1 := by dsimp only [fVal]; split_ifs <;> omega
  rw [patQVal_lt_iff hi hj, patPVal_lt_iff_no1 hfi hfj hfi1 hfj1, hband i, hband j]
  have hgt : j.val < i.val ↔ fVal j.val < fVal i.val := hf_sm.lt_iff_lt.symm
  rw [hgt]

theorem patQ_le_tau_leaderB (k : ℕ) : patQ (4 * k + 2) (2 * k) ≤ tau k := by
  rw [le_iff_contains]
  let f : Fin ((4 * k + 2) + (2 * k) + 1) →
      Fin ((2 * k + 1) + (2 * k + 1) + 2 * k + 2) := fun i => ⟨i.val + 1, by omega⟩
  have hf_sm : StrictMono f := fun _ _ hab => Nat.add_lt_add_right hab 1
  have hband : ∀ i : Fin ((4 * k + 2) + (2 * k) + 1),
      patPNo0Band (2 * k + 1) (2 * k + 1) (i.val + 1) = patQBand (4 * k + 2) i.val := by
    intro i
    dsimp only [patPNo0Band, patQBand]
    split_ifs <;> omega
  refine ⟨OrderEmbedding.ofStrictMono f hf_sm, ?_⟩
  intro i j
  change patQVal (4 * k + 2) (2 * k) i.val < patQVal (4 * k + 2) (2 * k) j.val ↔
    patPVal (2 * k + 1) (2 * k + 1) (2 * k) (i.val + 1) <
    patPVal (2 * k + 1) (2 * k + 1) (2 * k) (j.val + 1)
  have hi : i.val < (4 * k + 2) + (2 * k) + 1 := i.isLt
  have hj : j.val < (4 * k + 2) + (2 * k) + 1 := j.isLt
  rw [patQVal_lt_iff hi hj, patPVal_lt_iff_no0 (by omega) (by omega) (by omega) (by omega),
      hband i, hband j]
  have hgt : j.val < i.val ↔ j.val + 1 < i.val + 1 := by omega
  rw [hgt]

theorem patQ_le_tau {k p q : ℕ}
    (h : (p ≤ 2 * k + 1 ∧ q ≤ 4 * k + 1) ∨ (p ≤ 4 * k + 2 ∧ q ≤ 2 * k)) :
    patQ p q ≤ tau k := by
  rcases h with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact (patQ_le_patQ hp hq).trans (patQ_le_tau_leaderA k)
  · exact (patQ_le_patQ hp hq).trans (patQ_le_tau_leaderB k)

theorem patD_le_tau {k l : ℕ} (hl : l ≤ 6 * k + 2) : patD l ≤ tau k := by
  refine (patD_le_patD hl).trans ?_
  rw [le_iff_contains]
  let f : Fin (6 * k + 2) → Fin ((2 * k + 1) + (2 * k + 1) + 2 * k + 2) :=
    fun i => ⟨i.val + 2, by omega⟩
  have hf_sm : StrictMono f := fun _ _ hab => Nat.add_lt_add_right hab 2
  refine ⟨OrderEmbedding.ofStrictMono f hf_sm, ?_⟩
  intro i j
  change 6 * k + 2 - 1 - i.val < 6 * k + 2 - 1 - j.val ↔
    patPVal (2 * k + 1) (2 * k + 1) (2 * k) (i.val + 2) <
    patPVal (2 * k + 1) (2 * k + 1) (2 * k) (j.val + 2)
  have hi : i.val < 6 * k + 2 := i.isLt
  have hj : j.val < 6 * k + 2 := j.isLt
  rw [patPVal_lt_iff_tail (by omega) (by omega) (by omega) (by omega)]
  omega

/-! ### Complete Classification of `Downset (tau k)` -/

/-- Downward-closed subsets of `Fin m` are initial segments `{i | i.val < S.card}`. -/
private theorem downward_closed_fin_iff {m : ℕ} (S : Finset (Fin m))
    (hdown : ∀ i j : Fin m, j < i → i ∈ S → j ∈ S) :
    ∀ i : Fin m, i ∈ S ↔ i.val < S.card := by
  intro i
  constructor
  · intro hi
    have hsub : Finset.univ.filter (fun j : Fin m => j.val ≤ i.val) ⊆ S := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rcases eq_or_lt_of_le hj.2 with heq | hlt
      · exact (Fin.ext heq) ▸ hi
      · exact hdown i j hlt hi
    have hcard : (Finset.univ.filter (fun j : Fin m => j.val ≤ i.val)).card = i.val + 1 := by
      have hbij : (Finset.univ.filter (fun j : Fin m => j.val ≤ i.val)).card =
          (Finset.range (i.val + 1)).card := by
        refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
        · intro j hj; rw [Finset.mem_filter] at hj; rw [Finset.mem_range]; omega
        · intro a _ b _ h; exact Fin.ext h
        · intro r hr; rw [Finset.mem_range] at hr
          refine ⟨⟨r, by omega⟩, ?_, rfl⟩
          rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by dsimp; omega⟩
      rw [hbij, Finset.card_range]
    have := Finset.card_le_card hsub
    omega
  · intro hlt
    by_contra hni
    have hsub : S ⊆ Finset.univ.filter (fun j : Fin m => j.val < i.val) := by
      intro j hj
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hge
      rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with heq | hgt
      · exact hni ((Fin.ext heq) ▸ hj)
      · exact hni (hdown j i hgt hj)
    have hcard : (Finset.univ.filter (fun j : Fin m => j.val < i.val)).card = i.val := by
      have hbij : (Finset.univ.filter (fun j : Fin m => j.val < i.val)).card =
          (Finset.range i.val).card := by
        refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
        · intro j hj; rw [Finset.mem_filter] at hj; rw [Finset.mem_range]; exact hj.2
        · intro a _ b _ h; exact Fin.ext h
        · intro r hr; rw [Finset.mem_range] at hr
          refine ⟨⟨r, lt_trans hr i.isLt⟩, ?_, rfl⟩
          rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hr⟩
      rw [hbij, Finset.card_range]
    have := Finset.card_le_card hsub
    omega

/-- Counting preimages of a half-open interval `[a, b)` under a strictly monotone map
`Fin m ↪o Fin n`. -/
private theorem card_filter_lt_le {m n : ℕ} (f : Fin m ↪o Fin n) (a b : ℕ) (hab : a ≤ b) :
    (Finset.univ.filter (fun i : Fin m => (f i).val < b)).card -
    (Finset.univ.filter (fun i : Fin m => (f i).val < a)).card ≤ b - a := by
  have hsub : Finset.univ.filter (fun i : Fin m => (f i).val < a) ⊆
      Finset.univ.filter (fun i : Fin m => (f i).val < b) := by
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_univ _, lt_of_lt_of_le hi.2 hab⟩
  have hadd := Finset.card_sdiff_add_card_eq_card hsub
  have hle : ((Finset.univ.filter (fun i : Fin m => (f i).val < b)) \
      (Finset.univ.filter (fun i : Fin m => (f i).val < a))).card ≤
      (Finset.Ico a b).card := by
    refine Finset.card_le_card_of_injOn (fun i => (f i).val) ?_ ?_
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_Ico] at hi ⊢
      omega
    · intro i _ j _ heq
      exact f.injective (Fin.ext heq)
  rw [Nat.card_Ico] at hle
  omega

/-- Complete classification of every pattern `π ≤ tau k` into valley patterns `P(x,y,z)`,
one-leader valley-free patterns `Q(p,q)`, and decreasing patterns `D(l)`. -/
theorem downset_tau_classify {k : ℕ} {π : Perm} (h : π ≤ tau k) :
    (∃ x y z : ℕ, x ≤ 2 * k + 1 ∧ y ≤ 2 * k + 1 ∧ z ≤ 2 * k ∧
      1 ≤ x + y ∧ π = patP x y z) ∨
    (∃ p q : ℕ, 1 ≤ p ∧
      ((p ≤ 2 * k + 1 ∧ q ≤ 4 * k + 1) ∨ (p ≤ 4 * k + 2 ∧ q ≤ 2 * k)) ∧
      π = patQ p q) ∨
    (∃ l : ℕ, l ≤ 6 * k + 2 ∧ π = patD l) := by
  rcases le_iff_contains.mp h with ⟨f, hf⟩
  have hthresh : ∀ (t : ℕ) (i : Fin π.len),
      (f i).val < t ↔
        i.val < (Finset.univ.filter (fun j : Fin π.len => (f j).val < t)).card := by
    intro t i
    have hdown : ∀ a b : Fin π.len, b < a →
        a ∈ Finset.univ.filter (fun j : Fin π.len => (f j).val < t) →
        b ∈ Finset.univ.filter (fun j : Fin π.len => (f j).val < t) := by
      intro a b hba ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨Finset.mem_univ _, Nat.lt_trans (f.strictMono hba) ha.2⟩
    simpa [Finset.mem_filter] using downward_closed_fin_iff _ hdown i
  set c₁ := (Finset.univ.filter (fun i : Fin π.len => (f i).val < 2)).card
  set c₂ := (Finset.univ.filter (fun i : Fin π.len => (f i).val < 2 * k + 3)).card
  set c₃ := (Finset.univ.filter (fun i : Fin π.len => (f i).val < 4 * k + 4)).card
  set c₄ := (Finset.univ.filter (fun i : Fin π.len => (f i).val < 6 * k + 4)).card
  have hc₁_iff := hthresh 2
  have hc₂_iff := hthresh (2 * k + 3)
  have hc₃_iff := hthresh (4 * k + 4)
  have hc₄_eq : c₄ = π.len := by
    have hall : Finset.univ.filter (fun i : Fin π.len => (f i).val < 6 * k + 4) = Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      have := (f i).isLt
      change (f i).val < (2 * k + 1) + (2 * k + 1) + 2 * k + 2 at this
      omega
    simp [c₄, hall]
  have hc1_le2 : c₁ ≤ 2 := by
    have := card_filter_lt_le f 0 2 (by omega)
    have h0 : (Finset.univ.filter (fun i : Fin π.len => (f i).val < 0)).card = 0 := by simp
    omega
  have hc1_le_c2 : c₁ ≤ c₂ := Finset.card_le_card (by
    intro i hi; rw [Finset.mem_filter] at hi ⊢; exact ⟨Finset.mem_univ _, by omega⟩)
  have hc2_le_c3 : c₂ ≤ c₃ := Finset.card_le_card (by
    intro i hi; rw [Finset.mem_filter] at hi ⊢; exact ⟨Finset.mem_univ _, by omega⟩)
  have hc3_le_len : c₃ ≤ π.len := by
    rw [← hc₄_eq]
    exact Finset.card_le_card (by
      intro i hi; rw [Finset.mem_filter] at hi ⊢; exact ⟨Finset.mem_univ _, by omega⟩)
  have hbandX : c₂ - c₁ ≤ 2 * k + 1 := by
    have := card_filter_lt_le f 2 (2 * k + 3) (by omega); omega
  have hbandY : c₃ - c₂ ≤ 2 * k + 1 := by
    have := card_filter_lt_le f (2 * k + 3) (4 * k + 4) (by omega); omega
  have hbandZ : π.len - c₃ ≤ 2 * k := by
    have := card_filter_lt_le f (4 * k + 4) (6 * k + 4) (by omega); omega
  have hf_lt : ∀ i : Fin π.len, (f i).val < (2 * k + 1) + (2 * k + 1) + 2 * k + 2 :=
    fun i => (f i).isLt
  -- Case split on `c₁ ∈ {0, 1, 2}`
  have hc1_cases : c₁ = 0 ∨ c₁ = 1 ∨ c₁ = 2 := by omega
  rcases hc1_cases with hc1 | hc1 | hc1
  · -- Case `c₁ = 0`: neither leader kept → strictly decreasing `patD π.len`
    right; right
    refine ⟨π.len, by omega, ?_⟩
    apply Perm.eq_of_lt_iff (σ := π) (τ := patD π.len) rfl
    intro i j
    rw [hf i j]
    have hfi : 2 ≤ (f i).val := by have := hc₁_iff i; omega
    have hfj : 2 ≤ (f j).val := by have := hc₁_iff j; omega
    change patPVal (2 * k + 1) (2 * k + 1) (2 * k) (f i).val <
      patPVal (2 * k + 1) (2 * k + 1) (2 * k) (f j).val ↔
      π.len - 1 - i.val < π.len - 1 - j.val
    rw [patPVal_lt_iff_tail (hf_lt i) (hf_lt j) hfi hfj]
    have hgt : j.val < i.val ↔ (f j).val < (f i).val := f.lt_iff_lt.symm
    have hi_lt : i.val < π.len := i.isLt
    have hj_lt : j.val < π.len := j.isLt
    omega
  · -- Case `c₁ = 1`: exactly one leader kept (`(f 0).val = 0` or `(f 0).val = 1`)
    have hlen_pos : 0 < π.len := by omega
    have hf0_lt2 : (f ⟨0, hlen_pos⟩).val < 2 :=
      (hc₁_iff ⟨0, hlen_pos⟩).mpr (by dsimp; omega)
    have hf0_cases : (f ⟨0, hlen_pos⟩).val = 0 ∨ (f ⟨0, hlen_pos⟩).val = 1 := by omega
    rcases hf0_cases with hf0 | hf0
    · -- Leader `a` kept (`f 0 = 0`, `1` not in range)
      set p := c₂ - 1
      set q := π.len - c₂
      have hlen_eq : π.len = (patQ p q).len := by dsimp [patQ]; omega
      have hno1 : ∀ i : Fin π.len, (f i).val ≠ 1 := by
        intro i
        by_cases hi0 : i.val = 0
        · have : i = ⟨0, hlen_pos⟩ := Fin.ext hi0; rw [this, hf0]; omega
        · have := hc₁_iff i; omega
      have hband : ∀ i : Fin π.len,
          patPNo1Band (2 * k + 1) (f i).val = patQBand p i.val := by
        intro i
        have hi0 : i.val = 0 → (f i).val = 0 := fun hi => by
          have : i = ⟨0, hlen_pos⟩ := Fin.ext hi; rw [this, hf0]
        have hi_lt2 := hc₁_iff i
        have hi_X := hc₂_iff i
        unfold patPNo1Band patQBand
        split_ifs <;> omega
      have hpi : π = patQ p q := by
        apply Perm.eq_of_lt_iff hlen_eq
        intro i j
        rw [hf i j]
        change patPVal (2 * k + 1) (2 * k + 1) (2 * k) (f i).val <
          patPVal (2 * k + 1) (2 * k + 1) (2 * k) (f j).val ↔
          patQVal p q i.val < patQVal p q j.val
        have hi_lt : i.val < p + q + 1 := by have := i.isLt; omega
        have hj_lt : j.val < p + q + 1 := by have := j.isLt; omega
        rw [patPVal_lt_iff_no1 (hf_lt i) (hf_lt j) (hno1 i) (hno1 j),
            patQVal_lt_iff hi_lt hj_lt, hband i, hband j]
        have hgt : (f j).val < (f i).val ↔ j.val < i.val := f.lt_iff_lt
        rw [hgt]
      by_cases hp0 : p = 0
      · right; right
        refine ⟨q + 1, by omega, ?_⟩
        rw [hpi, hp0, patQ_zero]
      · right; left
        exact ⟨p, q, by omega, Or.inl ⟨by omega, by omega⟩, hpi⟩
    · -- Leader `b` kept (`f 0 = 1`, `0` not in range)
      set p := c₃ - 1
      set q := π.len - c₃
      have hlen_eq : π.len = (patQ p q).len := by dsimp [patQ]; omega
      have hno0 : ∀ i : Fin π.len, (f i).val ≠ 0 := by
        intro i
        by_cases hi0 : i.val = 0
        · have : i = ⟨0, hlen_pos⟩ := Fin.ext hi0; rw [this, hf0]; omega
        · have := hc₁_iff i; omega
      have hband : ∀ i : Fin π.len,
          patPNo0Band (2 * k + 1) (2 * k + 1) (f i).val = patQBand p i.val := by
        intro i
        have hi0 : i.val = 0 → (f i).val = 1 := fun hi => by
          have : i = ⟨0, hlen_pos⟩ := Fin.ext hi; rw [this, hf0]
        have hi_lt2 := hc₁_iff i
        have hi_Y := hc₃_iff i
        unfold patPNo0Band patQBand
        split_ifs <;> omega
      have hpi : π = patQ p q := by
        apply Perm.eq_of_lt_iff hlen_eq
        intro i j
        rw [hf i j]
        change patPVal (2 * k + 1) (2 * k + 1) (2 * k) (f i).val <
          patPVal (2 * k + 1) (2 * k + 1) (2 * k) (f j).val ↔
          patQVal p q i.val < patQVal p q j.val
        have hi_lt : i.val < p + q + 1 := by have := i.isLt; omega
        have hj_lt : j.val < p + q + 1 := by have := j.isLt; omega
        rw [patPVal_lt_iff_no0 (hf_lt i) (hf_lt j) (hno0 i) (hno0 j),
            patQVal_lt_iff hi_lt hj_lt, hband i, hband j]
        have hgt : (f j).val < (f i).val ↔ j.val < i.val := f.lt_iff_lt
        rw [hgt]
      by_cases hp0 : p = 0
      · right; right
        refine ⟨q + 1, by omega, ?_⟩
        rw [hpi, hp0, patQ_zero]
      · right; left
        exact ⟨p, q, by omega, Or.inr ⟨by omega, by omega⟩, hpi⟩
  · -- Case `c₁ = 2`: both leaders kept (`f 0 = 0`, `f 1 = 1`)
    have hlen_ge2 : 2 ≤ π.len := by omega
    have hf0_lt2 : (f ⟨0, by omega⟩).val < 2 :=
      (hc₁_iff ⟨0, by omega⟩).mpr (by dsimp; omega)
    have hf1_lt2 : (f ⟨1, by omega⟩).val < 2 :=
      (hc₁_iff ⟨1, by omega⟩).mpr (by dsimp; omega)
    have hf01 : (f ⟨0, by omega⟩).val < (f ⟨1, by omega⟩).val :=
      f.strictMono (show (⟨0, by omega⟩ : Fin π.len) < ⟨1, by omega⟩ from Nat.zero_lt_one)
    have hf0 : (f ⟨0, by omega⟩).val = 0 := by omega
    have hf1 : (f ⟨1, by omega⟩).val = 1 := by omega
    set x := c₂ - 2
    set y := c₃ - c₂
    set z := π.len - c₃
    have hlen_eq : π.len = (patP x y z).len := by dsimp [patP]; omega
    have hband : ∀ i : Fin π.len,
        patPBand (2 * k + 1) (2 * k + 1) (f i).val = patPBand x y i.val := by
      intro i
      have hi0 : i.val = 0 → (f i).val = 0 := fun hi => by
        have : i = ⟨0, by omega⟩ := Fin.ext hi; rw [this, hf0]
      have hi1 : i.val = 1 → (f i).val = 1 := fun hi => by
        have : i = ⟨1, by omega⟩ := Fin.ext hi; rw [this, hf1]
      have hi_lt2 := hc₁_iff i
      have hi_X := hc₂_iff i
      have hi_Y := hc₃_iff i
      unfold patPBand
      split_ifs <;> omega
    have hpi : π = patP x y z := by
      apply Perm.eq_of_lt_iff hlen_eq
      intro i j
      rw [hf i j]
      change patPVal (2 * k + 1) (2 * k + 1) (2 * k) (f i).val <
        patPVal (2 * k + 1) (2 * k + 1) (2 * k) (f j).val ↔
        patPVal x y z i.val < patPVal x y z j.val
      have hi_lt : i.val < x + y + z + 2 := by have := i.isLt; omega
      have hj_lt : j.val < x + y + z + 2 := by have := j.isLt; omega
      rw [patPVal_lt_iff (hf_lt i) (hf_lt j), patPVal_lt_iff hi_lt hj_lt, hband i, hband j]
      have hgt : (f j).val < (f i).val ↔ j.val < i.val := f.lt_iff_lt
      rw [hgt]
    by_cases hxy : 1 ≤ x + y
    · left
      exact ⟨x, y, z, by omega, by omega, by omega, hxy, hpi⟩
    · right; right
      have hx0 : x = 0 := by omega
      have hy0 : y = 0 := by omega
      refine ⟨z + 2, by omega, ?_⟩
      rw [hpi, hx0, hy0, patP_zero_zero]

/-! ### Exact Width of `Downset (tau k)`: Antichain + Matching Chain Cover -/

/-- The explicit antichain of size `3k^2 + 9k + 5` inside `Downset (tau k)`:
the `3k^2 + 5k + 2` middle-slice valley patterns of length `3k + 3`, together with
all `4k + 3` valley-free patterns of length `4k + 3`. -/
def familyAntichain (k : ℕ) : Finset Perm :=
  (boxSlice k (3 * k + 1)).image (fun t => patP t.1 t.2.1 t.2.2) ∪
  (insert (patD (4 * k + 3))
    ((Finset.Icc 1 (4 * k + 2)).image (fun p => patQ p (4 * k + 2 - p))))

theorem familyAntichain_subset (k : ℕ) (hk : 1 ≤ k) :
    familyAntichain k ⊆ Downset (tau k) := by
  intro π hπ
  rw [mem_downset_iff]
  unfold familyAntichain at hπ
  rcases Finset.mem_union.mp hπ with hval | hvf
  · rcases Finset.mem_image.mp hval with ⟨t, ht, rfl⟩
    rw [mem_boxSlice] at ht
    exact patP_le_tau ht.1 ht.2.1 ht.2.2.1
  · rcases Finset.mem_insert.mp hvf with rfl | hq
    · exact patD_le_tau (by omega)
    · rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
      rw [Finset.mem_Icc] at hp
      by_cases hple : p ≤ 2 * k + 1
      · exact patQ_le_tau (Or.inl ⟨hple, by omega⟩)
      · exact patQ_le_tau (Or.inr ⟨hp.2, by omega⟩)

theorem familyAntichain_isAntichain (k : ℕ) (hk : 1 ≤ k) :
    IsAntichain (familyAntichain k) := by
  intro x hx y hy hxy
  unfold familyAntichain at hx hy
  rcases Finset.mem_union.mp hx with hxV | hxVF <;>
  rcases Finset.mem_union.mp hy with hyV | hyVF
  · -- both valley patterns of length `3k + 3`
    rcases Finset.mem_image.mp hxV with ⟨tx, htx, rfl⟩
    rcases Finset.mem_image.mp hyV with ⟨ty, hty, rfl⟩
    rw [mem_boxSlice] at htx hty
    exact eq_of_le_of_len_eq hxy (by dsimp [patP]; omega)
  · -- valley pattern ≤ valley-free pattern: impossible by `hasValley_mono`
    exfalso
    rcases Finset.mem_image.mp hxV with ⟨tx, htx, rfl⟩
    rw [mem_boxSlice] at htx
    have hval : HasValley (patP tx.1 tx.2.1 tx.2.2) := patP_hasValley (by omega)
    have hval_y : HasValley y := hasValley_mono hval hxy
    rcases Finset.mem_insert.mp hyVF with rfl | hq
    · exact patD_not_hasValley _ hval_y
    · rcases Finset.mem_image.mp hq with ⟨p, _, rfl⟩
      exact patQ_not_hasValley _ _ hval_y
  · -- valley-free of length `4k + 3` ≤ valley of length `3k + 3`: impossible by length
    exfalso
    rcases Finset.mem_image.mp hyV with ⟨ty, hty, rfl⟩
    rw [mem_boxSlice] at hty
    have hlen_le := le_len_le hxy
    have hlen_x : x.len = 4 * k + 3 := by
      rcases Finset.mem_insert.mp hxVF with rfl | hq
      · rfl
      · rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
        rw [Finset.mem_Icc] at hp
        dsimp [patQ]; omega
    have hlen_y : (patP ty.1 ty.2.1 ty.2.2).len = 3 * k + 3 := by dsimp [patP]; omega
    omega
  · -- both valley-free of length `4k + 3`
    have hlen_x : x.len = 4 * k + 3 := by
      rcases Finset.mem_insert.mp hxVF with rfl | hq
      · rfl
      · rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
        rw [Finset.mem_Icc] at hp
        dsimp [patQ]; omega
    have hlen_y : y.len = 4 * k + 3 := by
      rcases Finset.mem_insert.mp hyVF with rfl | hq
      · rfl
      · rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
        rw [Finset.mem_Icc] at hp
        dsimp [patQ]; omega
    exact eq_of_le_of_len_eq hxy (hlen_x.trans hlen_y.symm)

theorem familyAntichain_card (k : ℕ) (_hk : 1 ≤ k) :
    (familyAntichain k).card = 3 * k ^ 2 + 9 * k + 5 := by
  unfold familyAntichain
  have hdisj : Disjoint
      ((boxSlice k (3 * k + 1)).image (fun t => patP t.1 t.2.1 t.2.2))
      (insert (patD (4 * k + 3))
        ((Finset.Icc 1 (4 * k + 2)).image (fun p => patQ p (4 * k + 2 - p)))) := by
    rw [Finset.disjoint_left]
    intro x hxV hxVF
    rcases Finset.mem_image.mp hxV with ⟨t, ht, rfl⟩
    rw [mem_boxSlice] at ht
    rcases Finset.mem_insert.mp hxVF with heq | hq
    · exact patP_ne_patD (by omega) heq
    · rcases Finset.mem_image.mp hq with ⟨p, _, heq⟩
      exact patP_ne_patQ (by omega) heq.symm
  rw [Finset.card_union_of_disjoint hdisj]
  have hcard1 : ((boxSlice k (3 * k + 1)).image (fun t => patP t.1 t.2.1 t.2.2)).card =
      3 * k ^ 2 + 5 * k + 2 := by
    rw [Finset.card_image_of_injective _ (fun a b h => by
      have := patP_injective h
      rcases a with ⟨x₁, y₁, z₁⟩; rcases b with ⟨x₂, y₂, z₂⟩
      simp only at this
      exact Prod.ext this.1 (Prod.ext this.2.1 this.2.2)), boxSlice_mid_card]
  have hnotmem : patD (4 * k + 3) ∉
      (Finset.Icc 1 (4 * k + 2)).image (fun p => patQ p (4 * k + 2 - p)) := by
    intro hm
    rcases Finset.mem_image.mp hm with ⟨p, hp, heq⟩
    rw [Finset.mem_Icc] at hp
    exact patQ_ne_patD hp.1 heq
  rw [Finset.card_insert_of_notMem hnotmem]
  have hcard2 : ((Finset.Icc 1 (4 * k + 2)).image (fun p => patQ p (4 * k + 2 - p))).card =
      4 * k + 2 := by
    rw [Finset.card_image_of_injOn (fun p₁ _ p₂ _ h => (patQ_injective h).1)]
    simp [Nat.card_Icc]
  rw [hcard1, hcard2]
  omega

/-- Index type for the matching cover of `Downset (tau k)` by `3k^2 + 9k + 5` chains. -/
inductive ChainIdx where
  /-- Symmetric chain in `Box(k)` identified by `(d₁, d₂)`. -/
  | box (id : ℕ × ℕ)
  /-- Chain of strictly decreasing patterns `D(l)`. -/
  | dec
  /-- Chain of one-leader patterns `Q(p, q)` with fixed `p`. -/
  | qFixedP (p : ℕ)
  /-- Chain of one-leader patterns `Q(p, q)` with fixed `q`. -/
  | qFixedQ (q : ℕ)
  deriving DecidableEq

/-- The `3k^2 + 9k + 5` chain indices covering `Downset (tau k)`. -/
def familyChainIndices (k : ℕ) : Finset ChainIdx :=
  ((boxFinset k).image (boxId k)).image ChainIdx.box ∪
  (insert ChainIdx.dec
    (((Finset.Icc 1 (2 * k + 1)).image ChainIdx.qFixedP) ∪
     ((Finset.range (2 * k + 1)).image ChainIdx.qFixedQ)))

/-- The chain of permutations corresponding to each `ChainIdx`. -/
def familyChain (k : ℕ) : ChainIdx → Finset Perm
  | ChainIdx.box id =>
      ((boxFinset k).filter (fun t => boxId k t = id)).image (fun t => patP t.1 t.2.1 t.2.2)
  | ChainIdx.dec =>
      (Finset.range (6 * k + 3)).image patD
  | ChainIdx.qFixedP p =>
      (Finset.range (4 * k + 2)).image (fun q => patQ p q)
  | ChainIdx.qFixedQ q =>
      (Finset.Icc (2 * k + 2) (4 * k + 2)).image (fun p => patQ p q)

theorem familyChain_isChain (k : ℕ) (idx : ChainIdx) : IsChain (familyChain k idx) := by
  cases idx with
  | box id =>
    intro x hx y hy
    rcases Finset.mem_image.mp hx with ⟨tx, htx, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨ty, hty, rfl⟩
    rw [Finset.mem_filter] at htx hty
    rcases box_chain_comparable htx.1 hty.1 (htx.2.trans hty.2.symm) with hle | hle
    · exact Or.inl (patP_le_patP hle.1 hle.2.1 hle.2.2)
    · exact Or.inr (patP_le_patP hle.1 hle.2.1 hle.2.2)
  | dec =>
    intro x hx y hy
    rcases Finset.mem_image.mp hx with ⟨lx, _, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨ly, _, rfl⟩
    rcases le_total lx ly with hle | hle
    · exact Or.inl (patD_le_patD hle)
    · exact Or.inr (patD_le_patD hle)
  | qFixedP p =>
    intro x hx y hy
    rcases Finset.mem_image.mp hx with ⟨qx, _, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨qy, _, rfl⟩
    rcases le_total qx qy with hle | hle
    · exact Or.inl (patQ_le_patQ (le_refl p) hle)
    · exact Or.inr (patQ_le_patQ (le_refl p) hle)
  | qFixedQ q =>
    intro x hx y hy
    rcases Finset.mem_image.mp hx with ⟨px, _, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨py, _, rfl⟩
    rcases le_total px py with hle | hle
    · exact Or.inl (patQ_le_patQ hle (le_refl q))
    · exact Or.inr (patQ_le_patQ hle (le_refl q))

theorem familyChain_covers (k : ℕ) :
    ∀ π ∈ Downset (tau k), ∃ idx ∈ familyChainIndices k, π ∈ familyChain k idx := by
  intro π hπ
  rw [mem_downset_iff] at hπ
  rcases downset_tau_classify hπ with
    ⟨x, y, z, hx, hy, hz, _, rfl⟩ | ⟨p, q, hp1, hbounds, rfl⟩ | ⟨l, hl, rfl⟩
  · have ht : (x, y, z) ∈ boxFinset k := mem_boxFinset.mpr ⟨hx, hy, hz⟩
    refine ⟨ChainIdx.box (boxId k (x, y, z)), ?_, ?_⟩
    · unfold familyChainIndices
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ ht))
    · exact Finset.mem_image.mpr ⟨(x, y, z), Finset.mem_filter.mpr ⟨ht, rfl⟩, rfl⟩
  · by_cases hple : p ≤ 2 * k + 1
    · have hq : q ≤ 4 * k + 1 := by rcases hbounds with ⟨_, hq⟩ | ⟨_, hq⟩ <;> omega
      refine ⟨ChainIdx.qFixedP p, ?_, ?_⟩
      · unfold familyChainIndices
        refine Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_))
        exact Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨hp1, hple⟩)
      · exact Finset.mem_image.mpr ⟨q, Finset.mem_range.mpr (by omega), rfl⟩
    · have hpq : p ≤ 4 * k + 2 ∧ q ≤ 2 * k := by
        rcases hbounds with ⟨hp, _⟩ | h2
        · omega
        · exact h2
      refine ⟨ChainIdx.qFixedQ q, ?_, ?_⟩
      · unfold familyChainIndices
        refine Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_))
        exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))
      · exact Finset.mem_image.mpr ⟨p, Finset.mem_Icc.mpr ⟨by omega, hpq.1⟩, rfl⟩
  · refine ⟨ChainIdx.dec, ?_, ?_⟩
    · unfold familyChainIndices
      exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    · exact Finset.mem_image.mpr ⟨l, Finset.mem_range.mpr (by omega), rfl⟩

theorem familyChainIndices_card (k : ℕ) :
    (familyChainIndices k).card = 3 * k ^ 2 + 9 * k + 5 := by
  unfold familyChainIndices
  have hd1 : Disjoint
      (((boxFinset k).image (boxId k)).image ChainIdx.box)
      (insert ChainIdx.dec
        (((Finset.Icc 1 (2 * k + 1)).image ChainIdx.qFixedP) ∪
         ((Finset.range (2 * k + 1)).image ChainIdx.qFixedQ))) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨_, _, rfl⟩
    rcases Finset.mem_insert.mp hx2 with h | hx3
    · exact ChainIdx.noConfusion h
    · rcases Finset.mem_union.mp hx3 with hp | hq
      · rcases Finset.mem_image.mp hp with ⟨_, _, h⟩; exact ChainIdx.noConfusion h
      · rcases Finset.mem_image.mp hq with ⟨_, _, h⟩; exact ChainIdx.noConfusion h
  have hndec : ChainIdx.dec ∉
      (((Finset.Icc 1 (2 * k + 1)).image ChainIdx.qFixedP) ∪
       ((Finset.range (2 * k + 1)).image ChainIdx.qFixedQ)) := by
    intro hm
    rcases Finset.mem_union.mp hm with hp | hq
    · rcases Finset.mem_image.mp hp with ⟨_, _, h⟩; exact ChainIdx.noConfusion h
    · rcases Finset.mem_image.mp hq with ⟨_, _, h⟩; exact ChainIdx.noConfusion h
  have hd2 : Disjoint
      ((Finset.Icc 1 (2 * k + 1)).image ChainIdx.qFixedP)
      ((Finset.range (2 * k + 1)).image ChainIdx.qFixedQ) := by
    rw [Finset.disjoint_left]
    intro x hp hq
    rcases Finset.mem_image.mp hp with ⟨_, _, rfl⟩
    rcases Finset.mem_image.mp hq with ⟨_, _, h⟩
    exact ChainIdx.noConfusion h
  rw [Finset.card_union_of_disjoint hd1, Finset.card_insert_of_notMem hndec,
      Finset.card_union_of_disjoint hd2]
  rw [Finset.card_image_of_injective _ (fun _ _ h => ChainIdx.box.inj h), boxId_image_card_eq]
  rw [Finset.card_image_of_injective _ (fun _ _ h => ChainIdx.qFixedP.inj h)]
  rw [Finset.card_image_of_injective _ (fun _ _ h => ChainIdx.qFixedQ.inj h)]
  simp [Nat.card_Icc]
  omega

/-- Exact width of `Downset (tau k)`: `3k^2 + 9k + 5` for all `k ≥ 1`. -/
theorem family_width (k : ℕ) (hk : 1 ≤ k) :
    width (Downset (tau k)) = 3 * k ^ 2 + 9 * k + 5 := by
  apply le_antisymm
  · calc
      width (Downset (tau k)) ≤ (familyChainIndices k).card :=
        width_le_of_indexed_chain_cover (fun idx _ => familyChain_isChain k idx)
          (familyChain_covers k)
      _ = 3 * k ^ 2 + 9 * k + 5 := familyChainIndices_card k
  · calc
      3 * k ^ 2 + 9 * k + 5 = (familyAntichain k).card := (familyAntichain_card k hk).symm
      _ ≤ width (Downset (tau k)) :=
        card_le_width_of_antichain (familyAntichain_subset k hk)
          (familyAntichain_isAntichain k hk)

/-! ### Exact Largest Rank of `Downset (tau k)`: `3k^2 + 8k + 5` -/

/-- Upper bound on every rank level of `Downset (tau k)`: at most `3k^2 + 8k + 5`. -/
theorem family_rankLevel_card_le (k : ℕ) (hk : 1 ≤ k) (l : ℕ) :
    (RankLevel (Downset (tau k)) l).card ≤ 3 * k ^ 2 + 8 * k + 5 := by
  by_cases hl0 : l = 0
  · subst hl0
    have hsub : RankLevel (Downset (tau k)) 0 ⊆ {patD 0} := by
      intro π hπ
      rw [RankLevel, Finset.mem_filter, mem_downset_iff] at hπ
      rw [Finset.mem_singleton]
      apply Perm.ext_val hπ.2
      intro i
      exact absurd i.isLt (by omega)
    calc
      (RankLevel (Downset (tau k)) 0).card ≤ ({patD 0} : Finset Perm).card :=
        Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
      _ ≤ 3 * k ^ 2 + 8 * k + 5 := by omega
  · by_cases hl1 : l = 1
    · subst hl1
      have hsub : RankLevel (Downset (tau k)) 1 ⊆ {patD 1} := by
        intro π hπ
        rw [RankLevel, Finset.mem_filter, mem_downset_iff] at hπ
        rw [Finset.mem_singleton]
        apply Perm.ext_val hπ.2
        intro i
        have hi0 : i.val = 0 := by omega
        have hpi0 : (π.perm i).val = 0 := by have := (π.perm i).isLt; omega
        change (π.perm i).val = 1 - 1 - i.val
        omega
      calc
        (RankLevel (Downset (tau k)) 1).card ≤ ({patD 1} : Finset Perm).card :=
          Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton _
        _ ≤ 3 * k ^ 2 + 8 * k + 5 := by omega
    · -- General case `l ≥ 2`
      have hl2 : 2 ≤ l := by omega
      let V : Finset Perm := (boxSlice k (l - 2)).image (fun t => patP t.1 t.2.1 t.2.2)
      let Q : Finset Perm :=
        (Finset.Icc 1 (min (l - 1) (4 * k + 2))).image (fun p => patQ p (l - 1 - p))
      let VF : Finset Perm := insert (patD l) Q
      have hsub : RankLevel (Downset (tau k)) l ⊆ V ∪ VF := by
        intro π hπ
        rw [RankLevel, Finset.mem_filter, mem_downset_iff] at hπ
        rcases hπ with ⟨hle, hlen⟩
        rcases downset_tau_classify hle with
          ⟨x, y, z, hx, hy, hz, _, rfl⟩ | ⟨p, q, hp1, hbounds, rfl⟩ | ⟨l', _, rfl⟩
        · apply Finset.mem_union_left
          refine Finset.mem_image.mpr ⟨(x, y, z), ?_, rfl⟩
          rw [mem_boxSlice]
          change x + y + z + 2 = l at hlen
          dsimp
          exact ⟨hx, hy, hz, by omega⟩
        · apply Finset.mem_union_right
          apply Finset.mem_insert_of_mem
          refine Finset.mem_image.mpr ⟨p, ?_, ?_⟩
          · rw [Finset.mem_Icc]
            change p + q + 1 = l at hlen
            have hpmax : p ≤ 4 * k + 2 := by
              rcases hbounds with ⟨hp, _⟩ | ⟨hp, _⟩ <;> omega
            omega
          · change p + q + 1 = l at hlen
            have hq : l - 1 - p = q := by omega
            rw [hq]
        · apply Finset.mem_union_right
          change l' = l at hlen
          rw [hlen]
          exact Finset.mem_insert_self _ _
      have hcard_V : V.card ≤ (boxSlice k (l - 2)).card := Finset.card_image_le
      have hcard_VF : VF.card ≤ min l (4 * k + 3) := by
        calc
          VF.card ≤ Q.card + 1 := Finset.card_insert_le _ _
          _ ≤ (Finset.Icc 1 (min (l - 1) (4 * k + 2))).card + 1 :=
            Nat.add_le_add_right Finset.card_image_le 1
          _ = min l (4 * k + 3) := by simp [Nat.card_Icc]; omega
      have htotal : (RankLevel (Downset (tau k)) l).card ≤
          (boxSlice k (l - 2)).card + min l (4 * k + 3) := by
        calc
          (RankLevel (Downset (tau k)) l).card ≤ (V ∪ VF).card := Finset.card_le_card hsub
          _ ≤ V.card + VF.card := Finset.card_union_le _ _
          _ ≤ (boxSlice k (l - 2)).card + min l (4 * k + 3) :=
            Nat.add_le_add hcard_V hcard_VF
      -- Three-case bound on `B(l - 2) + min(l, 4k + 3)`
      by_cases hc1 : l ≤ 3 * k + 3
      · have hB : (boxSlice k (l - 2)).card ≤ 3 * k ^ 2 + 5 * k + 2 := by
          rw [← boxSlice_mid_card k]
          exact boxSlice_card_le_mid k (l - 2)
        omega
      · by_cases hc2 : l ≤ 4 * k + 3
        · set t := l - (3 * k + 3)
          have ht1 : 1 ≤ t := by omega
          have htk : t ≤ k := by omega
          have hl_eq : l - 2 = 3 * k + 1 + t := by omega
          have hB : (boxSlice k (l - 2)).card = 3 * k ^ 2 + 5 * k + 2 - t ^ 2 := by
            rw [hl_eq]
            exact boxSlice_card k t htk
          have ht_le_sq : t ≤ t ^ 2 := by nlinarith
          have hsq_le : t ^ 2 ≤ 3 * k ^ 2 + 5 * k + 2 := by nlinarith
          omega
        · -- `l > 4k + 3`, so `l - 2 ≥ 4k + 2 ≥ 4k + 1`
          have hB1 : (boxSlice k (l - 2)).card ≤ (boxSlice k (4 * k + 1)).card :=
            boxSlice_card_antitone (by omega) (by omega)
          have hB2 : (boxSlice k (4 * k + 1)).card = 3 * k ^ 2 + 5 * k + 2 - k ^ 2 := by
            have : 4 * k + 1 = 3 * k + 1 + k := by omega
            rw [this]
            exact boxSlice_card k k (le_refl k)
          have hk_le_sq : k ≤ k ^ 2 := by nlinarith
          have hsq_le : k ^ 2 ≤ 3 * k ^ 2 + 5 * k + 2 := by nlinarith
          omega

/-- Exact size of rank `3k + 3` in `Downset (tau k)`: `3k^2 + 8k + 5`. -/
theorem family_rankLevel_mid_card (k : ℕ) (hk : 1 ≤ k) :
    (RankLevel (Downset (tau k)) (3 * k + 3)).card = 3 * k ^ 2 + 8 * k + 5 := by
  apply le_antisymm (family_rankLevel_card_le k hk (3 * k + 3))
  let M : Finset Perm :=
    (boxSlice k (3 * k + 1)).image (fun t => patP t.1 t.2.1 t.2.2) ∪
    (insert (patD (3 * k + 3))
      ((Finset.Icc 1 (3 * k + 2)).image (fun p => patQ p (3 * k + 2 - p))))
  have hsub : M ⊆ RankLevel (Downset (tau k)) (3 * k + 3) := by
    intro π hπ
    rw [RankLevel, Finset.mem_filter, mem_downset_iff]
    rcases Finset.mem_union.mp hπ with hval | hvf
    · rcases Finset.mem_image.mp hval with ⟨t, ht, rfl⟩
      rw [mem_boxSlice] at ht
      refine ⟨patP_le_tau ht.1 ht.2.1 ht.2.2.1, ?_⟩
      change t.1 + t.2.1 + t.2.2 + 2 = 3 * k + 3
      omega
    · rcases Finset.mem_insert.mp hvf with rfl | hq
      · exact ⟨patD_le_tau (by omega), rfl⟩
      · rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
        rw [Finset.mem_Icc] at hp
        constructor
        · by_cases hple : p ≤ 2 * k + 1
          · exact patQ_le_tau (Or.inl ⟨hple, by omega⟩)
          · exact patQ_le_tau (Or.inr ⟨by omega, by omega⟩)
        · dsimp [patQ]; omega
  have hcard : M.card = 3 * k ^ 2 + 8 * k + 5 := by
    dsimp only [M]
    have hdisj : Disjoint
        ((boxSlice k (3 * k + 1)).image (fun t => patP t.1 t.2.1 t.2.2))
        (insert (patD (3 * k + 3))
          ((Finset.Icc 1 (3 * k + 2)).image (fun p => patQ p (3 * k + 2 - p)))) := by
      rw [Finset.disjoint_left]
      intro x hxV hxVF
      rcases Finset.mem_image.mp hxV with ⟨t, ht, rfl⟩
      rw [mem_boxSlice] at ht
      rcases Finset.mem_insert.mp hxVF with heq | hq
      · exact patP_ne_patD (by omega) heq
      · rcases Finset.mem_image.mp hq with ⟨p, _, heq⟩
        exact patP_ne_patQ (by omega) heq.symm
    rw [Finset.card_union_of_disjoint hdisj]
    have hcard1 : ((boxSlice k (3 * k + 1)).image (fun t => patP t.1 t.2.1 t.2.2)).card =
        3 * k ^ 2 + 5 * k + 2 := by
      rw [Finset.card_image_of_injective _ (fun a b h => by
        have := patP_injective h
        rcases a with ⟨x₁, y₁, z₁⟩; rcases b with ⟨x₂, y₂, z₂⟩
        simp only at this
        exact Prod.ext this.1 (Prod.ext this.2.1 this.2.2)), boxSlice_mid_card]
    have hnotmem : patD (3 * k + 3) ∉
        (Finset.Icc 1 (3 * k + 2)).image (fun p => patQ p (3 * k + 2 - p)) := by
      intro hm
      rcases Finset.mem_image.mp hm with ⟨p, hp, heq⟩
      rw [Finset.mem_Icc] at hp
      exact patQ_ne_patD hp.1 heq
    rw [Finset.card_insert_of_notMem hnotmem]
    have hcard2 : ((Finset.Icc 1 (3 * k + 2)).image (fun p => patQ p (3 * k + 2 - p))).card =
        3 * k + 2 := by
      rw [Finset.card_image_of_injOn (fun p₁ _ p₂ _ h => (patQ_injective h).1)]
      simp [Nat.card_Icc]
    rw [hcard1, hcard2]
    omega
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- Exact largest rank of `Downset (tau k)`: `3k^2 + 8k + 5` for all `k ≥ 1`. -/
theorem family_largestRank (k : ℕ) (hk : 1 ≤ k) :
    largestRank (Downset (tau k)) = 3 * k ^ 2 + 8 * k + 5 :=
  largestRank_eq_of_bounds (family_rankLevel_card_le k hk)
    (le_of_eq (family_rankLevel_mid_card k hk).symm)

/-- **Main Theorem (Exact Sperner Deficiency `k`)**: For every `k ≥ 1`, the principal downset
`Downset (tau k)` of the permutation `tau k` of length `6k + 4` has exact Sperner deficiency `k`:
`width (Downset (tau k)) = largestRank (Downset (tau k)) + k`. -/
theorem family_exact_deficiency (k : ℕ) (hk : 1 ≤ k) :
    width (Downset (tau k)) = largestRank (Downset (tau k)) + k := by
  rw [family_width k hk, family_largestRank k hk]
  omega

/-- Every member of the infinite family `tau k` (`k ≥ 1`) has a non-Sperner principal downset. -/
theorem family_not_sperner (k : ℕ) (hk : 1 ≤ k) :
    ¬ IsSperner (Downset (tau k)) := by
  unfold IsSperner
  rw [family_exact_deficiency k hk]
  omega

end PatternPoset
