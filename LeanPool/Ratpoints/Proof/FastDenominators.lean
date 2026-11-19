/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import LeanPool.Ratpoints.Fast.Sieve

import LeanPool.Ratpoints.Proof.Containers

/-!
# The marks of the denominators of the fast search

The fast search finds its denominators by marks in byte arrays (`Ratpoints.Fast.denominators`), and
`Ratpoints.Fast.collectMarked` lists the marked ones in ascending order
(`Ratpoints.Fast.collectMarked_eq_filter`). For even degree, `Ratpoints.Fast.forbiddenDens` marks
only multiples of an odd `q` with `J(c_d | q) = -1`
(`Ratpoints.Fast.exists_dvd_of_getElem!_forbiddenDens_ne_zero`): it marks the multiples of `p`
when `Ratpoints.Fast.jacobiNat` gives `-1`, which it gives only for `J(c_d | p) = -1`
(`Ratpoints.Fast.jacobiNatAux_eq_zero_or_eq`, `Ratpoints.Fast.jacobiNat_eq_zero_or_eq`); that `p`
is a prime, as the sieve of Eratosthenes makes it, is not needed. For odd degree,
`Ratpoints.Fast.squareDens n hi` marks every `s k ^ 2 ≤ hi` with `s` dividing `n ≠ 0` and `k ≥ 1`
(`Ratpoints.Fast.getElem!_squareDens`).

## Main statements

* `Ratpoints.Fast.collectMarked_eq_filter`: the marked numbers in ascending order.
* `Ratpoints.Fast.exists_dvd_of_getElem!_forbiddenDens_ne_zero`: what a mark of
  `Ratpoints.Fast.forbiddenDens` means.
* `Ratpoints.Fast.getElem!_squareDens`: the marks of `Ratpoints.Fast.squareDens`.
-/

@[expose] public section

open scoped NumberTheorySymbols

namespace Ratpoints.Fast

/-! ### Marked numbers -/

theorem collectMarked_eq_filter (m : ByteArray) (v : UInt8) {lo : ℕ} (hlo : 1 ≤ lo) (n : ℕ)
    (acc : List ℕ) :
    collectMarked m v lo n acc = (List.range' lo (n + 1 - lo)).filter (m[·]! == v) ++ acc := by
  induction n generalizing acc with
  | zero => simp [collectMarked, show 1 - lo = 0 by lia]
  | succ n ih =>
    rw [collectMarked]
    by_cases h : n + 1 < lo
    · simp [h, show n + 1 + 1 - lo = 0 by lia]
    · simp only [h, ↓reduceIte]
      rw [ih, show n + 1 + 1 - lo = n + 1 - lo + 1 by lia,
        List.range'_concat, List.filter_append, List.append_assoc,
        show lo + 1 * (n + 1 - lo) = n + 1 by lia]
      cases hm : m[n + 1]! == v <;> simp [hm]

theorem collectMarked_sublist (m : ByteArray) (v : UInt8) {lo : ℕ} (hlo : 1 ≤ lo) (n : ℕ) :
    (collectMarked m v lo n []).Sublist (List.range' lo (n + 1 - lo)) := by
  rw [collectMarked_eq_filter m v hlo, List.append_nil]
  exact List.filter_sublist

theorem mem_collectMarked_iff {m : ByteArray} {v : UInt8} {lo : ℕ} (hlo : 1 ≤ lo) {n b : ℕ} :
    b ∈ collectMarked m v lo n [] ↔ b ∈ List.range' lo (n + 1 - lo) ∧ m[b]! = v := by
  simp [collectMarked_eq_filter m v hlo]

theorem of_getElem!_markMultiples {a : ByteArray} {n j hi b : ℕ}
    (h : (markMultiples a n j hi)[b]! ≠ 0) : a[b]! ≠ 0 ∨ ∃ k, b = j + n * k := by
  fun_induction markMultiples a n j hi with
  | case1 _ j _ ih =>
    rcases ih h with h' | ⟨k, rfl⟩
    · by_cases hjb : j = b
      · exact .inr ⟨0, by lia⟩
      · exact .inl (by rwa [ByteArray.getElem!_set!_ne _ _ _ _ hjb] at h')
    · exact .inr ⟨k + 1, by ring⟩
  | case2 => exact .inl h

/-! ### The Jacobi symbol -/

/-- Halving an even `a` against an odd `n` multiplies the symbol by `(2 / n)`. -/
theorem ite_mul_jacobiSym_div_two {a n : ℕ} (ha : a % 2 = 0) (hn : n % 2 = 1) (s : ℤ) :
    (if (n % 8 == 3 || n % 8 == 5) = true then -s else s) * J((a / 2 : ℕ) | n) = s * J(a | n) := by
  rw [← jacobiSym.even_odd (a := a) (by lia) hn, Int.natCast_div, Nat.cast_ofNat]
  simp only [Bool.or_eq_true, beq_iff_eq]
  split_ifs <;> ring

/-- Exchanging the odd `a` and `n`, with `n` reduced modulo `a`, multiplies the symbol by the sign
of the reciprocity. -/
theorem ite_mul_jacobiSym_mod {a n : ℕ} (ha : a % 2 = 1) (hn : n % 2 = 1) (s : ℤ) :
    (if (a % 4 == 3 && n % 4 == 3) = true then -s else s) * J((n % a : ℕ) | a) = s * J(a | n) := by
  rw [← jacobiSym.quadratic_reciprocity_if ha hn, Int.natCast_mod, ← jacobiSym.mod_left]
  simp only [Bool.and_eq_true, beq_iff_eq]
  split_ifs <;> ring

/-- `Ratpoints.Fast.jacobiNatAux` computes `s J(a | n)` for odd `n`, or gives up with `0`. -/
theorem jacobiNatAux_eq_zero_or_eq (fuel a : ℕ) {n : ℕ} (hn : n % 2 = 1) (s : ℤ) :
    jacobiNatAux fuel a n s = 0 ∨ jacobiNatAux fuel a n s = s * J(a | n) := by
  induction fuel generalizing a n s with
  | zero => exact .inl rfl
  | succ fuel ih =>
    rw [jacobiNatAux]
    rcases eq_or_ne a 0 with rfl | h0
    · by_cases h1 : n = 1 <;> simp [h1]
    by_cases h2 : a % 2 = 0
    · simp only [beq_iff_eq, h0, h2, ↓reduceIte]
      exact (ih _ hn _).imp_right (·.trans (ite_mul_jacobiSym_div_two h2 hn s))
    · simp only [beq_iff_eq, h0, h2, ↓reduceIte]
      exact (ih _ (by lia) _).imp_right (·.trans (ite_mul_jacobiSym_mod (by lia) hn s))

theorem jacobiNat_eq_zero_or_eq (a : ℕ) {n : ℕ} (hn : n % 2 = 1) :
    jacobiNat a n = 0 ∨ jacobiNat a n = J(a | n) := by
  have := jacobiNatAux_eq_zero_or_eq 256 (a % n) hn 1
  rwa [one_mul, Int.natCast_mod, ← jacobiSym.mod_left] at this

theorem jacobiSym_eq_neg_one_of_jacobiNat_eq_neg_one {a n : ℕ} (hn : n % 2 = 1)
    (h : jacobiNat a n = -1) : J(a | n) = -1 :=
  (jacobiNat_eq_zero_or_eq a hn).elim (fun h0 ↦ by simp [h0] at h) (·.symm.trans h)

theorem jacobiSym_toNat_emod (a : ℤ) {n : ℕ} (hn : n ≠ 0) :
    J((a % n).toNat | n) = J(a | n) := by
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by lia)), ← jacobiSym.mod_left]

/-! ### The denominators of even degree -/

/-- The invariant of the loop of `Ratpoints.Fast.forbiddenDensFrom`: every marked denominator is
a multiple of an odd `q` with `J(lc | q) = -1`; that `q` is a prime, as the sieve of Eratosthenes
makes it, is not needed. -/
theorem exists_dvd_of_getElem!_forbiddenDensFrom_ne_zero {lc : ℤ} {hi : ℕ} {comp forb : ByteArray}
    {p : ℕ} (hp : p % 2 = 1)
    (hforb : ∀ b, forb[b]! ≠ 0 → ∃ q, q % 2 = 1 ∧ q ∣ b ∧ J(lc | q) = -1) {b : ℕ}
    (h : (forbiddenDensFrom lc hi comp forb p)[b]! ≠ 0) :
    ∃ q, q % 2 = 1 ∧ q ∣ b ∧ J(lc | q) = -1 := by
  fun_induction forbiddenDensFrom lc hi comp forb p with
  | case1 comp forb p _ _ ih => exact ih (by lia) hforb h
  | case2 comp forb p _ _ _ r forb' ih =>
    refine ih (by lia) (fun b hb ↦ ?_) h
    simp only [forb', r, dite_eq_ite] at hb
    split_ifs at hb with hJ
    · rcases of_getElem!_markMultiples hb with hb | ⟨k, rfl⟩
      · exact hforb b hb
      · simp only [Bool.and_eq_true, beq_iff_eq] at hJ
        exact ⟨p, hp, ⟨k + 1, by ring⟩, (jacobiSym_toNat_emod lc (by lia)).symm.trans
          (jacobiSym_eq_neg_one_of_jacobiNat_eq_neg_one hp hJ.2)⟩
    · exact hforb b hb
  | case3 comp forb p _ => exact hforb b h

theorem exists_dvd_of_getElem!_forbiddenDens_ne_zero {lc : ℤ} {hi b : ℕ}
    (h : (forbiddenDens lc hi)[b]! ≠ 0) : ∃ q, q % 2 = 1 ∧ q ∣ b ∧ J(lc | q) = -1 :=
  exists_dvd_of_getElem!_forbiddenDensFrom_ne_zero (by decide)
    (fun _ hb ↦ absurd (ByteArray.getElem!_mk_replicate_zero ..) hb) h

/-! ### The denominators of odd degree -/

theorem size_markSquares (a : ByteArray) (s k hi : ℕ) : (markSquares a s k hi).size = a.size := by
  fun_induction markSquares a s k hi <;> simp_all

/-- `Ratpoints.Fast.markSquares` keeps the marks of `a` and marks `s k₀ ^ 2 ≤ hi` for `k ≤ k₀`. -/
theorem getElem!_markSquares {a : ByteArray} {s k hi b : ℕ} (hb : b < a.size)
    (h : a[b]! = 1 ∨ ∃ k₀ ≥ k, k₀ ≤ hi ∧ b = s * k₀ * k₀ ∧ b ≤ hi) :
    (markSquares a s k hi)[b]! = 1 := by
  fun_induction markSquares a s k hi with
  | case1 a k hk ih =>
    refine ih (by simpa using hb) ?_
    rcases h with h | ⟨k₀, hk₀, hk₀hi, rfl, hb'⟩
    · exact .inl (ByteArray.getElem!_set!_of_getElem!_eq hb h)
    · rcases eq_or_lt_of_le hk₀ with rfl | hk₀
      · exact .inl (ByteArray.getElem!_set!_self _ _ _ hb)
      · exact .inr ⟨k₀, hk₀, hk₀hi, rfl, hb'⟩
  | case2 a k hk =>
    refine h.resolve_right fun ⟨k₀, hk₀, hk₀hi, hb', hbhi⟩ ↦ hk ⟨by lia, ?_⟩
    exact (Nat.mul_le_mul (Nat.mul_le_mul_left s hk₀) hk₀).trans (hb' ▸ hbhi)

theorem getElem!_foldl_markSquares {n hi b : ℕ} (l : List ℕ) {a : ByteArray} (hb : b < a.size)
    (h : a[b]! = 1 ∨ ∃ s ∈ l, n % s = 0 ∧ ∃ k ≥ 1, k ≤ hi ∧ b = s * k * k ∧ b ≤ hi) :
    (l.foldl (fun a s ↦ if n % s == 0 then markSquares a s 1 hi else a) a)[b]! = 1 := by
  induction l generalizing a with
  | nil => simpa using h
  | cons s l ih =>
    rw [List.foldl_cons]
    refine ih (by split_ifs <;> simp [size_markSquares, hb]) ?_
    rcases h with h | ⟨s', hs', hn, k, hk, hkhi, rfl, hb'⟩
    · exact .inl (by split_ifs; exacts [getElem!_markSquares hb (.inl h), h])
    · rcases List.mem_cons.mp hs' with rfl | hs'
      · exact .inl (by simpa [hn] using getElem!_markSquares hb (.inr ⟨k, hk, hkhi, rfl, hb'⟩))
      · exact .inr ⟨s', hs', hn, k, hk, hkhi, rfl, hb'⟩

theorem getElem!_squareDens {n hi s k : ℕ} (hn : n ≠ 0) (hs : s ∣ n) (hk : 1 ≤ k)
    (hb : s * k * k ≤ hi) : (squareDens n hi)[s * k * k]! = 1 := by
  have hs0 : 0 < s := Nat.pos_of_dvd_of_pos hs (Nat.pos_of_ne_zero hn)
  have hk' : k ≤ s * k * k := (Nat.le_mul_of_pos_left k hs0).trans (Nat.le_mul_of_pos_right _ hk)
  refine getElem!_foldl_markSquares _ (by simpa using Nat.lt_succ_of_le hb)
    (.inr ⟨s, ?_, Nat.mod_eq_zero_of_dvd hs, k, hk, by lia, rfl, hb⟩)
  rw [List.mem_range'_1]
  lia [Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hs,
    (Nat.le_mul_of_pos_right s hk).trans (Nat.le_mul_of_pos_right _ hk)]

end Ratpoints.Fast

end
