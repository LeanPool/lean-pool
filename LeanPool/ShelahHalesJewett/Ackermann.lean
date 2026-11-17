/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Computability.Ackermann
public import LeanPool.ShelahHalesJewett.HalesJewett

/-!
# Shelah's bound is below the fifth level of the Ackermann function

The recursion `Combinatorics.Subspace.insensitiveBound` replaces `r` colors by `r ^ k` colors, so
after `j` steps the number of colors is `r ^ k ^ j`. Each step adds a term that is doubly
exponential in the earlier ones, so `insensitiveBound k n r` is at most `ack 4` at a linear
function of `n`. Shelah's bound applies `insensitiveBound` once for each letter, so it is below
`ack 5` at a linear function of the number of letters and of colors.

## Main results

* `Combinatorics.Subspace.insensitiveBound_le_ack`:
  `insensitiveBound k n r ≤ ack 4 (5 * n + k + r + 2)`.
* `Combinatorics.Line.shelahBound_lt_ack`: `shelahBound k r < ack 5 (2 * k + r)`.
* `Combinatorics.Line.exists_mono_of_ack_le`: the Hales--Jewett theorem in every dimension at
  least `ack 5 (2 * k + r)`, for `k` letters and `r` colors.
-/

@[expose] public section

namespace Combinatorics

private lemma pow_le_two_pow_ack_three {b x : ℕ} (hx : b ≤ x) : b ^ x ≤ 2 ^ ack 3 x := by
  apply (Nat.pow_le_pow_left (hx.trans Nat.lt_two_pow_self.le) x).trans
  rw [← pow_mul, ← sq]
  apply Nat.pow_le_pow_right two_pos
  exact (Nat.pow_le_pow_left (by grind [ack_zero]) 2).trans (ack_add_one_sq_lt_ack_add_three 0 x)

private lemma add_pow_le_ack_three {b x : ℕ} (hx : b ≤ x) : x + b ^ x ≤ ack 3 (ack 3 x) := by
  grind [pow_le_two_pow_ack_three hx, ack_three (ack 3 x), Nat.lt_two_pow_self (n := ack 3 x),
    lt_ack_right 3 x]

private lemma add_pow_pow_le_ack_four {b m : ℕ} (hb : 2 ≤ b) (hm : b ≤ ack 4 m) :
    ack 4 m + b ^ b ^ ack 4 m ≤ ack 4 (m + 4) := by
  rw [ack_succ_succ, ack_succ_succ, ack_succ_succ, ack_succ_succ]
  apply (ack_mono_right 3 (ack_mono_right 3 (add_pow_le_ack_three hm))).trans'
  apply (add_pow_le_ack_three (b := b) (x := ack 4 m + b ^ ack 4 m) (by grind)).trans'
  gcongr ?_ + b ^ ?_ <;> grind

namespace Subspace

private lemma insensitiveBound_pow_add_le_ack (k r i j : ℕ) :
    insensitiveBound k i (r ^ k ^ j) + j + i ≤ ack 4 (5 * i + j + k + r + 2) := by
  induction i generalizing j with
  | zero => grind [insensitiveBound, lt_ack_right 4 (5 * 0 + j + k + r + 2)]
  | succ i ih =>
    rw [insensitiveBound, ← pow_mul r, ← pow_succ, ← pow_mul, ← pow_add,
      (by grind : 5 * (i + 1) + j + k + r + 2 = 5 * i + (j + 1) + k + r + 2 + 4)]
    have h : r ^ k ^ (j + insensitiveBound k i (r ^ k ^ (j + 1))) ≤
        (k + r + 2) ^ (k + r + 2) ^ ack 4 (5 * i + (j + 1) + k + r + 2) := by
      gcongr <;> grind
    grind [add_pow_pow_le_ack_four (b := k + r + 2) (m := 5 * i + (j + 1) + k + r + 2) (by grind)
      (by grind [lt_ack_right 4 (5 * i + (j + 1) + k + r + 2)])]

/-- The dimension `insensitiveBound k n r` is at most the fourth level of the Ackermann function
at a linear function of `n`. -/
theorem insensitiveBound_le_ack (k n r : ℕ) :
    insensitiveBound k n r ≤ ack 4 (5 * n + k + r + 2) := by
  grind [insensitiveBound_pow_add_le_ack k r n 0]

end Subspace

namespace Line

private lemma shelahBound_succ_le_ack (j r : ℕ) : shelahBound (j + 1) r ≤ ack 5 (2 * j + r) := by
  induction j with
  | zero => grind [shelahBound, ack_pos 5 r]
  | succ j ih =>
    rw [shelahBound, (by grind : 2 * (j + 1) + r = 2 * j + r + 1 + 1), ack_succ_succ,
      ack_succ_succ]
    apply (Subspace.insensitiveBound_le_ack _ _ _).trans
    apply ack_mono_right 4
    grind [add_lt_ack 5 (2 * j + r), ack_three (ack 5 (2 * j + r)),
      Nat.lt_two_pow_self (n := ack 5 (2 * j + r)),
      ack_le_ack (by grind : 3 ≤ 4) (le_refl (ack 5 (2 * j + r)))]

/-- Shelah's bound is below the fifth level of the Ackermann function. -/
theorem shelahBound_lt_ack (k r : ℕ) : shelahBound k r < ack 5 (2 * k + r) := by
  rcases k with _ | j
  · grind [shelahBound, one_lt_ack_succ_left 4 r]
  · exact (shelahBound_succ_le_ack j r).trans_lt (ack_strictMono_right 5 (by grind))

variable {α κ ι : Type*} [Fintype α] [Fintype κ] [Fintype ι]

/-- The **Hales--Jewett theorem** with the Ackermann function as the bound: over a nonempty
alphabet `α`, every coloring of the words indexed by `ι` has a monochromatic line if `card ι` is
at least `ack 5 (2 * card α + card κ)`. -/
theorem exists_mono_of_ack_le [Nonempty α]
    (h : ack 5 (2 * Fintype.card α + Fintype.card κ) ≤ Fintype.card ι) (C : (ι → α) → κ) :
    ∃ l : Line α ι, l.IsMono C :=
  exists_mono_of_shelahBound_le ((shelahBound_lt_ack _ _).le.trans h) C

end Line

end Combinatorics
