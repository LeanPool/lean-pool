/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import LeanPool.Ratpoints.Model.Sturm
public import Std.WP

import LeanPool.Ratpoints.Proof.Bits
import LeanPool.Ratpoints.Proof.Containers
import LeanPool.Ratpoints.Proof.VCSimp

/-!
# The contracts of the Sturm step

The steps of the remainder chain `Ratpoints.Sturm.chain` as plain functions, by well-founded
recursion where the model has a loop, the predicate of a remainder chain, and the contract of the
chain as a `@[spec]` theorem using the Hoare specifications of Lean core, with loop
invariants that are named definitions; the contracts of the evaluation of a row at a dyadic number
(`Ratpoints.Sturm.evalSign`: the sign of the value of the Horner rule in integers), of the signs and
the count of sign changes of the chain there (`Ratpoints.Sturm.signsAt`) and at `±∞`
(`Ratpoints.Sturm.countsAtInfinity`); the loop of the intersection with the caller's intervals
(`Ratpoints.Sturm.intersect`) as a recursion on the two lists (`Ratpoints.Sturm.intersectList`); and
the failure of the Sturm step (`Ratpoints.Sturm.computeSturm`) exactly when the chain fails.

## Main definitions

* `Ratpoints.Sturm.dropZeros`, `Ratpoints.Sturm.reduceOnce`, `Ratpoints.Sturm.fullReduce`: the zero
  leading coefficients of a remainder dropped, one reduction step followed by that drop, and the
  reduction of a remainder until its degree is below that of the divisor, `#[]` when it becomes
  zero.
* `Ratpoints.Sturm.content`, `Ratpoints.Sturm.normalize`: the gcd of the coefficients of a
  remainder, and the remainder negated and divided by it.
* `Ratpoints.Sturm.IsChain`: a remainder chain of a polynomial and its derivative.
* `Ratpoints.Sturm.IsChainResult`: the result of the chain as its contract states it, a chain whose
  last row is constant, or `none` when a chain reduces to zero.
* `Ratpoints.Sturm.hornerValue`: the value of a row at `n / 2 ^ e` times `2 ^ (e deg)`, by the
  Horner rule of `Ratpoints.Sturm.evalSign`.
* `Ratpoints.Sturm.signCount`: the sign changes that `Ratpoints.Sturm.signsAt` counts, zeros
  skipped.
* `Ratpoints.Sturm.signAtTop`, `Ratpoints.Sturm.signAtBot`: the signs of the rows at `±∞`.
* `Ratpoints.Sturm.intersectList`: the intersection of two lists of intervals by the steps of
  `Ratpoints.Sturm.intersect`.

## Main statements

* `Ratpoints.Sturm.chain_spec`: the loops of `Ratpoints.Sturm.chain` end, and its result satisfies
  `Ratpoints.Sturm.IsChainResult`; `Ratpoints.Sturm.isChainResult_run_chain` states this without
  the program logic.
* `Ratpoints.Sturm.IsChain.size_le`: a chain of a polynomial of degree `d` has at most `d + 1` rows.
* `Ratpoints.Sturm.evalSign_spec`, `Ratpoints.Sturm.signsAt_spec`,
  `Ratpoints.Sturm.countsAtInfinity_spec`, `Ratpoints.Sturm.intersect_spec`: the contracts of the
  evaluation, the signs at a midpoint, the counts at `±∞` and the intersection, with the plain
  statements `Ratpoints.Sturm.run_evalSign`, `Ratpoints.Sturm.run_signsAt`,
  `Ratpoints.Sturm.run_countsAtInfinity` and `Ratpoints.Sturm.toList_run_intersect`.
* `Ratpoints.Sturm.run_computeSturm_eq_none_iff`: the Sturm step fails exactly when the chain does.

## Implementation notes

The file uses Lean core and `Std` only, as `Ratpoints.Proof.Words` does; the lemmas on arrays,
lists, ranges and integers that are not about the model are in `Ratpoints.Proof.Containers`, those
on `long`s in `Ratpoints.Proof.Bits`. The plain statements let the files with Mathlib use the
contracts without the program logic; the values of the doubles of the intervals are in
`Ratpoints.Proof.Bisection`.
-/

@[expose] public section

open scoped Std.WP

namespace Ratpoints

namespace Sturm

/-! ### The steps of the chain -/

/-- The array `t` with its zero entries on top dropped, the zero leading coefficients of a
remainder: the loop of `Ratpoints.Sturm.chain` after a reduction step. -/
def dropZeros (t : Array Int) : Array Int :=
  if (t.back? == some 0) = true then dropZeros t.pop else t
termination_by t.size
decreasing_by exact Array.size_pop_lt_of_back?_eq_some (beq_iff_eq.mp ‹_›)

theorem dropZeros_of_beq {t : Array Int} (h : (t.back? == some 0) = true) :
    dropZeros t = dropZeros t.pop := by
  rw [dropZeros, ite_eq_left h]

theorem dropZeros_of_not_beq {t : Array Int} (h : ¬(t.back? == some 0) = true) :
    dropZeros t = t := by
  rw [dropZeros, ite_eq_right h]

theorem size_dropZeros_le (t : Array Int) : (dropZeros t).size ≤ t.size := by
  fun_induction dropZeros t with
  | case1 t h ih => lia [Array.size_pop_lt_of_back?_eq_some (beq_iff_eq.mp h)]
  | case2 => exact Nat.le_refl _

theorem back!_dropZeros_ne_zero {t : Array Int} (h : (dropZeros t).size ≠ 0) :
    (dropZeros t).back! ≠ 0 := by
  fun_induction dropZeros t with
  | case1 t _ ih => exact ih h
  | case2 t h' => exact Array.back!_ne_of_back?_ne h (by simpa using h')

theorem getElem!_dropZeros (t : Array Int) (i : Nat) : (dropZeros t)[i]! = t[i]! := by
  fun_induction dropZeros t with
  | case1 t h ih =>
    rw [ih, Array.getElem!_pop_of_back!_eq (by rw [Array.back!_eq_back?, beq_iff_eq.mp h]; rfl)]
  | case2 => rfl

theorem size_reduce (s t : Array Int) : (reduce s t).size = t.size - 1 + 1 := by
  simp [reduce]

/-- The entries of the reduction of `t` by `s`, `deg t ≥ deg s`: `u t - v X^(deg t - deg s) s` with
`u > 0` and `u lc t = v lc s`, so that the leading entry cancels. -/
theorem exists_getElem!_reduce {s t : Array Int} (hle : s.size ≤ t.size) (hs : s.back! ≠ 0) :
    ∃ u v : Int, 0 < u ∧ u * t.back! = v * s.back! ∧ ∀ n, (reduce s t)[n]! =
      u * t[n]! - v * if t.size - s.size ≤ n then s[n - (t.size - s.size)]! else 0 := by
  -- `hs1` halves the time of the `grind` at the end
  have hs1 := Array.size_ne_zero_of_back!_ne hs
  simp only [reduce]
  generalize hg : (Int.gcd s.back! t.back! : Int) = g
  have hds : g ∣ s.back! := hg ▸ Int.gcd_dvd_left ..
  have key := Int.ediv_mul_eq_ediv_mul_of_dvd hds (hg ▸ Int.gcd_dvd_right ..)
  have hu := Int.ediv_ne_zero_of_dvd hds hs
  refine ⟨if s.back! / g < 0 then -(s.back! / g) else s.back! / g,
    if s.back! / g < 0 then -(t.back! / g) else t.back! / g, by split <;> lia,
    by split <;> first | exact key | rw [Int.neg_mul, Int.neg_mul, key], fun n ↦ ?_⟩
  by_cases hn : n < t.size <;> grind [Array.getElem!_map_range, Int.default_eq_zero]

theorem back!_reduce {s t : Array Int} (hle : s.size ≤ t.size) (hs : s.back! ≠ 0) :
    (reduce s t).back! = 0 := by
  obtain ⟨u, v, -, huv, h⟩ := exists_getElem!_reduce hle hs
  have hs1 := Array.size_ne_zero_of_back!_ne hs
  grind [Array.back!_eq_getElem!, size_reduce]

/-- One reduction of `t` by `s` with the leading entry, which cancels, dropped, and then the zeros
on top: one pass of the reduction loop of `Ratpoints.Sturm.chain`. -/
def reduceOnce (s t : Array Int) : Array Int :=
  dropZeros (reduce s t).pop

theorem exists_getElem!_reduceOnce {s t : Array Int} (hle : s.size ≤ t.size) (hs : s.back! ≠ 0) :
    ∃ u v : Int, 0 < u ∧ ∀ n, (reduceOnce s t)[n]! =
      u * t[n]! - v * if t.size - s.size ≤ n then s[n - (t.size - s.size)]! else 0 := by
  obtain ⟨u, v, hu, -, h⟩ := exists_getElem!_reduce hle hs
  refine ⟨u, v, hu, fun n ↦ ?_⟩
  rw [reduceOnce, getElem!_dropZeros, Array.getElem!_pop_of_back!_eq (back!_reduce hle hs), h]

theorem size_reduceOnce_lt {s t : Array Int} (h : (reduceOnce s t).size ≠ 0) :
    (reduceOnce s t).size < t.size := by
  have := size_dropZeros_le (reduce s t).pop
  rw [Array.size_pop, size_reduce] at this
  rw [reduceOnce] at h ⊢
  lia

/-- The reduction loop of `Ratpoints.Sturm.chain`: `t` reduced by `s` until its size is below that
of `s`, and `#[]` when a reduction leaves nothing, where the chain returns `none`. -/
def fullReduce (s t : Array Int) : Array Int :=
  if s.size ≤ t.size then
    if (reduceOnce s t).size = 0 then #[] else fullReduce s (reduceOnce s t)
  else t
termination_by t.size
decreasing_by exact size_reduceOnce_lt ‹_›

theorem fullReduce_of_lt {s t : Array Int} (h : t.size < s.size) : fullReduce s t = t := by
  rw [fullReduce, ite_eq_right (by lia)]

theorem fullReduce_of_size_eq_zero {s t : Array Int} (hle : s.size ≤ t.size)
    (h : (reduceOnce s t).size = 0) : fullReduce s t = #[] := by
  rw [fullReduce, ite_eq_left hle, ite_eq_left h]

theorem fullReduce_of_size_ne_zero {s t : Array Int} (hle : s.size ≤ t.size)
    (h : (reduceOnce s t).size ≠ 0) : fullReduce s t = fullReduce s (reduceOnce s t) := by
  rw [fullReduce, ite_eq_left hle, ite_eq_right h]

/-- The gcd of the entries of `t`, the loop of `Ratpoints.Sturm.chain` over the coefficients of a
remainder, there with a `break` once the gcd is `1`. -/
def content (t : Array Int) : Nat :=
  t.foldl (fun g a ↦ g.gcd a.natAbs) 0

/-- The array `t` negated and divided by the gcd of its entries: the change of sign and the
division of a remainder by the gcd of its coefficients in `Ratpoints.Sturm.chain`. -/
def normalize (t : Array Int) : Array Int :=
  (t.map Neg.neg).map fun x ↦ x / (content (t.map Neg.neg) : Int)

theorem natCast_content_dvd_getElem! (t : Array Int) (i : Nat) : (content t : Int) ∣ t[i]! := by
  by_cases hi : i < t.size
  · rw [content, ← Array.foldl_toList, getElem!_pos t i hi]
    exact Int.ofNat_dvd_left.mpr
      (List.foldl_gcd_natAbs_dvd_natAbs 0 (Array.mem_def.mp (Array.getElem_mem hi)))
  · rw [getElem!_neg t i hi]
    exact Int.dvd_zero _

theorem size_normalize (t : Array Int) : (normalize t).size = t.size := by
  simp [normalize]

theorem mul_getElem!_normalize (t : Array Int) (i : Nat) :
    (content (t.map Neg.neg) : Int) * (normalize t)[i]! = -t[i]! := by
  rw [normalize, Array.getElem!_map (f := (· / _)) (Int.zero_ediv _),
    Int.mul_ediv_cancel' (natCast_content_dvd_getElem! _ i), Array.getElem!_map Int.neg_zero]

theorem content_map_neg_ne_zero {t : Array Int} (h : (normalize t).back! ≠ 0) :
    content (t.map Neg.neg) ≠ 0 := fun h0 ↦
  h (by rw [normalize, h0, Array.back!_map (f := (· / _)) (Int.zero_ediv _)]; simp)

theorem back!_normalize_ne_zero {t : Array Int} (h : t.back! ≠ 0) : (normalize t).back! ≠ 0 := by
  have hd := natCast_content_dvd_getElem! (t.map Neg.neg) (t.size - 1)
  grind [normalize, Array.back!_eq_getElem!, Int.ediv_ne_zero_of_dvd]

/-! ### Remainder chains -/

/-- The rows `ch` are a remainder chain of the polynomial `f` of degree `d` with the coefficients
`c₀, …, c_d`, the entries of `c`, as `Ratpoints.Sturm.chain` computes it. -/
structure IsChain (c : List Int) (d : Nat) (ch : Array (Array Int)) : Prop where
  /-- The chain has `f` and `f'` at least. -/
  two_le_size : 2 ≤ ch.size
  /-- The first row is `f`, the coefficients `c₀, …, c_d`. -/
  getElem!_zero : ch[0]! = (Array.range (d + 1)).map fun x ↦ c.getD x 0
  /-- The second row is `f'`, the coefficients `(n + 1) c_(n+1)` for `n < d`. -/
  getElem!_one : ch[1]! = (Array.range d).map fun (n : Nat) ↦ (n + 1 : Int) * c.getD (n + 1) 0
  /-- Each further row is the full reduction of the row two before by the row before, negated and
  divided by the gcd of its entries. -/
  getElem!_add_two (k : Nat) (hk : k + 2 < ch.size) :
    ch[k + 2]! = normalize (fullReduce ch[k + 1]! ch[k]!)
  /-- Every row has a nonzero last entry, its leading coefficient. -/
  back!_ne_zero (k : Nat) (hk : k < ch.size) : ch[k]!.back! ≠ 0
  /-- The sizes decrease strictly from `f'` on. -/
  size_lt (k : Nat) (hk : k + 2 < ch.size) : ch[k + 2]!.size < ch[k + 1]!.size

/-- The result of `Ratpoints.Sturm.chain` as its contract states it: `some ch` for a chain `ch`
whose last row is constant; `none` when there is a chain whose last row is not constant and reduces
the row before it to zero, which `Ratpoints.Sturm.fullReduce` gives as `#[]`. -/
def IsChainResult (c : List Int) (d : Nat) : Option (Array (Array Int)) → Prop
  | none => ∃ ch, IsChain c d ch ∧ 2 ≤ ch.back!.size ∧ fullReduce ch.back! ch[ch.size - 2]! = #[]
  | some ch => IsChain c d ch ∧ ch.back!.size = 1

theorem isChain_pair {c : List Int} {d : Nat} (hd : 1 ≤ d) (hc : c.getD d 0 ≠ 0) :
    IsChain c d #[(Array.range (d + 1)).map fun x ↦ c.getD x 0,
      (Array.range d).map fun (n : Nat) ↦ (n + 1 : Int) * c.getD (n + 1) 0] := by
  refine ⟨by simp, by simp, by simp, fun k hk ↦ absurd hk (by simp), fun k hk ↦ ?_,
    fun k hk ↦ absurd hk (by simp)⟩
  obtain rfl | rfl : k = 0 ∨ k = 1 := by simp at hk; lia
  · simpa [Array.back!_map_range _ (Nat.succ_ne_zero d)] using hc
  · simpa [Array.back!_map_range _ (by lia : d ≠ 0), Nat.sub_add_cancel hd] using
      Int.mul_ne_zero (by lia) hc

theorem IsChain.push {c : List Int} {d : Nat} {ch : Array (Array Int)} {t : Array Int}
    (h : IsChain c d ch) (ht : fullReduce ch.back! ch[ch.size - 2]! = t) (ht0 : t.back! ≠ 0)
    (hlt : t.size < ch.back!.size) : IsChain c d (ch.push (normalize t)) := by
  obtain ⟨m, hm⟩ : ∃ m, ch.size = m + 2 := ⟨ch.size - 2, by lia [h.two_le_size]⟩
  have hp {i : Nat} (hi : i < m + 2) : (ch.push (normalize t))[i]! = ch[i]! :=
    Array.getElem!_push_lt (hm ▸ hi)
  have hn : (ch.push (normalize t))[m + 2]! = normalize t := hm ▸ Array.getElem!_push_eq
  simp only [Array.back!_eq_getElem!, hm, show m + 2 - 1 = m + 1 by lia,
    show m + 2 - 2 = m by lia] at ht hlt
  refine ⟨by simp [hm], by rw [hp (by lia), h.getElem!_zero], by rw [hp (by lia), h.getElem!_one],
    fun k hk ↦ ?_, fun k hk ↦ ?_, fun k hk ↦ ?_⟩ <;> rw [Array.size_push, hm] at hk
  · rcases Nat.lt_succ_iff_lt_or_eq.mp (by lia : k < m + 1) with hk' | rfl
    · rw [hp (by lia), hp (by lia), hp (by lia), h.getElem!_add_two k (by lia)]
    · rw [hn, hp (by lia), hp (by lia), ht]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
    · exact hp hk' ▸ h.back!_ne_zero k (hm ▸ hk')
    · exact hn.symm ▸ back!_normalize_ne_zero ht0
  · rcases Nat.lt_succ_iff_lt_or_eq.mp (by lia : k < m + 1) with hk' | rfl
    · rw [hp (by lia), hp (by lia)]
      exact h.size_lt k (by lia)
    · rw [hn, hp (by lia), size_normalize]
      exact hlt

/-- The row `k + 1` of a chain has at most `d - k` entries: the sizes drop by one at least from
`f'` on. -/
theorem IsChain.size_getElem!_add_one_add_le {c : List Int} {d : Nat} {ch : Array (Array Int)}
    (h : IsChain c d ch) {k : Nat} (hk : k + 1 < ch.size) : ch[k + 1]!.size + k ≤ d := by
  induction k with
  | zero => simp [h.getElem!_one]
  | succ k ih => grind [h.size_lt k hk]

/-- A chain has at most `d + 1` rows, the rows of the table of the C code. -/
theorem IsChain.size_le {c : List Int} {d : Nat} {ch : Array (Array Int)} (h : IsChain c d ch) :
    ch.size ≤ d + 1 := by
  have := h.two_le_size
  lia [h.size_getElem!_add_one_add_le (k := ch.size - 2) (by lia),
    Array.size_ne_zero_of_back!_ne (h.back!_ne_zero (ch.size - 2 + 1) (by lia))]

/-! ### The invariants -/

/-- The rows while the loop of `Ratpoints.Sturm.chain` over `k` runs, after the indices `pref`, with
the indices `suff` still to come: a chain (`Ratpoints.Sturm.IsChain`), whose last row is constant
once no index is left; while indices are left, one row for each index done after `f` and `f'`, the
last one not constant, its size and the number of rows adding up to at most `d + 2`. -/
def ChainLoopInvariant (c : List Int) (d : Nat) (pref suff : List Nat)
    (ch : Array (Array Int)) : Prop :=
  IsChain c d ch ∧ (suff = [] → ch.back!.size = 1) ∧
    (suff ≠ [] → ch.size = pref.length + 2 ∧ 2 ≤ ch.back!.size ∧ ch.back!.size + ch.size ≤ d + 2)

/-- The invariant of the loop of `Ratpoints.Sturm.chain` over `k`, on the pair of the value of an
early `return` and the rows: no `return` yet and `Ratpoints.Sturm.ChainLoopInvariant`, or the
`return` of `none`, which ends the loop, with the result `none` of the contract. -/
def ChainInvariant (c : List Int) (d : Nat) (pref suff : List Nat)
    (x : Option (Option (Array (Array Int))) × Array (Array Int)) : Prop :=
  x.1 = none ∧ ChainLoopInvariant c d pref suff x.2 ∨
    suff = [] ∧ x.1 = some none ∧ IsChainResult c d none

/-- The invariant of the reduction loop of `Ratpoints.Sturm.chain` of `t₀` by `s`, on the pair of
the value of an early `return` and the remainder: no `return`, the same full reduction as `t₀`, a
nonzero last entry, and at the exit a size below that of `s`; or, at the exit, the `return` of
`none`, when the full reduction of `t₀` leaves nothing. -/
def ReduceInvariant (s t₀ : Array Int) (exit : Bool)
    (x : Option (Option (Array (Array Int))) × Array Int) : Prop :=
  x.1 = none ∧ fullReduce s x.2 = fullReduce s t₀ ∧ x.2.back! ≠ 0 ∧
      (exit = true → x.2.size < s.size) ∨
    exit = true ∧ x.1 = some none ∧ fullReduce s t₀ = #[]

/-- The invariant of the loop of `Ratpoints.Sturm.chain` that drops the zeros on top of `t₀`: the
same result of `Ratpoints.Sturm.dropZeros`, and no zero on top at the exit. -/
def DropZerosInvariant (t₀ : Array Int) (exit : Bool) (t : Array Int) : Prop :=
  dropZeros t = dropZeros t₀ ∧ (exit = true → ¬(t.back? == some 0) = true)

/-- The invariant of the loop of `Ratpoints.Sturm.chain` over the entries of a remainder: the gcd of
the entries `pref` done, the `break` at `1` included. -/
def ContentInvariant (pref : List Int) (g : Nat) : Prop :=
  g = pref.foldl (fun g a ↦ g.gcd a.natAbs) 0

/-! ### Initialization, preservation and exit of the loop invariants -/

theorem chainInvariant_nil {c : List Int} {d : Nat} (h : 1 ≤ d ∧ c.getD d 0 ≠ 0) :
    ChainInvariant c d [] (ForIn.toList [2:d + 1])
      (none, #[(Array.range (d + 1)).map fun x ↦ c.getD x 0,
        (Array.range d).map fun (n : Nat) ↦ (n + 1 : Int) * c.getD (n + 1) 0]) := by
  have hl : ForIn.toList [2:d + 1] = List.range' 2 (d - 1) := by simp [Std.Legacy.Range.size]
  refine .inl ⟨rfl, isChain_pair h.1 h.2, fun h0 ↦ ?_, fun h0 ↦ ?_⟩
  · rw [hl, List.range'_eq_nil_iff] at h0
    simp [Array.back!_eq_getElem!]
    lia
  · have : d - 1 ≠ 0 := fun h1 ↦ h0 (by rw [hl, h1]; rfl)
    simp [Array.back!_eq_getElem!]
    lia

theorem ChainInvariant.isChainResult {c : List Int} {d : Nat} {pref suff : List Nat}
    {y : Option (Option (Array (Array Int)))} {ch : Array (Array Int)}
    {a : Option (Array (Array Int))} (h : ChainInvariant c d pref suff (y, ch)) (hy : y = some a) :
    IsChainResult c d a := by
  rcases h with ⟨hy', -⟩ | ⟨-, hy', h⟩
  · cases hy.symm.trans hy'
  · obtain rfl := Option.some.inj (hy.symm.trans hy')
    exact h

theorem ChainInvariant.isChainResult_some {c : List Int} {d : Nat} {pref : List Nat}
    {y : Option (Option (Array (Array Int)))} {ch : Array (Array Int)}
    (h : ChainInvariant c d pref [] (y, ch)) (hy : y = none) : IsChainResult c d (some ch) := by
  rcases h with ⟨-, h⟩ | ⟨-, hy', -⟩
  · exact ⟨h.1, h.2.1 rfl⟩
  · cases hy.symm.trans hy'

theorem ChainInvariant.chainLoopInvariant {c : List Int} {d : Nat} {pref : List Nat} {cur : Nat}
    {suff : List Nat} {y : Option (Option (Array (Array Int)))} {ch : Array (Array Int)}
    (h : ChainInvariant c d pref (cur :: suff) (y, ch)) :
    y = none ∧ ChainLoopInvariant c d pref (cur :: suff) ch :=
  h.resolve_right fun h ↦ List.cons_ne_nil _ _ h.1

/-- At the index `cur`, the chain has `cur` rows: the reduction is of the row `cur - 2` by the row
`cur - 1`, the last one. -/
theorem ChainLoopInvariant.size_eq {c : List Int} {d : Nat} {pref : List Nat} {cur : Nat}
    {suff : List Nat} {ch : Array (Array Int)} (hl : ForIn.toList [2:d + 1] = pref ++ cur :: suff)
    (h : ChainLoopInvariant c d pref (cur :: suff) ch) : ch.size = cur := by
  lia [Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl,
    (h.2.2 (List.cons_ne_nil _ _)).1]

theorem ChainInvariant.reduceInvariant {c : List Int} {d : Nat} {pref : List Nat} {cur : Nat}
    {suff : List Nat} {y : Option (Option (Array (Array Int)))} {ch : Array (Array Int)}
    (hl : ForIn.toList [2:d + 1] = pref ++ cur :: suff)
    (h : ChainInvariant c d pref (cur :: suff) (y, ch)) :
    ReduceInvariant ch[cur - 1]! ch[cur - 2]! false (none, ch[cur - 2]!) := by
  obtain ⟨-, h⟩ := h.chainLoopInvariant
  exact .inl ⟨rfl, rfl, h.1.back!_ne_zero _ (by lia [h.size_eq hl, h.1.two_le_size]), nofun⟩

theorem ChainInvariant.of_reduceInvariant_some {c : List Int} {d : Nat} {pref : List Nat}
    {cur : Nat} {suff : List Nat} {y z : Option (Option (Array (Array Int)))}
    {ch : Array (Array Int)} {t : Array Int} {a : Option (Array (Array Int))}
    (hl : ForIn.toList [2:d + 1] = pref ++ cur :: suff)
    (h : ChainInvariant c d pref (cur :: suff) (y, ch))
    (ht : ReduceInvariant ch[cur - 1]! ch[cur - 2]! true (z, t)) (hz : z = some a) :
    ChainInvariant c d (ForIn.toList [2:d + 1]) [] (some a, ch) := by
  obtain ⟨-, h⟩ := h.chainLoopInvariant
  have hs := h.size_eq hl
  rcases ht with ⟨hz', -⟩ | ⟨-, hz', ht⟩
  · cases hz.symm.trans hz'
  · obtain rfl := Option.some.inj (hz.symm.trans hz')
    refine .inr ⟨rfl, rfl, ch, h.1, (h.2.2 (List.cons_ne_nil _ _)).2.1, ?_⟩
    rwa [Array.back!_eq_getElem!, hs]

/-- The step of the loop over `k`: the normalized full reduction `t` pushed onto the chain. -/
theorem ChainLoopInvariant.push {c : List Int} {d : Nat} {pref : List Nat} {cur : Nat}
    {suff : List Nat} {ch : Array (Array Int)} {t : Array Int}
    (hl : ForIn.toList [2:d + 1] = pref ++ cur :: suff)
    (h : ChainLoopInvariant c d pref (cur :: suff) ch)
    (ht : fullReduce ch[cur - 1]! ch[cur - 2]! = t) (ht0 : t.back! ≠ 0)
    (hlt : t.size < ch[cur - 1]!.size) :
    IsChain c d (ch.push (normalize t)) ∧ (¬(normalize t).size = 1 →
      ChainLoopInvariant c d (pref ++ [cur]) suff (ch.push (normalize t))) := by
  have hs := h.size_eq hl
  have hlen := Std.Legacy.Range.length_add_length_add_one_of_toList_eq_append_cons hl
  have hcur := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  obtain ⟨-, hb2, hle⟩ := h.2.2 (List.cons_ne_nil _ _)
  rw [← hs, ← Array.back!_eq_getElem!] at ht hlt
  have hc := h.1.push ht ht0 hlt
  have ht1 := Array.size_ne_zero_of_back!_ne ht0
  refine ⟨hc, fun h1 ↦ ⟨hc, fun hsuff ↦ ?_, fun _ ↦ ?_⟩⟩ <;>
    simp only [Array.back!_push, Array.size_push, size_normalize, List.length_append,
      List.length_singleton] at h1 ⊢
  · simp only [hsuff, List.length_nil] at hlen
    lia
  · lia

theorem ChainInvariant.push_normalize {c : List Int} {d : Nat} {pref : List Nat} {cur : Nat}
    {suff : List Nat} {y : Option (Option (Array (Array Int)))} {ch : Array (Array Int)}
    {t : Array Int} (hl : ForIn.toList [2:d + 1] = pref ++ cur :: suff)
    (h : ChainInvariant c d pref (cur :: suff) (y, ch))
    (ht : ReduceInvariant ch[cur - 1]! ch[cur - 2]! true (none, t)) :
    ((normalize t).size = 1 →
        ChainInvariant c d (ForIn.toList [2:d + 1]) [] (none, ch.push (normalize t))) ∧
      (¬(normalize t).size = 1 →
        ChainInvariant c d (pref ++ [cur]) suff (none, ch.push (normalize t))) := by
  obtain ⟨-, h⟩ := h.chainLoopInvariant
  obtain ⟨-, hfr, ht0, hlt⟩ := ht.resolve_right (by simp)
  rw [fullReduce_of_lt (hlt rfl)] at hfr
  obtain ⟨hc, h'⟩ := h.push hl hfr.symm ht0 (hlt rfl)
  refine ⟨fun h1 ↦ .inl ⟨rfl, hc, fun _ ↦ ?_, fun h ↦ absurd rfl h⟩, fun h1 ↦ .inl ⟨rfl, h' h1⟩⟩
  rwa [Array.back!_push]

theorem contentInvariant_nil : ContentInvariant [] 0 :=
  rfl

theorem ContentInvariant.append {pref : List Int} {g : Nat} (h : ContentInvariant pref g)
    (cur : Int) : ContentInvariant (pref ++ [cur]) (g.gcd cur.natAbs) := by
  rw [ContentInvariant, List.foldl_append, ← h]
  rfl

theorem ContentInvariant.of_gcd_eq_one {xs pref suff : List Int} {cur : Int} {g : Nat}
    (hl : xs = pref ++ cur :: suff) (h : ContentInvariant pref g) (hg : g.gcd cur.natAbs = 1) :
    ContentInvariant xs (g.gcd cur.natAbs) := by
  rw [ContentInvariant, hl, List.foldl_append, List.foldl_cons, ← h, hg, List.foldl_gcd_natAbs_one]

theorem ContentInvariant.normalize_eq {t : Array Int} {g : Nat}
    (h : ContentInvariant (ForIn.toList (t.map Neg.neg)) g) :
    normalize t = (t.map Neg.neg).map fun x ↦ x / (g : Int) := by
  rw [ContentInvariant, Std.Internal.ForIn.toList_array, Array.foldl_toList] at h
  rw [normalize, content, h]

theorem ContentInvariant.normalize_eq_map_neg {t : Array Int} {g : Nat}
    (h : ContentInvariant (ForIn.toList (t.map Neg.neg)) g) (h1 : ¬¬g = 1) :
    normalize t = t.map Neg.neg := by
  rw [h.normalize_eq, Decidable.of_not_not h1]
  simp

theorem ChainInvariant.push_of_size_eq_one {c : List Int} {d : Nat} {pref : List Nat} {cur : Nat}
    {suff : List Nat} {y z : Option (Option (Array (Array Int)))} {ch : Array (Array Int)}
    {t r : Array Int} (hl : ForIn.toList [2:d + 1] = pref ++ cur :: suff)
    (h : ChainInvariant c d pref (cur :: suff) (y, ch))
    (ht : ReduceInvariant ch[cur - 1]! ch[cur - 2]! true (z, t)) (hz : z = none)
    (hr : normalize t = r) (h1 : r.size = 1) :
    ChainInvariant c d (ForIn.toList [2:d + 1]) [] (none, ch.push r) := by
  subst hz hr
  exact (h.push_normalize hl ht).1 h1

theorem ChainInvariant.push_of_size_ne_one {c : List Int} {d : Nat} {pref : List Nat} {cur : Nat}
    {suff : List Nat} {y z : Option (Option (Array (Array Int)))} {ch : Array (Array Int)}
    {t r : Array Int} (hl : ForIn.toList [2:d + 1] = pref ++ cur :: suff)
    (h : ChainInvariant c d pref (cur :: suff) (y, ch))
    (ht : ReduceInvariant ch[cur - 1]! ch[cur - 2]! true (z, t)) (hz : z = none)
    (hr : normalize t = r) (h1 : ¬r.size = 1) :
    ChainInvariant c d (pref ++ [cur]) suff (none, ch.push r) := by
  subst hz hr
  exact (h.push_normalize hl ht).2 h1

theorem dropZerosInvariant_self (t : Array Int) : DropZerosInvariant t false t :=
  ⟨rfl, nofun⟩

theorem DropZerosInvariant.pop {t₀ t : Array Int} {mb : Nat}
    (h : t.size = mb ∧ DropZerosInvariant t₀ false t) (hb : (t.back? == some 0) = true) :
    t.pop.size < mb ∧ DropZerosInvariant t₀ false t.pop := by
  obtain ⟨rfl, h⟩ := h
  exact ⟨Array.size_pop_lt_of_back?_eq_some (beq_iff_eq.mp hb),
    (dropZeros_of_beq hb).symm.trans h.1, nofun⟩

theorem DropZerosInvariant.exit {t₀ t : Array Int} {mb : Nat}
    (h : t.size = mb ∧ DropZerosInvariant t₀ false t) (hb : ¬(t.back? == some 0) = true) :
    DropZerosInvariant t₀ true t :=
  ⟨h.2.1, fun _ ↦ hb⟩

theorem DropZerosInvariant.eq_reduceOnce {s t t' : Array Int}
    (h : DropZerosInvariant (reduce s t).pop true t') : t' = reduceOnce s t :=
  (dropZeros_of_not_beq (h.2 rfl)).symm.trans h.1

theorem ReduceInvariant.of_size_eq_zero {s t₀ t t' : Array Int}
    {y : Option (Option (Array (Array Int)))} {mb : Nat}
    (h : t.size = mb ∧ ReduceInvariant s t₀ false (y, t)) (hle : s.size ≤ t.size)
    (hd : DropZerosInvariant (reduce s t).pop true t') (h0 : t'.size = 0) :
    ReduceInvariant s t₀ true (some none, t') := by
  obtain ⟨-, hfr, -, -⟩ := h.2.resolve_right (by simp)
  rw [hd.eq_reduceOnce] at h0
  exact .inr ⟨rfl, rfl, hfr ▸ fullReduce_of_size_eq_zero hle h0⟩

theorem ReduceInvariant.of_size_ne_zero {s t₀ t t' : Array Int}
    {y : Option (Option (Array (Array Int)))} {mb : Nat}
    (h : t.size = mb ∧ ReduceInvariant s t₀ false (y, t)) (hle : s.size ≤ t.size)
    (hd : DropZerosInvariant (reduce s t).pop true t') (h0 : ¬t'.size = 0) :
    t'.size < mb ∧ ReduceInvariant s t₀ false (none, t') := by
  obtain ⟨rfl, h⟩ := h
  obtain ⟨-, hfr, -, -⟩ := h.resolve_right (by simp)
  rw [hd.eq_reduceOnce] at h0 ⊢
  exact ⟨size_reduceOnce_lt h0, .inl ⟨rfl, (fullReduce_of_size_ne_zero hle h0).symm.trans hfr,
    back!_dropZeros_ne_zero h0, nofun⟩⟩

theorem ReduceInvariant.exit {s t₀ t : Array Int} {y : Option (Option (Array (Array Int)))}
    {mb : Nat} (h : t.size = mb ∧ ReduceInvariant s t₀ false (y, t)) (hlt : ¬s.size ≤ t.size) :
    ReduceInvariant s t₀ true (none, t) := by
  obtain ⟨-, hfr, ht0, -⟩ := h.2.resolve_right (by simp)
  exact .inl ⟨rfl, hfr, ht0, fun _ ↦ by lia⟩

/- The invariants are irreducible from here on: the verification conditions of
`Ratpoints.Sturm.chain` are closed by their lemmas, never by unfolding them. -/
attribute [local irreducible] ChainLoopInvariant ChainInvariant ReduceInvariant DropZerosInvariant
  ContentInvariant

private theorem trimRemainder_spec (row : Array Int) :
    ⦃ True ⦄ (forIn (m := Id) ({} : Lean.Loop) row fun _ candidate ↦
      if candidate.back? == some 0 then pure (.yield candidate.pop) else pure (.done candidate))
    ⦃ DropZerosInvariant row true ⦄ := by
  apply Std.WP.Triple.iff.mpr
  refine Std.WP.Triple.entails_wp_of_pre (Std.WP.Spec.forIn_loop
    (Std.WP.Variant.ofMeasure Array.size) (.mk (DropZerosInvariant row)) Lean.Order.bot ?_) ?_
  · intro candidate remaining
    split <;> apply Std.WP.Triple.pure
    · intro h
      vc_simp
      exact DropZerosInvariant.pop h ‹_›
    · intro h
      vc_simp
      exact DropZerosInvariant.exit h ‹_›
  · exact fun _ ↦ dropZerosInvariant_self row

private theorem reduceRemainder_spec (divisor dividend : Array Int) :
    ⦃ ReduceInvariant divisor dividend false (none, dividend) ⦄
    (forIn (m := Id) ({} : Lean.Loop) (none, dividend) fun _ state ↦
      if divisor.size ≤ state.2.size then do
        let trimmed ← forIn (m := Id) ({} : Lean.Loop) (reduce divisor state.2).pop fun _ candidate ↦
          if candidate.back? == some 0 then pure (.yield candidate.pop) else pure (.done candidate)
        if trimmed.size = 0 then pure (.done (some none, trimmed)) else pure (.yield (none, trimmed))
      else pure (.done (none, state.2)))
    ⦃ ReduceInvariant divisor dividend true ⦄ := by
  refine Std.WP.Spec.forIn_loop (Std.WP.Variant.ofMeasure fun state ↦ state.2.size)
    (.mk (ReduceInvariant divisor dividend)) Lean.Order.bot ?_
  rintro ⟨returned, candidate⟩ remaining
  dsimp only
  split
  · refine Std.WP.Triple.bind _ _
      (fun trimmed ↦ (candidate.size = remaining ∧
        ReduceInvariant divisor dividend false (returned, candidate)) ∧
        DropZerosInvariant (reduce divisor candidate).pop true trimmed) ?_ ?_
    · refine ⟨fun h ↦ ?_⟩
      vc_simp
      exact ⟨h, (trimRemainder_spec _).le_wp trivial⟩
    · intro trimmed
      split <;> apply Std.WP.Triple.pure
      · rintro ⟨h, trimmedInvariant⟩
        exact ReduceInvariant.of_size_eq_zero h ‹_› trimmedInvariant ‹_›
      · rintro ⟨h, trimmedInvariant⟩
        vc_simp
        exact ReduceInvariant.of_size_ne_zero h ‹_› trimmedInvariant ‹_›
  · apply Std.WP.Triple.pure
    intro h
    vc_simp
    exact ReduceInvariant.exit h ‹_›

private theorem contentLoop_spec (row : Array Int) :
    ⦃ True ⦄ (forIn (m := Id) row (0 : Nat) fun (coefficient : Int) value ↦
      if value.gcd coefficient.natAbs = 1 then pure (.done (value.gcd coefficient.natAbs))
      else pure (.yield (value.gcd coefficient.natAbs)))
    ⦃ ContentInvariant (ForIn.toList row) ⦄ := by
  apply Std.WP.Triple.iff.mpr
  refine Std.WP.Triple.entails_wp_of_pre (Std.WP.Spec.forIn_pure
    (fun visited _ ↦ ContentInvariant visited) ?_) ?_
  · intro visited coefficient suffix hRange value
    split <;> apply Std.WP.Triple.pure
    · exact fun h ↦ ContentInvariant.of_gcd_eq_one hRange h ‹_›
    · exact fun h ↦ h.append coefficient
  · exact fun _ ↦ contentInvariant_nil

/-- The loop over `k` ends by its range, the reduction loop by the size of the remainder, which
drops with every pass, and the loop that drops the zeros on top by the size as well. -/
@[spec]
theorem chain_spec (c : List Int) (d : Nat) :
    ⦃ 1 ≤ d ∧ c.getD d 0 ≠ 0 ⦄ chain c d ⦃ IsChainResult c d ⦄ := by
  refine ⟨fun valid ↦ ?_⟩
  have specification : ⦃ True ⦄ chain c d ⦃ IsChainResult c d ⦄ := by
    rw [chain.eq_1]
    dsimp only
    let indices := ForIn.toList [2:d + 1]
    refine Std.WP.Triple.bind _ _ (ChainInvariant c d indices []) ?_ ?_
    · apply Std.WP.Triple.iff.mpr
      refine Std.WP.Triple.entails_wp_of_pre (Std.WP.Spec.forIn_pure (ChainInvariant c d) ?_) ?_
      · rintro visited current suffix hRange ⟨returned, rows⟩
        dsimp only
        let previous := ChainInvariant c d visited (current :: suffix) (returned, rows)
        let divisor := rows[current - 1]!
        let dividend := rows[current - 2]!
        refine Std.WP.Triple.bind _ _
          (fun state ↦ previous ∧ ReduceInvariant divisor dividend true state) ?_ ?_
        · exact ⟨fun h ↦ ⟨h, (reduceRemainder_spec divisor dividend).le_wp
            (h.reduceInvariant hRange)⟩⟩
        · rintro ⟨reductionResult, remainder⟩
          cases reductionResult with
          | some result =>
            apply Std.WP.Triple.pure
            exact fun ⟨h, reduced⟩ ↦ h.of_reduceInvariant_some hRange reduced rfl
          | none =>
            let negated := remainder.map Neg.neg
            let reduced := previous ∧ ReduceInvariant divisor dividend true (none, remainder)
            refine Std.WP.Triple.bind _ _
              (fun value ↦ reduced ∧ ContentInvariant (ForIn.toList negated) value) ?_ ?_
            · exact ⟨fun h ↦ ⟨h, (contentLoop_spec negated).le_wp trivial⟩⟩
            · intro value
              repeat' first
              | apply Std.WP.Triple.pure
                rintro ⟨⟨h, hReduced⟩, contentInvariant⟩
                have normalized := contentInvariant.normalize_eq (t := remainder)
                first
                | exact h.push_of_size_eq_one hRange hReduced rfl normalized ‹_›
                | exact h.push_of_size_ne_one hRange hReduced rfl normalized ‹_›
                | exact h.push_of_size_eq_one hRange hReduced rfl
                    (contentInvariant.normalize_eq_map_neg ‹_›) ‹_›
                | exact h.push_of_size_ne_one hRange hReduced rfl
                    (contentInvariant.normalize_eq_map_neg ‹_›) ‹_›
              | split
      · exact fun _ ↦ chainInvariant_nil valid
    · rintro ⟨result, rows⟩
      cases result with
      | some result =>
        apply Std.WP.Triple.pure
        exact fun h ↦ h.isChainResult rfl
      | none =>
        apply Std.WP.Triple.pure
        exact fun h ↦ h.isChainResult_some rfl
  exact specification.le_wp trivial

/-- `Ratpoints.Sturm.chain_spec` as a plain statement, which the files with Mathlib use without the
program logic. -/
theorem isChainResult_run_chain {c : List Int} {d : Nat} (hd : 1 ≤ d) (hc : c.getD d 0 ≠ 0) :
    IsChainResult c d (Id.run (chain c d)) :=
  Std.WP.Id.of_run_eq_wp rfl _ ((chain_spec c d).le_wp ⟨hd, hc⟩)

/-! ### The signs of the chain -/

/-- The value of the polynomial with the coefficients `row`, constant term first, at `num / 2 ^ e`,
times `2 ^ (e deg)`, `deg` the size of `row` less one, as the Horner rule of
`Ratpoints.Sturm.evalSign` computes it in integers, after `j` of its steps: from the leading
coefficient, `w ↦ w num + c_(deg - j - 1) 2 ^ (e (j + 1))` at the step `j`. -/
def hornerValue (row : Array Int) (num : Int) (e : Nat) : Nat → Int
  | 0 => row[row.size - 1]!
  | j + 1 => hornerValue row num e j * num + row[row.size - 2 - j]! * 2 ^ (e * (j + 1))

/-- The invariant of the loop of `Ratpoints.Sturm.evalSign` after the steps `pref`: the value of
the Horner rule after as many steps, and the exponent of the next step. -/
def EvalSignInvariant (row : Array Int) (num denexp : Int64) (pref : List Nat) (x : Int × Int64) :
    Prop :=
  x.1 = hornerValue row num.toInt denexp.toInt.toNat pref.length ∧
    x.2.toInt = denexp.toInt * (pref.length + 1)

theorem evalSignInvariant_nil (row : Array Int) (num denexp : Int64) :
    EvalSignInvariant row num denexp [] (row[row.size - 1]!, denexp) := by
  simp [EvalSignInvariant, hornerValue]

theorem EvalSignInvariant.sign_eq {row : Array Int} {num denexp : Int64} {w : Int} {e : Int64}
    (h : EvalSignInvariant row num denexp (ForIn.toList [:row.size - 1]) (w, e)) :
    w.sign = (hornerValue row num.toInt denexp.toInt.toNat (row.size - 1)).sign := by
  rw [show w = _ from h.1]
  simp [Std.Internal.ForIn.toList_range]

/-- A step of the loop of `Ratpoints.Sturm.evalSign`; the exponents `denexp (j + 1)` stay below
`2 ^ 63`. -/
theorem EvalSignInvariant.push {row : Array Int} {num denexp : Int64} {pref suff : List Nat}
    {cur : Nat} (hd : 0 ≤ denexp.toInt ∧ denexp.toInt * row.size < 2 ^ 63)
    (hl : ForIn.toList [:row.size - 1] = pref ++ cur :: suff) {w : Int} {e : Int64}
    (h : EvalSignInvariant row num denexp pref (w, e)) :
    EvalSignInvariant row num denexp (pref ++ [cur])
      (w * num.toInt + row[row.size - 1 - 1 - cur]! * 2 ^ e.toInt.toNat, e + denexp) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  obtain ⟨h1, h2⟩ := h
  have hb : denexp.toInt * (cur + 1 + 1) ≤ denexp.toInt * row.size :=
    Int.mul_le_mul_of_nonneg_left (by lia) hd.1
  refine ⟨?_, ?_⟩
  · simp only [List.length_append, List.length_singleton, hornerValue, h2, hc]
    congr 3
    · lia
    · rw [Int.toNat_mul (by lia) (by lia)]; simp
  · rw [Int64.toInt_add_of_lt (by lia) (by lia), h2]
    simp only [List.length_append, List.length_singleton]
    push_cast
    lia

/-- The number of sign changes that the loop of `Ratpoints.Sturm.signsAt` counts in the signs `l`
after the sign `s`: a sign `-s` counts and becomes the sign compared, another sign that is not `0`
becomes the sign compared, and a `0` is skipped. For a sign `s ≠ 0` this is the number of sign
changes of `s` followed by `l`, the zeros skipped. -/
def signCount : Int → List Int → Nat
  | _, [] => 0
  | s, t :: ts => if t = -s then signCount t ts + 1 else if t ≠ 0 then signCount t ts else
      signCount s ts

/-- The invariant of the loop of `Ratpoints.Sturm.signsAt` with the indices `suff` still to come:
the count so far and the count of the signs `σ n` still to come after the sign compared add up to
`total`. -/
def SignsAtInvariant (σ : Nat → Int) (total : Nat) (suff : List Nat) (x : Nat × Int) : Prop :=
  x.1 + signCount x.2 (suff.map σ) = total

theorem signsAtInvariant_init (σ : Nat → Int) (c : Nat) (s : Int) (l : List Nat) :
    SignsAtInvariant σ (c + signCount s (l.map σ)) l (c, s) :=
  rfl

theorem SignsAtInvariant.of_cons {σ : Nat → Int} {total cur : Nat} {suff : List Nat} {cmid : Nat}
    {s : Int} (h : SignsAtInvariant σ total (cur :: suff) (cmid, s)) :
    SignsAtInvariant σ total suff
      (if σ cur = -s then cmid + 1 else cmid, if σ cur = -s then σ cur else
        if σ cur ≠ 0 then σ cur else s) := by
  simp only [SignsAtInvariant, List.map_cons, signCount] at h ⊢
  grind

theorem SignsAtInvariant.of_cons_neg {σ : Nat → Int} {total cur : Nat} {suff : List Nat}
    {cmid : Nat} {s s2 : Int} (h : SignsAtInvariant σ total (cur :: suff) (cmid, s))
    (h2 : s2 = σ cur) (hn : s2 = -s) : SignsAtInvariant σ total suff (cmid + 1, s2) := by
  subst h2
  simpa [hn] using h.of_cons

theorem SignsAtInvariant.of_cons_ne {σ : Nat → Int} {total cur : Nat} {suff : List Nat}
    {cmid : Nat} {s s2 : Int} (h : SignsAtInvariant σ total (cur :: suff) (cmid, s))
    (h2 : s2 = σ cur) (hn : ¬s2 = -s) (h0 : ¬s2 = 0) :
    SignsAtInvariant σ total suff (cmid, s2) := by
  subst h2
  simpa [hn, h0] using h.of_cons

theorem SignsAtInvariant.of_cons_zero {σ : Nat → Int} {total cur : Nat} {suff : List Nat}
    {cmid : Nat} {s s2 : Int} (h : SignsAtInvariant σ total (cur :: suff) (cmid, s))
    (h2 : s2 = σ cur) (hn : ¬s2 = -s) (h0 : ¬¬s2 = 0) :
    SignsAtInvariant σ total suff (cmid, s) := by
  subst h2
  simpa [hn, h0] using h.of_cons

theorem SignsAtInvariant.eq {σ : Nat → Int} {s0 s1 r0 r1 b : Int} {k cmid : Nat}
    (h0 : s0 = r0) (h1 : s1 = r1)
    (h : SignsAtInvariant σ ((if s0 * s1 = -1 then 1 else 0) +
      signCount (if s1 = 0 then s0 else s1) ((ForIn.toList [2:k + 1]).map σ)) [] (cmid, b)) :
    (s0, s1, cmid) = (r0, r1, (if r0 * r1 = -1 then 1 else 0) +
      signCount (if r1 = 0 then r0 else r1) ((List.range' 2 (k - 1)).map σ)) := by
  subst h0 h1
  simp only [SignsAtInvariant, List.map_nil, signCount, Nat.add_zero] at h
  simp [h, Std.Internal.ForIn.toList_range]

/-- The sign of the leading coefficient of the row `n` of the chain `rows`, the sign of the row at
`+∞`. -/
def signAtTop (rows : Array (Array Int)) (n : Nat) : Int := rows[n]![rows[n]!.size - 1]!.sign

/-- The sign of the row `n` of the chain `rows` at `-∞`: that of its leading coefficient, negated
for odd degree. -/
def signAtBot (rows : Array (Array Int)) (n : Nat) : Int :=
  if (rows[n]!.size - 1) % 2 = 1 then -signAtTop rows n else signAtTop rows n

/-- The invariant of the loop of `Ratpoints.Sturm.countsAtInfinity` after the indices `pref`: the
numbers of the indices `n` among them where the signs of the rows `n` and `n + 1` differ at `+∞` and
at `-∞`. -/
def CountsInvariant (rows : Array (Array Int)) (pref : List Nat) (x : Nat × Nat) : Prop :=
  x = (pref.countP fun n ↦ signAtTop rows n != signAtTop rows (n + 1),
    pref.countP fun n ↦ signAtBot rows n != signAtBot rows (n + 1))

theorem countsInvariant_nil (rows : Array (Array Int)) : CountsInvariant rows [] (0, 0) :=
  rfl

theorem CountsInvariant.push {rows : Array (Array Int)} {pref : List Nat} {cur c1 c2 : Nat}
    (h : CountsInvariant rows pref (c1, c2)) {a b : Nat}
    (ha : a = if signAtTop rows cur = signAtTop rows (cur + 1) then c1 else c1 + 1)
    (hb : b = if signAtBot rows cur = signAtBot rows (cur + 1) then c2 else c2 + 1) :
    CountsInvariant rows (pref ++ [cur]) (a, b) := by
  simp only [CountsInvariant, Prod.mk.injEq] at h ⊢
  rw [List.countP_append, List.countP_append, ← h.1, ← h.2, ha, hb]
  constructor <;> split <;> simp_all

theorem CountsInvariant.range {rows : Array (Array Int)} {k : Nat} {x : Nat × Nat}
    (h : CountsInvariant rows (ForIn.toList [:k]) x) : CountsInvariant rows (List.range k) x := by
  simpa [Std.Internal.ForIn.toList_range, List.range_eq_range'] using h

attribute [local irreducible] EvalSignInvariant SignsAtInvariant CountsInvariant

/-- The exponents `denexp (j + 1)` of the Horner rule stay below `2 ^ 63`, so that the `long` `e`
does not overflow. -/
@[spec]
theorem evalSign_spec (row : Array Int) (num denexp : Int64) :
    ⦃ 0 ≤ denexp.toInt ∧ denexp.toInt * row.size < 2 ^ 63 ⦄ evalSign row num denexp
    ⦃ fun s ↦ s = (hornerValue row num.toInt denexp.toInt.toNat (row.size - 1)).sign ⦄ := by
  refine ⟨fun bounds ↦ ?_⟩
  have specification : ⦃ True ⦄ evalSign row num denexp
      ⦃ fun sign ↦ sign = (hornerValue row num.toInt denexp.toInt.toNat (row.size - 1)).sign ⦄ := by
    rw [evalSign.eq_1]
    dsimp only
    refine Std.WP.Triple.bind _ _
      (EvalSignInvariant row num denexp (ForIn.toList [:row.size - 1])) ?_ ?_
    · apply Std.WP.Triple.iff.mpr
      refine Std.WP.Triple.entails_wp_of_pre (Std.WP.Spec.forIn_pure
        (fun visited _ state ↦ EvalSignInvariant row num denexp visited state) ?_) ?_
      · rintro visited current suffix hRange ⟨value, exponent⟩
        apply Std.WP.Triple.pure
        exact fun h ↦ h.push bounds hRange
      · exact fun _ ↦ evalSignInvariant_nil row num denexp
    · rintro ⟨value, exponent⟩
      apply Std.WP.Triple.pure
      exact fun h ↦ h.sign_eq
  exact specification.le_wp trivial

/-- `Ratpoints.Sturm.evalSign_spec` as a plain statement. -/
theorem run_evalSign {row : Array Int} (num : Int64) {denexp : Int64} (h0 : 0 ≤ denexp.toInt)
    (h : denexp.toInt * row.size < 2 ^ 63) :
    Id.run (evalSign row num denexp) =
      (hornerValue row num.toInt denexp.toInt.toNat (row.size - 1)).sign :=
  Std.WP.Id.of_run_eq_wp rfl _ ((evalSign_spec row num denexp).le_wp ⟨h0, h⟩)

-- The sign of a row at the midpoint, as a value for the contract of `Ratpoints.Sturm.signsAt`.
private theorem evalSign_value (row : Array Int) (num denexp : Int64) :
    ⦃ True ⦄ evalSign row num denexp ⦃ fun r ↦ r = Id.run (evalSign row num denexp) ⦄ :=
  ⟨fun _ ↦ rfl⟩

@[spec]
theorem signsAt_spec (rows : Array (Array Int)) (k : Nat) (nm dem : Int64) :
    ⦃ True ⦄ signsAt rows k nm dem ⦃ fun r ↦ r = (Id.run (evalSign rows[0]! nm dem),
      Id.run (evalSign rows[1]! nm dem),
      (if Id.run (evalSign rows[0]! nm dem) * Id.run (evalSign rows[1]! nm dem) = -1 then 1 else 0)
        + signCount (if Id.run (evalSign rows[1]! nm dem) = 0 then Id.run (evalSign rows[0]! nm dem)
          else Id.run (evalSign rows[1]! nm dem))
          ((List.range' 2 (k - 1)).map fun n ↦ Id.run (evalSign rows[n]! nm dem))) ⦄ := by
  let signOf := fun n : Nat ↦ Id.run (evalSign rows[n]! nm dem)
  rw [signsAt.eq_1]
  refine Std.WP.Triple.bind _ _ (fun firstSign ↦ firstSign = signOf 0)
    (evalSign_value rows[0]! nm dem) ?_
  intro firstSign
  refine Std.WP.Triple.bind _ _
    (fun secondSign ↦ firstSign = signOf 0 ∧ secondSign = signOf 1) ?_ ?_
  · exact ⟨fun h ↦ ⟨h, rfl⟩⟩
  intro secondSign
  let initialCount := if firstSign * secondSign = -1 then 1 else 0
  let initialSign := if secondSign = 0 then firstSign else secondSign
  let indices := ForIn.toList [2:k + 1]
  let total := initialCount + signCount initialSign (indices.map signOf)
  let invariant := fun (suffix : List Nat) (state : Nat × Int) ↦
    firstSign = signOf 0 ∧ secondSign = signOf 1 ∧ SignsAtInvariant signOf total suffix state
  refine Std.WP.Triple.bind _ _ (invariant []) ?_ ?_
  · apply Std.WP.Triple.iff.mpr
    refine Std.WP.Triple.entails_wp_of_pre
      (Std.WP.Spec.forIn_pure (fun _ suffix ↦ invariant suffix) ?_) ?_
    · rintro visited current suffix hRange ⟨count, lastSign⟩
      dsimp only
      refine Std.WP.Triple.bind _ _
        (fun nextSign ↦ invariant (current :: suffix) (count, lastSign) ∧
          nextSign = signOf current) ?_ ?_
      · exact ⟨fun h ↦ ⟨h, rfl⟩⟩
      · intro nextSign
        repeat' first
        | apply Std.WP.Triple.pure
          rintro ⟨⟨h0, h1, h⟩, hs⟩
          refine ⟨h0, h1, ?_⟩
          first
          | exact h.of_cons_neg hs ‹_›
          | exact h.of_cons_ne hs ‹_› ‹_›
          | exact h.of_cons_zero hs ‹_› ‹_›
        | split
    · exact fun ⟨h0, h1⟩ ↦ ⟨h0, h1, signsAtInvariant_init signOf _ _ _⟩
  · rintro ⟨count, lastSign⟩
    apply Std.WP.Triple.pure
    exact fun ⟨h0, h1, h⟩ ↦ SignsAtInvariant.eq h0 h1 h

/-- `Ratpoints.Sturm.signsAt_spec` as a plain statement: the signs `σ 0` and `σ 1` of `f` and `f'`
at the midpoint, and the number of sign changes of `σ 0, …, σ k`, the signs of the rows of the
chain there, the zeros skipped (`Ratpoints.Sturm.signCount`). -/
theorem run_signsAt (rows : Array (Array Int)) (k : Nat) (nm dem : Int64) :
    Id.run (signsAt rows k nm dem) = (Id.run (evalSign rows[0]! nm dem),
      Id.run (evalSign rows[1]! nm dem),
      (if Id.run (evalSign rows[0]! nm dem) * Id.run (evalSign rows[1]! nm dem) = -1 then 1 else 0)
        + signCount (if Id.run (evalSign rows[1]! nm dem) = 0 then Id.run (evalSign rows[0]! nm dem)
          else Id.run (evalSign rows[1]! nm dem))
          ((List.range' 2 (k - 1)).map fun n ↦ Id.run (evalSign rows[n]! nm dem))) :=
  Std.WP.Id.of_run_eq_wp rfl _ ((signsAt_spec rows k nm dem).le_wp trivial)

@[spec]
theorem countsAtInfinity_spec (rows : Array (Array Int)) (k : Nat) :
    ⦃ True ⦄ countsAtInfinity rows k ⦃ fun r ↦ CountsInvariant rows (List.range k) r ⦄ := by
  rw [countsAtInfinity.eq_1]
  refine Std.WP.Triple.bind _ _ (CountsInvariant rows (ForIn.toList [:k])) ?_ ?_
  · apply Std.WP.Triple.iff.mpr
    refine Std.WP.Triple.entails_wp_of_pre (Std.WP.Spec.forIn_pure
      (fun visited _ state ↦ CountsInvariant rows visited state) ?_) ?_
    · rintro visited current suffix hRange ⟨topCount, bottomCount⟩
      dsimp only
      repeat' first
      | apply Std.WP.Triple.pure
        intro h
        refine h.push ?_ ?_ <;> simp only [signAtTop, signAtBot] <;> grind
      | split
    · exact fun _ ↦ countsInvariant_nil rows
  · intro state
    apply Std.WP.Triple.pure
    exact fun h ↦ h.range

/-- `Ratpoints.Sturm.countsAtInfinity_spec` as a plain statement: the numbers of the indices
`n < k` where the signs of the rows `n` and `n + 1` of the chain differ at `+∞` and at `-∞`, the
numbers of sign changes of a chain whose rows have nonzero leading coefficients. -/
theorem run_countsAtInfinity (rows : Array (Array Int)) (k : Nat) :
    Id.run (countsAtInfinity rows k) =
      ((List.range k).countP fun n ↦ signAtTop rows n != signAtTop rows (n + 1),
        (List.range k).countP fun n ↦ signAtBot rows n != signAtBot rows (n + 1)) := by
  have h := Std.WP.Id.of_run_eq_wp rfl _ ((countsAtInfinity_spec rows k).le_wp trivial)
  rwa [CountsInvariant] at h

/-! ### The intersection with the caller's intervals -/

/-- The intersection of the intervals `loc` with the intervals `ivs`, by the steps of
`Ratpoints.Sturm.intersect` (`Ratpoints.Sturm.meet`) as a recursion on the two lists: the interval
that a step notes, followed by the intersection of the rest, without the interval of `loc` or of
`ivs` that ends first. -/
def intersectList : List (Double × Double) → List (Double × Double) → List (Double × Double)
  | [], _ => []
  | _ :: _, [] => []
  | a :: as, b :: bs =>
    (meet a b).1.toList ++
      if (meet a b).2 then intersectList as (b :: bs) else intersectList (a :: as) bs
termination_by l1 l2 => l1.length + l2.length

theorem intersectList_cons_cons (a b : Double × Double) (as bs : List (Double × Double)) :
    intersectList (a :: as) (b :: bs) = (meet a b).1.toList ++
      if (meet a b).2 then intersectList as (b :: bs) else intersectList (a :: as) bs := by
  rw [intersectList]

@[simp]
theorem intersectList_nil_left (bs : List (Double × Double)) : intersectList [] bs = [] := by
  simp [intersectList]

@[simp]
theorem intersectList_nil_right (as : List (Double × Double)) : intersectList as [] = [] := by
  cases as <;> simp [intersectList]

/-- The invariant of the loop of `Ratpoints.Sturm.intersect` on the cursors `n1`, `n2` and the
intervals noted: they followed by the intersection of the rest of the lists are the intersection of
the lists, and at the exit the rest of one of the lists is empty. -/
def IntersectInvariant (loc ivs : Array (Double × Double)) (exit : Bool)
    (x : Nat × Nat × Array (Double × Double)) : Prop :=
  x.2.2.toList ++ intersectList (loc.toList.drop x.1) (ivs.toList.drop x.2.1) =
      intersectList loc.toList ivs.toList ∧
    (exit = true → intersectList (loc.toList.drop x.1) (ivs.toList.drop x.2.1) = [])

theorem intersectInvariant_zero (loc ivs : Array (Double × Double)) :
    IntersectInvariant loc ivs false (0, 0, #[]) := by
  simp [IntersectInvariant]

theorem IntersectInvariant.exit {loc ivs : Array (Double × Double)} {n1 n2 : Nat}
    {out : Array (Double × Double)} (h : IntersectInvariant loc ivs false (n1, n2, out))
    (hx : ¬(n1 < loc.size ∧ n2 < ivs.size)) : IntersectInvariant loc ivs true (n1, n2, out) := by
  refine ⟨h.1, fun _ ↦ ?_⟩
  rcases Nat.lt_or_ge n1 loc.size with h1 | h1
  · simp [List.drop_eq_nil_of_le (by simp; lia : ivs.toList.length ≤ n2)]
  · simp [List.drop_eq_nil_of_le (by simp; lia : loc.toList.length ≤ n1)]

theorem IntersectInvariant.eq {loc ivs : Array (Double × Double)} {n1 n2 : Nat}
    {out : Array (Double × Double)} (h : IntersectInvariant loc ivs true (n1, n2, out)) :
    out.toList = intersectList loc.toList ivs.toList := by
  simpa [h.2 rfl] using h.1

theorem IntersectInvariant.next {loc ivs : Array (Double × Double)} {n1 n2 : Nat}
    {out : Array (Double × Double)} (h : IntersectInvariant loc ivs false (n1, n2, out))
    (hx : n1 < loc.size ∧ n2 < ivs.size) :
    IntersectInvariant loc ivs false
      (if (meet loc[n1]! ivs[n2]!).2 then n1 + 1 else n1,
        if (meet loc[n1]! ivs[n2]!).2 then n2 else n2 + 1,
        match (meet loc[n1]! ivs[n2]!).1 with | some v => out.push v | none => out) := by
  refine ⟨?_, nofun⟩
  rw [← h.1, Array.drop_toList_eq_getElem!_cons hx.1, Array.drop_toList_eq_getElem!_cons hx.2,
    intersectList_cons_cons]
  rcases meet loc[n1]! ivs[n2]! with ⟨_ | v, _ | _⟩ <;>
    simp [Array.drop_toList_eq_getElem!_cons hx.1, Array.drop_toList_eq_getElem!_cons hx.2]

theorem IntersectInvariant.push_left {loc ivs : Array (Double × Double)} {n1 n2 : Nat}
    {out : Array (Double × Double)} (h : IntersectInvariant loc ivs false (n1, n2, out))
    (hx : n1 < loc.size ∧ n2 < ivs.size) {v : Double × Double}
    (hm : (meet loc[n1]! ivs[n2]!).fst = some v) (hs : (meet loc[n1]! ivs[n2]!).snd = true) :
    IntersectInvariant loc ivs false (n1 + 1, n2, out.push v) := by
  simpa [hm, hs] using h.next hx

theorem IntersectInvariant.push_right {loc ivs : Array (Double × Double)} {n1 n2 : Nat}
    {out : Array (Double × Double)} (h : IntersectInvariant loc ivs false (n1, n2, out))
    (hx : n1 < loc.size ∧ n2 < ivs.size) {v : Double × Double}
    (hm : (meet loc[n1]! ivs[n2]!).fst = some v) (hs : ¬(meet loc[n1]! ivs[n2]!).snd = true) :
    IntersectInvariant loc ivs false (n1, n2 + 1, out.push v) := by
  simpa [hm, hs] using h.next hx

theorem IntersectInvariant.skip_left {loc ivs : Array (Double × Double)} {n1 n2 : Nat}
    {out : Array (Double × Double)} (h : IntersectInvariant loc ivs false (n1, n2, out))
    (hx : n1 < loc.size ∧ n2 < ivs.size) {o : Option (Double × Double)}
    (ho : ∀ v, o = some v → False) (hm : (meet loc[n1]! ivs[n2]!).fst = o)
    (hs : (meet loc[n1]! ivs[n2]!).snd = true) :
    IntersectInvariant loc ivs false (n1 + 1, n2, out) := by
  cases o with
  | none => simpa [hm, hs] using h.next hx
  | some v => exact (ho v rfl).elim

theorem IntersectInvariant.skip_right {loc ivs : Array (Double × Double)} {n1 n2 : Nat}
    {out : Array (Double × Double)} (h : IntersectInvariant loc ivs false (n1, n2, out))
    (hx : n1 < loc.size ∧ n2 < ivs.size) {o : Option (Double × Double)}
    (ho : ∀ v, o = some v → False) (hm : (meet loc[n1]! ivs[n2]!).fst = o)
    (hs : ¬(meet loc[n1]! ivs[n2]!).snd = true) :
    IntersectInvariant loc ivs false (n1, n2 + 1, out) := by
  cases o with
  | none => simpa [hm, hs] using h.next hx
  | some v => exact (ho v rfl).elim

attribute [local irreducible] IntersectInvariant

/-- The loop ends since every pass moves one of the cursors. -/
@[spec]
theorem intersect_spec (loc ivs : Array (Double × Double)) :
    ⦃ True ⦄ intersect loc ivs ⦃ fun out ↦ out.toList = intersectList loc.toList ivs.toList ⦄ := by
  rw [intersect.eq_1]
  refine Std.WP.Triple.bind _ _ (IntersectInvariant loc ivs true) ?_ ?_
  · apply Std.WP.Triple.iff.mpr
    refine Std.WP.Triple.entails_wp_of_pre (Std.WP.Spec.forIn_loop
      (Std.WP.Variant.ofMeasure fun state ↦ loc.size + ivs.size - state.1 - state.2.1)
      (.mk (IntersectInvariant loc ivs)) Lean.Order.bot ?_) ?_
    · rintro ⟨leftIndex, rightIndex, output⟩ remaining
      dsimp only
      repeat' first
      | apply Std.WP.Triple.pure
        intro h
        vc_simp
        first
        | exact h.2.exit ‹_›
        | exact ⟨by lia, h.2.push_left ‹_› ‹_› ‹_›⟩
        | exact ⟨by lia, h.2.push_right ‹_› ‹_› ‹_›⟩
        | exact ⟨by lia, h.2.skip_left ‹_› ‹_› rfl ‹_›⟩
        | exact ⟨by lia, h.2.skip_right ‹_› ‹_› rfl ‹_›⟩
      | split
    · exact fun _ ↦ intersectInvariant_zero loc ivs
  · rintro ⟨leftIndex, rightIndex, output⟩
    apply Std.WP.Triple.pure
    exact fun h ↦ h.eq

/-- `Ratpoints.Sturm.intersect_spec` as a plain statement. -/
theorem toList_run_intersect (loc ivs : Array (Double × Double)) :
    (Id.run (intersect loc ivs)).toList = intersectList loc.toList ivs.toList :=
  Std.WP.Id.of_run_eq_wp rfl _ ((intersect_spec loc ivs).le_wp trivial)

/-! ### The Sturm step -/

/-- The Sturm step fails exactly when the remainder chain does: after the chain, the counts at
infinity, the bisection and the intersection always give intervals. -/
theorem run_computeSturm_eq_none_iff (c : List Int) (d iter : Nat)
    (ivlist : Array (Double × Double)) :
    Id.run (computeSturm c d iter ivlist) = none ↔ Id.run (chain c d) = none := by
  rcases h : Id.run (chain c d) with _ | rows
  · simp only [computeSturm, Id.run_bind, h, Id.run_pure]
  · simp only [computeSturm, Id.run_bind, h, reduceCtorEq, iff_false]
    split <;> simp

end Sturm

end Ratpoints

end
