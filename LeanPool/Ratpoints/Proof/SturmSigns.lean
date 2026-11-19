/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import LeanPool.Ratpoints.Mathlib.Algebra.Polynomial.Sturm.Sequence
public import LeanPool.Ratpoints.Proof.Setup
public import LeanPool.Ratpoints.Proof.SturmCounts

import Mathlib.Data.List.GetD
import LeanPool.Ratpoints.Mathlib.Algebra.Polynomial.FieldDivision
import LeanPool.Ratpoints.Mathlib.Analysis.Polynomial.Sturm
import LeanPool.Ratpoints.Mathlib.Basic.Sign.Defs
import LeanPool.Ratpoints.Mathlib.Data.List.SignVariations
import LeanPool.Ratpoints.Mathlib.FieldTheory.Perfect
import LeanPool.Ratpoints.Proof.Containers

/-!
# The signs of the chain of the Sturm step

The signs that the Sturm step computes, in the terms of Mathlib: the Horner value of
`Ratpoints.Sturm.evalSign` is `2 ^ (e deg)` times the value of the polynomial of the row at
`n / 2 ^ e` (`Ratpoints.Sturm.hornerValue_eq_eval`), so that `Ratpoints.Sturm.evalSign` computes its
sign (`Ratpoints.Sturm.run_evalSign_eq_sign_eval`); the count of `Ratpoints.Sturm.signsAt` at a
point where `f` and `f'` do not both vanish is the number of sign variations
(`List.signVariations`) of the signs of the rows there
(`Ratpoints.Sturm.run_signsAt_eq_signVariations`); and the counts of
`Ratpoints.Sturm.countsAtInfinity` are the numbers of sign variations of the signs of the leading
coefficients, negated for odd degree at `-∞`
(`Ratpoints.Sturm.run_countsAtInfinity_eq_signVariations`).

The rows of a chain whose last row is constant are, over `ℚ`, positive multiples of the entries of
Mathlib's `Polynomial.sturmSeq` of `f` and `f'`
(`Ratpoints.Sturm.IsChain.forall₂_posAssoc_sturmSeq`, from `Ratpoints.Sturm.IsChain.exists_mul_eq`),
and so over `ℝ`
(`Ratpoints.Sturm.IsChain.forall₂_posAssoc_sturmSeq_map`); hence, for a polynomial of degree
`d < 2 ^ 57` and the depths up to `55` of the Sturm step, `Ratpoints.Sturm.signsAt` computes the
signs of the real polynomial `f` and its derivative and the count `V` of Sturm's theorem
(`Ratpoints.Sturm.IsChain.run_signsAt_eq`), and `Ratpoints.Sturm.countsAtInfinity` the counts
`V(+∞)` and `V(-∞)` (`Ratpoints.Sturm.IsChain.run_countsAtInfinity_eq`).

## Main definitions

* `Ratpoints.Sturm.rowPolys`: the polynomials over `ℚ` of the rows of a chain.
* `Ratpoints.Sturm.chainPoly`: the real polynomial of a chain.

## Main statements

* `Ratpoints.Sturm.hornerValue_eq_eval`, `Ratpoints.Sturm.run_evalSign_eq_sign_eval`: the value and
  the sign of a row at a dyadic number.
* `Ratpoints.Sturm.signCount_eq_signVariations`,
  `Ratpoints.Sturm.ite_add_signCount_eq_signVariations`,
  `Ratpoints.Sturm.run_signsAt_eq_signVariations`: the count of the signs at a midpoint.
* `Ratpoints.Sturm.run_countsAtInfinity_eq_signVariations`: the counts at `±∞`.
* `Ratpoints.Sturm.IsChain.forall₂_posAssoc_sturmSeq_map`: the chain as the Sturm sequence over `ℝ`.
* `Ratpoints.Sturm.IsChain.run_signsAt_eq`, `Ratpoints.Sturm.IsChain.run_countsAtInfinity_eq`: the
  signs and counts of the Sturm step are those of the real polynomial.
-/

@[expose] public section

namespace Ratpoints

namespace Sturm

open Polynomial

/-- The Horner value after `j` steps, `∑ c_(deg - i) n ^ (j - i) 2 ^ (e i)` over `i ≤ j`. -/
theorem hornerValue_eq_sum (row : Array ℤ) (n : ℤ) (e j : ℕ) :
    hornerValue row n e j =
      ∑ i ∈ Finset.range (j + 1), row[row.size - 1 - i]! * n ^ (j - i) * 2 ^ (e * i) := by
  induction j with
  | zero => simp [hornerValue]
  | succ j ih =>
    rw [hornerValue, ih, Finset.sum_range_succ _ (j + 1), Finset.sum_mul,
      show row.size - 2 - j = row.size - 1 - (j + 1) by lia, Nat.sub_self, pow_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [show j + 1 - i = j - i + 1 by lia [Finset.mem_range.mp hi], pow_succ]
    ring

/-- The Horner value of `Ratpoints.Sturm.evalSign` is `2 ^ (e deg)` times the value of the
polynomial of the row at `n / 2 ^ e`. -/
theorem hornerValue_eq_eval (row : Array ℤ) (n : ℤ) (e : ℕ) (h : row.size ≠ 0) :
    (hornerValue row n e (row.size - 1) : ℚ) =
      2 ^ (e * (row.size - 1)) * (poly row.toList).eval ((n : ℚ) / 2 ^ e) := by
  rw [hornerValue_eq_sum, poly, eval_finsetSum, Finset.mul_sum, Array.length_toList,
    show row.size = row.size - 1 + 1 by lia, ← Finset.sum_range_reflect]
  push_cast
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi := Finset.mem_range.mp hi
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  rw [List.getD_eq_getElem _ _ (by simp; lia), Array.getElem_toList, ← getElem!_pos row _ (by lia),
    div_pow, show e * (row.size - 1) = e * (row.size - 1 - i) + e * i by
      rw [← Nat.mul_add]; congr 1; lia, pow_add, ← pow_mul,
    show row.size - 1 - (row.size - 1 - i) = i by lia]
  field

/-- `Ratpoints.Sturm.evalSign` computes the sign of the value of the polynomial of the row at
`num / 2 ^ denexp`. -/
theorem run_evalSign_eq_sign_eval {row : Array ℤ} (h : row.size ≠ 0) (num : Int64) {denexp : Int64}
    (h0 : 0 ≤ denexp.toInt) (hd : denexp.toInt * row.size < 2 ^ 63) :
    Id.run (evalSign row num denexp) =
      (SignType.sign ((poly row.toList).eval ((num.toInt : ℚ) / 2 ^ denexp.toInt.toNat)) : ℤ) := by
  rw [run_evalSign num h0 hd, Int.sign_eq_sign, ← sign_intCast (α := ℚ),
    hornerValue_eq_eval _ _ _ h, sign_mul, sign_pos (by positivity), one_mul]

/-- The sign changes that `Ratpoints.Sturm.signsAt` counts after a sign `s ≠ 0` in a list of signs
are the sign variations of `s` followed by the list. -/
theorem signCount_eq_signVariations {s : ℤ} (hs : s = -1 ∨ s = 1) {l : List ℤ}
    (hl : ∀ t ∈ l, t = -1 ∨ t = 0 ∨ t = 1) : signCount s l = (s :: l).signVariations := by
  induction l generalizing s with
  | nil => simp [signCount]
  | cons t l ih =>
    have hl' : ∀ t ∈ l, t = -1 ∨ t = 0 ∨ t = 1 := fun t ht ↦ hl t (by simp [ht])
    rcases hl t (by simp) with rfl | rfl | rfl <;> rcases hs with rfl | rfl <;>
      simp [signCount, ih (.inl rfl) hl', ih (.inr rfl) hl',
        List.signVariations_cons_cons_of_ne_zero]

/-- The count of `Ratpoints.Sturm.signsAt` from the signs `s0` and `s1` of `f` and `f'`, not both
zero, and the signs of the further rows: the sign variations of all of them. -/
theorem ite_add_signCount_eq_signVariations {s0 s1 : ℤ} (h0 : s0 = -1 ∨ s0 = 0 ∨ s0 = 1)
    (h1 : s1 = -1 ∨ s1 = 0 ∨ s1 = 1) (h01 : s0 ≠ 0 ∨ s1 ≠ 0) {l : List ℤ}
    (hl : ∀ t ∈ l, t = -1 ∨ t = 0 ∨ t = 1) :
    (if s0 * s1 = -1 then 1 else 0) + signCount (if s1 = 0 then s0 else s1) l =
      (s0 :: s1 :: l).signVariations := by
  rcases h0 with rfl | rfl | rfl <;> rcases h1 with rfl | rfl | rfl <;>
    simp_all [signCount_eq_signVariations, List.signVariations_cons_cons_of_ne_zero, add_comm]

/-- The counts of `Ratpoints.Sturm.countsAtInfinity` for rows with nonzero leading coefficients:
the sign variations of the signs of the rows `0, …, k` at `+∞` and at `-∞`. -/
theorem run_countsAtInfinity_eq_signVariations {rows : Array (Array ℤ)} {k : ℕ}
    (h : ∀ n ≤ k, rows[n]!.back! ≠ 0) :
    Id.run (countsAtInfinity rows k) = (((List.range (k + 1)).map (signAtTop rows)).signVariations,
      ((List.range (k + 1)).map (signAtBot rows)).signVariations) := by
  have ht (n : ℕ) (hn : n ≤ k) : signAtTop rows n = -1 ∨ signAtTop rows n = 1 := by
    have := h n hn
    rw [Array.back!_eq_getElem!] at this
    rcases Int.lt_or_gt_of_ne this with h' | h'
    · exact .inl (Int.sign_eq_neg_one_of_neg h')
    · exact .inr (Int.sign_eq_one_of_pos h')
  have hb (n : ℕ) (hn : n ≤ k) : signAtBot rows n = -1 ∨ signAtBot rows n = 1 := by
    simp only [signAtBot]; rcases ht n hn with h' | h' <;> split_ifs <;> simp [h']
  rw [run_countsAtInfinity, List.countP_ne_eq_signVariations ht,
    List.countP_ne_eq_signVariations hb]

/-- `Ratpoints.Sturm.evalSign` returns a sign. -/
theorem run_evalSign_eq_neg_one_or_eq_zero_or_eq_one (row : Array ℤ) (num denexp : Int64) :
    Id.run (evalSign row num denexp) = -1 ∨ Id.run (evalSign row num denexp) = 0 ∨
      Id.run (evalSign row num denexp) = 1 := by
  simp only [evalSign, Id.run_bind, Id.run_pure]
  exact (Int.sign_trichotomy _).elim (.inr ∘ .inr) (·.elim (.inr ∘ .inl) .inl)

/-- The count of `Ratpoints.Sturm.signsAt` at a point where `f` and `f'` do not both vanish is the
number of sign variations of the signs of the rows `0, …, k` of the chain there. -/
theorem run_signsAt_eq_signVariations {rows : Array (Array ℤ)} {k : ℕ} (hk : 1 ≤ k)
    {nm dem : Int64}
    (h01 : Id.run (evalSign rows[0]! nm dem) ≠ 0 ∨ Id.run (evalSign rows[1]! nm dem) ≠ 0) :
    Id.run (signsAt rows k nm dem) = (Id.run (evalSign rows[0]! nm dem),
      Id.run (evalSign rows[1]! nm dem),
      ((List.range (k + 1)).map fun n ↦ Id.run (evalSign rows[n]! nm dem)).signVariations) := by
  have hl : (List.range (k + 1)).map (fun n ↦ Id.run (evalSign rows[n]! nm dem)) =
      Id.run (evalSign rows[0]! nm dem) :: Id.run (evalSign rows[1]! nm dem) ::
        (List.range' 2 (k - 1)).map fun n ↦ Id.run (evalSign rows[n]! nm dem) := by
    rw [show k + 1 = k - 1 + 1 + 1 by lia, List.range_eq_range', List.range'_succ,
      List.range'_succ]
    rfl
  rw [run_signsAt, hl, ite_add_signCount_eq_signVariations
    (run_evalSign_eq_neg_one_or_eq_zero_or_eq_one ..)
    (run_evalSign_eq_neg_one_or_eq_zero_or_eq_one ..) h01 fun t ht ↦ ?_]
  obtain ⟨n, -, rfl⟩ := List.mem_map.mp ht
  exact run_evalSign_eq_neg_one_or_eq_zero_or_eq_one ..

/-! ### The chain as a Sturm sequence -/

theorem IsChain.poly_toList_ne_zero {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)}
    (h : IsChain c d ch) {i : ℕ} (hi : i < ch.size) : poly ch[i]!.toList ≠ 0 := fun h0 ↦ by
  have := coeff_poly_toList ch[i]! (ch[i]!.size - 1)
  rw [h0, coeff_zero, ← Array.back!_eq_getElem!, eq_comm, Int.cast_eq_zero] at this
  exact h.back!_ne_zero i hi this

/-- In a chain, the row `k + 2` is a positive multiple of the negated remainder of the row `k` by
the row `k + 1`, the entry of `Polynomial.sturmSeq` that follows them: by
`Ratpoints.Sturm.IsChain.exists_mul_eq`, `-s_k = (g / A) s_(k+2) - (Q / A) s_(k+1)`, where
`s_(k+2)` has the smaller degree. -/
theorem IsChain.posAssoc_neg_mod {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)} (h : IsChain c d ch)
    {k : ℕ} (hk : k + 2 < ch.size) :
    PosAssoc (-poly ch[k]!.toList % poly ch[k + 1]!.toList) (poly ch[k + 2]!.toList) := by
  obtain ⟨A, g, hA, hg, Q, hQ⟩ := h.exists_mul_eq hk
  have hA' : (A : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hA.ne'
  have heq : -poly ch[k]!.toList - C ((g : ℚ) / A) * poly ch[k + 2]!.toList =
      poly ch[k + 1]!.toList * -(C (A : ℚ)⁻¹ * Q) := by
    have hAC : C (A : ℚ)⁻¹ * C (A : ℚ) = 1 := by rw [← C_mul, inv_mul_cancel₀ hA', C_1]
    rw [div_eq_inv_mul, C_mul]
    linear_combination (-C (A : ℚ)⁻¹) * hQ + poly ch[k]!.toList * hAC
  refine PosAssoc.symm ⟨g / A, div_pos (Int.cast_pos.mpr hg) (Int.cast_pos.mpr hA), ?_⟩
  rw [mod_eq_of_dvd_sub (Dvd.intro _ heq.symm), C_mul_mod, (mod_eq_self_iff
    (h.poly_toList_ne_zero (by lia))).mpr (degree_lt_degree (h.natDegree_lt hk))]

/-- The polynomials over `ℚ` of the rows of a chain. -/
noncomputable abbrev rowPolys (ch : Array (Array ℤ)) : List ℚ[X] :=
  ch.toList.map fun r ↦ poly r.toList

theorem getElem_rowPolys (ch : Array (Array ℤ)) {i : ℕ} (hi : i < (rowPolys ch).length) :
    (rowPolys ch)[i] = poly ch[i]!.toList := by
  simp only [rowPolys, List.getElem_map, Array.getElem_toList]
  rw [getElem!_pos ch i (by simpa using hi)]

/-- The rows of a chain whose last row is constant are entrywise positive multiples of the entries
of the Sturm sequence of `f` and `f'`, over `ℚ`. -/
theorem IsChain.forall₂_posAssoc_sturmSeq {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)}
    (h : IsChain c d ch) (h1 : ch.back!.size = 1) :
    List.Forall₂ PosAssoc (rowPolys ch)
      (sturmSeq (poly (c.take (d + 1))) (derivative (poly (c.take (d + 1))))) := by
  have h2 := h.two_le_size
  rw [← h.poly_toList_getElem!_zero, ← h.poly_toList_getElem!_one,
    ← getElem_rowPolys ch (i := 0) (by simp; lia), ← getElem_rowPolys ch (i := 1) (by simp; lia)]
  refine forall₂_posAssoc_sturmSeq_of_getElem (by simpa using h2) (fun p hp ↦ ?_)
    (fun k hk ↦ ?_) ?_
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    exact getElem_rowPolys ch hi ▸ h.poly_toList_ne_zero (by simpa using hi)
  · simpa only [getElem_rowPolys] using h.posAssoc_neg_mod (by simpa using hk)
  · rw [List.getLast_eq_getElem, getElem_rowPolys, List.length_map, Array.length_toList,
      ← Array.back!_eq_getElem!]
    have hb := h.back!_ne_zero (ch.size - 1) (by lia)
    rw [← Array.back!_eq_getElem!] at hb
    rw [eq_C_of_natDegree_eq_zero (p := poly ch.back!.toList)
      (by rw [natDegree_poly_toList hb, h1]), coeff_poly_toList]
    exact isUnit_C.mpr (Int.cast_ne_zero.mpr (by rwa [Array.back!_eq_getElem!, h1] at hb)).isUnit

/-- The real polynomial of `c` that the chain of `c` and its degree `d` computes the remainder
chain of, the polynomial with the coefficients `c₀, …, c_d` over `ℝ`. -/
noncomputable abbrev chainPoly (c : List ℤ) (d : ℕ) : ℝ[X] :=
  (poly (c.take (d + 1))).map (Rat.castHom ℝ)

/-- The real polynomials of the rows of a chain whose last row is constant are entrywise positive
multiples of the entries of the Sturm sequence of `f` and `f'` over `ℝ`, the sequence of
`Ratpoints.SturmTheorem`. -/
theorem IsChain.forall₂_posAssoc_sturmSeq_map {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)}
    (h : IsChain c d ch) (h1 : ch.back!.size = 1) :
    List.Forall₂ PosAssoc ((rowPolys ch).map (map (Rat.castHom ℝ)))
      (sturmSeq (chainPoly c d) (derivative (chainPoly c d))) := by
  rw [derivative_map, sturmSeq_map]
  refine List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr ?_)
  exact (h.forall₂_posAssoc_sturmSeq h1).imp fun p q ⟨a, ha, hpq⟩ ↦
    ⟨a, mod_cast ha, by rw [← hpq, Polynomial.map_mul, map_C]; rfl⟩

/-- Every row of a chain has at most `d + 1` entries. -/
theorem IsChain.size_getElem!_le {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)} (h : IsChain c d ch)
    {n : ℕ} (hn : n < ch.size) : ch[n]!.size ≤ d + 1 := by
  rcases n with _ | n
  · simp [h.getElem!_zero]
  · lia [h.size_getElem!_add_one_add_le hn]

/-- `Ratpoints.Sturm.evalSign` computes the sign of the real polynomial of a row of a chain of a
polynomial of degree `d < 2 ^ 57` at `nm / 2 ^ dem` for `0 ≤ dem ≤ 55`, the depths of the Sturm
step, where the exponents stay within a `long`. -/
theorem IsChain.run_evalSign_eq {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)} (h : IsChain c d ch)
    (hd : d < 2 ^ 57) {n : ℕ} (hn : n < ch.size) (nm : Int64) {dem : Int64} (h0 : 0 ≤ dem.toInt)
    (h55 : dem.toInt ≤ 55) :
    Id.run (evalSign ch[n]! nm dem) = (SignType.sign (((poly ch[n]!.toList).map
      (Rat.castHom ℝ)).eval (((nm.toInt : ℚ) / 2 ^ dem.toInt.toNat : ℚ) : ℝ)) : ℤ) := by
  have hs := h.size_getElem!_le hn
  have hb : dem.toInt * ch[n]!.size < 2 ^ 63 := calc
    dem.toInt * ch[n]!.size ≤ 55 * ch[n]!.size := by gcongr
    _ < 2 ^ 63 := by lia
  rw [sign_eval_map_ratCastHom, run_evalSign_eq_sign_eval (Array.size_ne_zero_of_back!_ne
    (h.back!_ne_zero n hn)) nm h0 hb]

/-- Integer signs of the values of a map `g` at the real polynomials of the rows of a chain have the
sign variations of those values. -/
theorem signVariations_map_range_eq {ch : Array (Array ℤ)} {s : ℕ → ℤ} {g : ℝ[X] → ℝ}
    (hs : ∀ n < ch.size, s n = (SignType.sign (g ((poly ch[n]!.toList).map (Rat.castHom ℝ))) : ℤ)) :
    ((List.range ch.size).map s).signVariations =
      (((rowPolys ch).map (map (Rat.castHom ℝ))).map g).signVariations := by
  have hl : (List.range ch.size).map s =
      (((rowPolys ch).map (map (Rat.castHom ℝ))).map g).map fun y ↦ (SignType.sign y : ℤ) := by
    refine List.ext_getElem (by simp) fun n hn _ ↦ ?_
    rw [List.length_map, List.length_range] at hn
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    rw [← getElem!_pos ch n hn, hs n hn]
  rw [hl, List.signVariations_map (fun y ↦ by cases SignType.sign y <;> rfl)]

/-- The signs that `Ratpoints.Sturm.evalSign` computes for the rows of a chain whose last row is
constant, of a polynomial of degree `d < 2 ^ 57`, at `nm / 2 ^ dem` for `0 ≤ dem ≤ 55`, have the
sign variations of the Sturm sequence of the real polynomial there. -/
theorem IsChain.signVariations_run_evalSign {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)}
    (h : IsChain c d ch) (h1 : ch.back!.size = 1) (hd : d < 2 ^ 57) (nm : Int64) {dem : Int64}
    (h0 : 0 ≤ dem.toInt) (h55 : dem.toInt ≤ 55) :
    ((List.range ch.size).map fun n ↦ Id.run (evalSign ch[n]! nm dem)).signVariations =
      sturmV (chainPoly c d) (((nm.toInt : ℚ) / 2 ^ dem.toInt.toNat : ℚ) : ℝ) := by
  rw [signVariations_map_range_eq fun n hn ↦ h.run_evalSign_eq hd hn nm h0 h55]
  exact (signVariations_map_eval_eq_of_forall₂ (h.forall₂_posAssoc_sturmSeq_map h1) _).symm

/-- At `m = nm / 2 ^ dem`, `0 ≤ dem ≤ 55`, `Ratpoints.Sturm.signsAt` on a chain whose last row is
constant, of a polynomial of degree `d < 2 ^ 57` that is squarefree over `ℝ`, computes the signs of
`f(m)` and `f'(m)` and the count `V(m)` of the Sturm sequence over `ℝ`. -/
theorem IsChain.run_signsAt_eq {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)} (h : IsChain c d ch)
    (h1 : ch.back!.size = 1) (hd : d < 2 ^ 57) (hsq : Squarefree (chainPoly c d)) (nm : Int64)
    {dem : Int64} (h0 : 0 ≤ dem.toInt) (h55 : dem.toInt ≤ 55) :
    Id.run (signsAt ch (ch.size - 1) nm dem) =
      ((SignType.sign ((chainPoly c d).eval (((nm.toInt : ℚ) / 2 ^ dem.toInt.toNat : ℚ) : ℝ)) : ℤ),
        (SignType.sign ((derivative (chainPoly c d)).eval
          (((nm.toInt : ℚ) / 2 ^ dem.toInt.toNat : ℚ) : ℝ)) : ℤ),
        sturmV (chainPoly c d) (((nm.toInt : ℚ) / 2 ^ dem.toInt.toNat : ℚ) : ℝ)) := by
  have h2 := h.two_le_size
  have hσ0 := h.run_evalSign_eq hd (n := 0) (by lia) nm h0 h55
  have hσ1 := h.run_evalSign_eq hd (n := 1) (by lia) nm h0 h55
  rw [h.poly_toList_getElem!_zero] at hσ0
  rw [h.poly_toList_getElem!_one, h.poly_toList_getElem!_zero, ← derivative_map] at hσ1
  rw [run_signsAt_eq_signVariations (by lia) ?_, hσ0, hσ1, Nat.sub_add_cancel (by lia),
    h.signVariations_run_evalSign h1 hd nm h0 h55]
  rw [hσ0, hσ1]
  simpa using hsq.eval_ne_zero_or_eval_derivative_ne_zero _

/-- The sign of the leading coefficient of the real polynomial of a row of a chain is the sign of
the row at `+∞` of `Ratpoints.Sturm.countsAtInfinity`. -/
theorem IsChain.sign_leadingCoeff_map {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)}
    (h : IsChain c d ch) {n : ℕ} (hn : n < ch.size) :
    (SignType.sign ((poly ch[n]!.toList).map (Rat.castHom ℝ)).leadingCoeff : ℤ) =
      signAtTop ch n := by
  rw [leadingCoeff_map, leadingCoeff_poly_toList (h.back!_ne_zero n hn), signAtTop,
    ← Array.back!_eq_getElem!, Int.sign_eq_sign, Rat.coe_castHom, Rat.cast_intCast, sign_intCast]

/-- The sign at `-∞` of the real polynomial of a row of a chain, `(-1) ^ deg` times the sign of its
leading coefficient, is the sign of the row at `-∞` of `Ratpoints.Sturm.countsAtInfinity`. -/
theorem IsChain.sign_neg_one_pow_mul_leadingCoeff_map {c : List ℤ} {d : ℕ}
    {ch : Array (Array ℤ)} (h : IsChain c d ch) {n : ℕ} (hn : n < ch.size) :
    (SignType.sign ((-1) ^ ((poly ch[n]!.toList).map (Rat.castHom ℝ)).natDegree *
      ((poly ch[n]!.toList).map (Rat.castHom ℝ)).leadingCoeff) : ℤ) = signAtBot ch n := by
  rw [natDegree_map, natDegree_poly_toList (h.back!_ne_zero n hn), sign_mul, SignType.coe_mul,
    h.sign_leadingCoeff_map hn, signAtBot]
  rcases Nat.even_or_odd (ch[n]!.size - 1) with hk | hk
  · rw [hk.neg_one_pow, ite_eq_right (Nat.not_odd_iff_even.mpr hk ∘ Nat.odd_iff.mpr)]
    simp
  · rw [hk.neg_one_pow, ite_eq_left (Nat.odd_iff.mp hk)]
    simp

/-- For a chain whose last row is constant, the counts of `Ratpoints.Sturm.countsAtInfinity` are
the counts `V(+∞)` and `V(-∞)` of the Sturm sequence of the real polynomial. -/
theorem IsChain.run_countsAtInfinity_eq {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)}
    (h : IsChain c d ch) (h1 : ch.back!.size = 1) :
    Id.run (countsAtInfinity ch (ch.size - 1)) = (vTop (chainPoly c d), vBot (chainPoly c d)) := by
  have h2 := h.two_le_size
  rw [run_countsAtInfinity_eq_signVariations (fun n hn ↦ h.back!_ne_zero n (by lia)),
    Nat.sub_add_cancel (by lia), vTop, vBot,
    signVariations_map_leadingCoeff_eq_of_forall₂ (h.forall₂_posAssoc_sturmSeq_map h1),
    signVariations_map_neg_one_pow_mul_leadingCoeff_eq_of_forall₂
      (h.forall₂_posAssoc_sturmSeq_map h1),
    signVariations_map_range_eq fun n hn ↦ (h.sign_leadingCoeff_map hn).symm,
    signVariations_map_range_eq (g := fun p ↦ (-1) ^ p.natDegree * p.leadingCoeff)
      fun n hn ↦ (h.sign_neg_one_pow_mul_leadingCoeff_map hn).symm]

end Sturm

end Ratpoints

end
