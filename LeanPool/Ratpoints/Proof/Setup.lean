/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Squarefree.Basic
public import LeanPool.Ratpoints.Model.BruteForce
public import LeanPool.Ratpoints.Model.Candidate
public import LeanPool.Ratpoints.Model.Setup
public import LeanPool.Ratpoints.Proof.Sturm
public import LeanPool.Ratpoints.Spec.Basic

import Mathlib.Data.List.DropRight
import Mathlib.Data.List.GetD
import Mathlib.FieldTheory.Perfect
import LeanPool.Ratpoints.Mathlib.Data.Int.Sqrt
import LeanPool.Ratpoints.Mathlib.Data.List.Nodup
import LeanPool.Ratpoints.Mathlib.RingTheory.Coprime.Basic
import LeanPool.Ratpoints.Proof.BruteForce
import LeanPool.Ratpoints.Proof.Containers

/-!
# Coefficient polynomials, remainder chains, and reversal

`Ratpoints.poly` represents a list of integral coefficients as a polynomial over the rationals.
The signed remainder chain represents the polynomial and its derivative by arrays of integer
coefficients. The chain detects repeated factors, and consecutive nonzero rows have the signs
and relative degrees required by the Sturm sequence.

Reversing the list exchanges the two coordinates of the binary form. The reversal map preserves
the height and normalization of points, and the resulting correspondence applies to the
brute-force and fast searches.
-/

@[expose] public section

namespace Ratpoints

open Polynomial

/-- The polynomial over `ℚ` with the coefficient list `c`, constant term first. -/
noncomputable def poly (c : List ℤ) : ℚ[X] :=
  ∑ i ∈ Finset.range c.length, C (c.getD i 0 : ℚ) * X ^ i

@[simp]
theorem coeff_poly (c : List ℤ) (i : ℕ) : (poly c).coeff i = c.getD i 0 := by
  simp only [poly, finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (not_lt.mp h), Int.cast_zero]

theorem getD_degree_ne_zero_of_pos {c : List ℤ} (h : 0 < degree c) : c.getD (degree c) 0 ≠ 0 := by
  have hd : degree c = (c.rdropWhile (· == 0)).length - 1 := by simp [degree_def, List.rdropWhile]
  have hne : c.rdropWhile (· == 0) ≠ [] := fun h0 ↦ by simp [hd, h0] at h
  have hlt : degree c < (c.rdropWhile (· == 0)).length := by lia
  have hp := List.rdropWhile_prefix (· == 0) c
  rw [List.getD_eq_getElem _ _ (hlt.trans_le hp.length_le), ← hp.getElem hlt]
  simpa [hd, List.getLast_eq_getElem] using List.rdropWhile_last_not _ _ hne

theorem natDegree_poly (c : List ℤ) : (poly c).natDegree = degree c := by
  refine le_antisymm (natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ ?_) ?_
  · rw [coeff_poly, getD_eq_zero_of_degree_lt hi, Int.cast_zero]
  · rcases (degree c).eq_zero_or_pos with h | h
    · simp [h]
    · exact le_natDegree_of_ne_zero (by simpa using getD_degree_ne_zero_of_pos h)

/-- The entries of `c` above its degree are zero, so dropping them does not change the polynomial
`Ratpoints.poly c`; with `n = d + 1` for the degree `d` of `c`, this turns the polynomial of
`Ratpoints.Sturm.run_chain_eq_none_iff` into `Ratpoints.poly c`. -/
theorem poly_take_of_degree_lt {c : List ℤ} {n : ℕ} (h : degree c < n) :
    poly (c.take n) = poly c := by
  ext i
  simp only [coeff_poly, List.getD_eq_getElem?_getD, List.getElem?_take]
  split_ifs with hi
  · rfl
  · rw [← List.getD_eq_getElem?_getD, getD_eq_zero_of_degree_lt (by lia)]
    simp

/-- The binary form of `c` at `(a, b)`, `b ≠ 0`, is `b ^ D` times the value of the polynomial of
`c` at `a / b`, `D = d + d % 2` its even degree. -/
theorem binaryForm_eq_mul_eval {c : List ℤ} (a : ℤ) {b : ℤ} (hb : b ≠ 0) :
    (binaryForm c a b : ℚ) =
      (b : ℚ) ^ (degree c + degree c % 2) * (poly c).eval ((a : ℚ) / b) := by
  have hb' : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
  rw [binaryForm, eval_eq_sum_range, natDegree_poly, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [coeff_poly, show degree c + degree c % 2 = degree c + degree c % 2 - i + i by
    simp at hi; lia, pow_add, Nat.add_sub_cancel, div_pow]
  field

/-! ### The polynomial of an array -/

theorem coeff_poly_toList (a : Array ℤ) (i : ℕ) : (poly a.toList).coeff i = a[i]! := by
  simp [Array.getElem!_eq_getD]

theorem natDegree_poly_toList {a : Array ℤ} (h : a.back! ≠ 0) :
    (poly a.toList).natDegree = a.size - 1 := by
  refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ ?_) ?_
  · rw [coeff_poly_toList, getElem!_neg a i (by lia)]
    simp
  · rw [coeff_poly_toList, ← Array.back!_eq_getElem!]
    exact Int.cast_ne_zero.mpr h

theorem leadingCoeff_poly_toList {a : Array ℤ} (h : a.back! ≠ 0) :
    (poly a.toList).leadingCoeff = a.back! := by
  rw [leadingCoeff, natDegree_poly_toList h, coeff_poly_toList, Array.back!_eq_getElem!]

private theorem poly_toList_eq_zero_of_size_eq_zero {a : Array ℤ} (h : a.size = 0) :
    poly a.toList = 0 := by
  simp [poly, h]

-- The scaled subtraction of a reduction step, from its coefficients.
private theorem poly_toList_eq_C_mul_sub_C_mul_X_pow_mul {t a b : Array ℤ} {w v : ℤ} {e : ℕ}
    (h : ∀ i, t[i]! = w * a[i]! - v * if e ≤ i then b[i - e]! else 0) :
    poly t.toList = C (w : ℚ) * poly a.toList - C (v : ℚ) * X ^ e * poly b.toList :=
  AddMonoidAlgebra.ext <| Finsupp.ext fun i ↦ by
    rw [coeff_poly_toList, h, coeff_sub, coeff_C_mul, mul_assoc, coeff_C_mul, coeff_X_pow_mul',
      coeff_poly_toList, coeff_poly_toList]
    split_ifs <;> simp

-- The constant polynomial of an integer other than `0` is a unit over `ℚ`.
private theorem isUnit_C_intCast {A : ℤ} (h : A ≠ 0) : IsUnit (C (A : ℚ)) :=
  isUnit_C.mpr (Int.cast_ne_zero.mpr h).isUnit

-- A constant other than `0` is coprime to every polynomial.
private theorem isCoprime_poly_toList_of_size_eq_one {a : Array ℤ} (h1 : a.size = 1)
    (h : a.back! ≠ 0) (p : ℚ[X]) : IsCoprime p (poly a.toList) := by
  rw [eq_C_of_natDegree_eq_zero (p := poly a.toList) (by rw [natDegree_poly_toList h, h1]),
    coeff_poly_toList]
  rw [Array.back!_eq_getElem!, h1] at h
  exact isCoprime_one_right.of_isCoprime_of_dvd_right (isUnit_C_intCast h).dvd

namespace Sturm

/-! ### The steps of the chain as polynomials -/

private theorem exists_poly_reduceOnce {s t : Array ℤ} (hle : s.size ≤ t.size)
    (hs : s.back! ≠ 0) :
    ∃ u v : ℤ, 0 < u ∧ poly (reduceOnce s t).toList =
      C (u : ℚ) * poly t.toList - C (v : ℚ) * X ^ (t.size - s.size) * poly s.toList := by
  obtain ⟨u, v, hu, h⟩ := exists_getElem!_reduceOnce hle hs
  exact ⟨u, v, hu, poly_toList_eq_C_mul_sub_C_mul_X_pow_mul h⟩

-- The full reduction of `t` by `s` is `A t - Q s` with an integer `A > 0`.
private theorem exists_poly_fullReduce {s : Array ℤ} (hs : s.back! ≠ 0) (t : Array ℤ) :
    ∃ A : ℤ, 0 < A ∧ ∃ Q : ℚ[X],
      poly (fullReduce s t).toList = C (A : ℚ) * poly t.toList - Q * poly s.toList := by
  fun_induction fullReduce s t with
  | case1 t hle h0 =>
    obtain ⟨u, v, hu, h⟩ := exists_poly_reduceOnce hle hs
    rw [poly_toList_eq_zero_of_size_eq_zero h0] at h
    exact ⟨u, hu, C (v : ℚ) * X ^ (t.size - s.size), by
      rw [poly_toList_eq_zero_of_size_eq_zero rfl, h]⟩
  | case2 t hle _ ih =>
    obtain ⟨A, hA, Q, hQ⟩ := ih
    obtain ⟨u, v, hu, h⟩ := exists_poly_reduceOnce hle hs
    refine ⟨A * u, Int.mul_pos hA hu, C (A : ℚ) * C (v : ℚ) * X ^ (t.size - s.size) + Q, ?_⟩
    rw [hQ, h, Int.cast_mul, C_mul]
    ring
  | case3 => exact ⟨1, Int.one_pos, 0, by simp⟩

-- `g` times the normalized remainder is `-t`, for the gcd `g` of the entries of `-t`.
private theorem mul_poly_normalize (t : Array ℤ) :
    C ((content (t.map Neg.neg) : ℤ) : ℚ) * poly (normalize t).toList = -poly t.toList :=
  AddMonoidAlgebra.ext <| Finsupp.ext fun i ↦ by
    rw [coeff_C_mul, coeff_poly_toList, coeff_neg, coeff_poly_toList, ← Int.cast_mul,
      mul_getElem!_normalize, Int.cast_neg]

-- A full reduction that leaves nothing: `s`, not constant, divides `t`.
private theorem not_isCoprime_of_fullReduce_eq_empty {s t : Array ℤ} (hs : s.back! ≠ 0)
    (h2 : 2 ≤ s.size) (h : fullReduce s t = #[]) :
    ¬ IsCoprime (poly t.toList) (poly s.toList) := fun hc ↦ by
  obtain ⟨A, hA, Q, hQ⟩ := exists_poly_fullReduce hs t
  rw [h, poly_toList_eq_zero_of_size_eq_zero rfl, eq_comm, sub_eq_zero] at hQ
  have hu := hc.isUnit_of_dvd' ((isUnit_C_intCast hA.ne').dvd_mul_left.mp
    ⟨Q, by rw [hQ, mul_comm]⟩) dvd_rfl
  have := natDegree_eq_zero_of_isUnit hu
  rw [natDegree_poly_toList hs] at this
  lia

/-! ### Remainder chains -/

theorem IsChain.poly_toList_getElem!_zero {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)}
    (h : IsChain c d ch) : poly ch[0]!.toList = poly (c.take (d + 1)) :=
  AddMonoidAlgebra.ext <| Finsupp.ext fun i ↦ by
    rw [coeff_poly_toList, h.getElem!_zero, coeff_poly, List.getD_eq_getElem?_getD,
      List.getElem?_take]
    split_ifs with hi
    · rw [Array.getElem!_map_range _ hi, List.getD_eq_getElem?_getD]
    · rw [getElem!_neg _ i (by simpa using hi)]
      simp

theorem IsChain.poly_toList_getElem!_one {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)}
    (h : IsChain c d ch) : poly ch[1]!.toList = derivative (poly ch[0]!.toList) :=
  AddMonoidAlgebra.ext <| Finsupp.ext fun n ↦ by
    rw [coeff_derivative, coeff_poly_toList, coeff_poly_toList, h.getElem!_zero, h.getElem!_one]
    by_cases hn : n < d
    · rw [Array.getElem!_map_range _ hn, Array.getElem!_map_range _ (by lia)]
      push_cast
      ring
    · rw [getElem!_neg _ n (by simpa using hn), getElem!_neg _ (n + 1) (by simpa using hn)]
      simp

/-- Three consecutive rows `s_k`, `s_(k+1)`, `s_(k+2)` of a remainder chain satisfy
`A s_k = Q s_(k+1) - g s_(k+2)` with integers `A, g > 0`, the relation of a generalized Sturm
sequence; compare Mathlib's `Polynomial.sturmSeq`, which has `A = g = 1` and `Q` the quotient
(`Polynomial.sturmSeq_cons`): the integer factors keep the rows integral, and the rows are positive
rational multiples of its entries. -/
theorem IsChain.exists_mul_eq {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)} (h : IsChain c d ch)
    {k : ℕ} (hk : k + 2 < ch.size) :
    ∃ A g : ℤ, 0 < A ∧ 0 < g ∧ ∃ Q : ℚ[X], C (A : ℚ) * poly ch[k]!.toList =
      Q * poly ch[k + 1]!.toList - C (g : ℚ) * poly ch[k + 2]!.toList := by
  obtain ⟨A, hA, Q, hQ⟩ := exists_poly_fullReduce (h.back!_ne_zero (k + 1) (by lia)) ch[k]!
  have h2 := h.back!_ne_zero (k + 2) hk
  rw [h.getElem!_add_two k hk] at h2 ⊢
  refine ⟨A, _, hA, Int.natCast_pos.mpr (Nat.pos_of_ne_zero (content_map_neg_ne_zero h2)), Q, ?_⟩
  rw [mul_poly_normalize, hQ]
  ring

theorem IsChain.natDegree_lt {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)} (h : IsChain c d ch)
    {k : ℕ} (hk : k + 2 < ch.size) :
    (poly ch[k + 2]!.toList).natDegree < (poly ch[k + 1]!.toList).natDegree := by
  rw [natDegree_poly_toList (h.back!_ne_zero _ hk),
    natDegree_poly_toList (h.back!_ne_zero _ (by lia))]
  lia [h.size_lt k hk, Array.size_ne_zero_of_back!_ne (h.back!_ne_zero _ hk)]

-- Coprimality goes down a remainder chain.
private theorem IsChain.isCoprime_iff {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)}
    (h : IsChain c d ch) {k : ℕ} (hk : k + 1 < ch.size) :
    IsCoprime (poly ch[k]!.toList) (poly ch[k + 1]!.toList) ↔
      IsCoprime (poly ch[0]!.toList) (poly ch[1]!.toList) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨A, g, hA, hg, Q, hQ⟩ := h.exists_mul_eq (k := k) hk
    rw [isCoprime_iff_of_mul_eq_mul_sub_mul (isUnit_C_intCast hA.ne') (isUnit_C_intCast hg.ne') hQ]
    exact ih (by lia)

-- `f` is squarefree exactly when the last two rows of a chain of `f` are coprime.
private theorem IsChain.squarefree_iff_isCoprime_back! {c : List ℤ} {d : ℕ}
    {ch : Array (Array ℤ)} (h : IsChain c d ch) :
    Squarefree (poly (c.take (d + 1))) ↔
      IsCoprime (poly ch[ch.size - 2]!.toList) (poly ch.back!.toList) := by
  have := h.two_le_size
  rw [← h.poly_toList_getElem!_zero, ← PerfectField.separable_iff_squarefree, separable_def,
    ← h.poly_toList_getElem!_one, Array.back!_eq_getElem!,
    show ch.size - 1 = ch.size - 2 + 1 by lia, h.isCoprime_iff (k := ch.size - 2) (by lia)]

-- The last row of a chain has a nonzero leading coefficient.
private theorem IsChain.back!_back!_ne_zero {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)}
    (h : IsChain c d ch) : ch.back!.back! ≠ 0 :=
  h.back!_ne_zero _ (by lia [h.two_le_size])

/-- For the coefficients `c₀, …, c_d` of a polynomial `f` of degree `d ≥ 1`, the remainder chain is
`none`, where `sturm.c` returns `-1`, exactly when `f` is not squarefree over `ℚ`; for the degree
`d` of `c`, `f` is `Ratpoints.poly c` (`Ratpoints.poly_take_of_degree_lt`). -/
theorem run_chain_eq_none_iff {c : List ℤ} {d : ℕ} (hd : 1 ≤ d) (hc : c.getD d 0 ≠ 0) :
    Id.run (chain c d) = none ↔ ¬ Squarefree (poly (c.take (d + 1))) := by
  have hres := isChainResult_run_chain hd hc
  generalize Id.run (chain c d) = res at hres ⊢
  cases res with
  | none =>
    obtain ⟨ch, h, h2, h0⟩ := hres
    rw [h.squarefree_iff_isCoprime_back!]
    exact iff_of_true rfl (not_isCoprime_of_fullReduce_eq_empty h.back!_back!_ne_zero h2 h0)
  | some ch =>
    obtain ⟨h, h1⟩ := hres
    rw [h.squarefree_iff_isCoprime_back!]
    exact iff_of_false (Option.some_ne_none ch)
      (not_not.mpr (isCoprime_poly_toList_of_size_eq_one h1 h.back!_back!_ne_zero _))

end Sturm

/-! ### The reversal -/

-- `a` followed by the reversal of the entries `1, …, n` of `l`, for
-- `n < l.length`.
private theorem _root_.List.getD_cons_reverse_drop_take_of_lt {α : Type*} {l : List α} {n : ℕ}
    (h : n < l.length) (a : α) (i : ℕ) (x : α) :
    (a :: ((l.take (n + 1)).drop 1).reverse).getD i x =
      if i = 0 then a else if i ≤ n then l.getD (n + 1 - i) x else x := by
  cases i <;> grind

-- The degree of `c` from its entries: nonzero at `d` and zero above.
private theorem degree_eq_of_getD_ne_zero {c : List ℤ} {d : ℕ} (hd : c.getD d 0 ≠ 0)
    (h : ∀ i > d, c.getD i 0 = 0) : degree c = d := by
  rw [← natDegree_poly]
  refine natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ by rw [coeff_poly, h i hi, Int.cast_zero])
    (by rwa [coeff_poly, Int.cast_ne_zero])

-- The binary form as a sum over the range up to any bound `M ≥ degree c`.
private theorem binaryForm_eq_sum_range {c : List ℤ} {M : ℕ} (hM : degree c ≤ M) (x z : ℤ) :
    binaryForm c x z =
      ∑ i ∈ Finset.range (M + 1), c.getD i 0 * x ^ i * z ^ (degree c + degree c % 2 - i) := by
  rw [binaryForm]
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by lia)) fun i _ hi ↦ ?_
  rw [getD_eq_zero_of_degree_lt (by simp at hi; lia)]
  simp

/-- Two lists whose degrees round up to the same even number `N` and whose entries are reflected at
`N` have binary forms with `x` and `z` exchanged. -/
theorem binaryForm_eq_of_getD_eq_getD_sub {c c' : List ℤ} {N : ℕ}
    (hN : degree c + degree c % 2 = N) (hN' : degree c' + degree c' % 2 = N)
    (h : ∀ i ≤ N, c'.getD i 0 = c.getD (N - i) 0) (x z : ℤ) :
    binaryForm c' x z = binaryForm c z x := by
  rw [binaryForm_eq_sum_range (M := N) (by lia), hN', binaryForm_eq_sum_range (M := N) (by lia),
    hN, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi := Finset.mem_range.mp hi
  rw [h _ (by lia), Nat.add_sub_cancel, Nat.sub_sub_self (by lia)]
  ring

-- The binary form has the even degree `degree c + degree c % 2`, so `F(-x, -z) = F(x, z)`.
private theorem binaryForm_neg_neg (c : List ℤ) (x z : ℤ) :
    binaryForm c (-x) (-z) = binaryForm c x z := by
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have h1 : (-1 : ℤ) ^ i * (-1) ^ (degree c + degree c % 2 - i) = 1 := by
    rw [← pow_add, Nat.add_sub_cancel' (by lia [Finset.mem_range.mp hi]),
      Even.neg_one_pow (by rw [Nat.even_iff]; lia)]
  rw [neg_pow x, neg_pow z]
  linear_combination c.getD i 0 * x ^ i * z ^ (degree c + degree c % 2 - i) * h1

namespace Setup

/-- The square test of the set-up, as GMP decides it, is `IsSquare`. -/
theorem isSquare_eq_true_iff (a : ℤ) : isSquare a = true ↔ IsSquare a := by
  simp only [isSquare, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  rw [← Int.sqrt_mul_self_eq_iff, ← Int.exists_mul_self]
  exact exists_congr fun _ ↦ eq_comm

theorem isSquare_eq_false_iff (a : ℤ) : isSquare a = false ↔ ¬IsSquare a := by
  rw [← Bool.not_eq_true, isSquare_eq_true_iff]

@[simp]
theorem reversal_false (c : List ℤ) (d : ℕ) : reversal false c d = .ok (c, d, false) := rfl

/-- In each of the three cases of the reversal check `Ratpoints.Setup.reversal`, the reversed list
is the reflection of `c` in the even degree `d + d % 2` of the binary form (with `c_(d+1) = 0` in
its third case, of odd `d`). -/
theorem getD_eq_of_reversal_eq_ok {allow : Bool} {c c' : List ℤ} {d' : ℕ}
    (h : reversal allow c (degree c) = .ok (c', d', true)) (i : ℕ) :
    c'.getD i 0 =
      if i ≤ degree c + degree c % 2 then c.getD (degree c + degree c % 2 - i) 0 else 0 := by
  generalize hd : degree c = d at h ⊢
  obtain rfl | hc := eq_or_ne c []
  · cases allow <;> simp [reversal, ← hd] at h
  have hlt : d < c.length := by lia [degree_le_length_sub_one c, List.length_pos_iff.mpr hc]
  simp only [reversal] at h
  split_ifs at h with hs h2 h0 h1 hsq hodd <;>
    simp only [Except.ok.injEq, Prod.mk.injEq, Bool.false_eq_true, and_false] at h <;>
    obtain ⟨rfl, rfl, -⟩ := h
  · grind
  · grind
  · have : c.getD (d + 1) 0 = 0 := getD_eq_zero_of_degree_lt (by lia)
    rw [List.getD_cons_reverse_drop_take_of_lt hlt]
    grind

theorem eq_of_reversal_eq_ok_false {allow : Bool} {c c' : List ℤ} {d d' : ℕ}
    (h : reversal allow c d = .ok (c', d', false)) : c' = c ∧ d' = d := by
  simp only [reversal] at h
  split_ifs at h <;> simp_all

-- The cases that reverse: `c₀ = 0`, `c₁ ≠ 0` and the degree `D - 1` (cases 1 and 3), or `c₀ ≠ 0`,
-- even `d` and the degree `d` (case 2).
private theorem reversal_eq_ok_cases {allow : Bool} {c c' : List ℤ} {d' : ℕ}
    (h : reversal allow c (degree c) = .ok (c', d', true)) :
    c.getD 0 0 = 0 ∧ c.getD 1 0 ≠ 0 ∧ d' + 1 = degree c + degree c % 2 ∨
      c.getD 0 0 ≠ 0 ∧ d' = degree c ∧ degree c % 2 = 0 := by
  generalize hd : degree c = d at h ⊢
  simp only [reversal] at h
  split_ifs at h with hs h2 h0 h1 hsq hodd <;>
    simp only [Except.ok.injEq, Prod.mk.injEq, Bool.false_eq_true, and_false] at h <;>
    obtain ⟨rfl, rfl, -⟩ := h
  · have : 1 ≤ d := Nat.pos_of_ne_zero fun h0 ↦ h1 (getD_eq_zero_of_degree_lt (by lia))
    exact .inl ⟨h0, h1, by lia⟩
  · exact .inr ⟨h0, rfl, h2⟩
  · exact .inl ⟨hodd.2.1, fun h ↦ absurd (h ▸ hodd.2.2) (by decide), by lia⟩

/-- The new leading coefficient of a reversal by `Ratpoints.Setup.reversal`, `c₁` when `c₀ = 0` and
`c₀` otherwise, is not zero, so the degree that the check returns is that of its list, also without
a reversal. -/
theorem degree_eq_of_reversal_eq_ok {allow rev : Bool} {c c' : List ℤ} {d' : ℕ}
    (h : reversal allow c (degree c) = .ok (c', d', rev)) : degree c' = d' := by
  cases rev
  · obtain ⟨rfl, rfl⟩ := eq_of_reversal_eq_ok_false h
    rfl
  have hc' := getD_eq_of_reversal_eq_ok h
  rcases reversal_eq_ok_cases h with ⟨h0, h1, hN⟩ | ⟨h0, rfl, h2⟩ <;>
    refine degree_eq_of_getD_ne_zero ?_ fun i hi ↦ ?_ <;> rw [hc'] <;> grind

/-- The reversal check `Ratpoints.Setup.reversal` keeps the degree at least `1`: it lowers only an
even degree `d ≥ 2`, to `d - 1`, when `c₀ = 0`, and keeps it otherwise. -/
theorem one_le_of_reversal_eq_ok {allow rev : Bool} {c c' : List ℤ} {d d' : ℕ}
    (h : reversal allow c d = .ok (c', d', rev)) (h1 : 1 ≤ d) : 1 ≤ d' := by
  simp only [reversal] at h
  split_ifs at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;> lia

/-- The reversal check `Ratpoints.Setup.reversal` does not raise the degree: it lowers only an even
degree `d ≥ 2`, to `d - 1`, when `c₀ = 0`, and keeps it otherwise. -/
theorem degree_le_of_reversal_eq_ok {allow rev : Bool} {c c' : List ℤ} {d d' : ℕ}
    (h : reversal allow c d = .ok (c', d', rev)) : d' ≤ d := by
  simp only [reversal] at h
  split_ifs at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;> lia

-- The binary form of the reversed list has the even degree `d + d % 2` of that of `c`.
private theorem add_mod_two_eq_of_reversal_eq_ok {allow : Bool} {c c' : List ℤ} {d' : ℕ}
    (h : reversal allow c (degree c) = .ok (c', d', true)) :
    d' + d' % 2 = degree c + degree c % 2 := by
  rcases reversal_eq_ok_cases h with ⟨-, -, hN⟩ | ⟨-, rfl, -⟩ <;> lia

/-- The binary form of the reversed list is that of `c` with `x` and `z` exchanged, since the list
is the reflection of `c` in the even degree `d + d % 2` of the binary form. -/
theorem binaryForm_eq_of_reversal_eq_ok {allow : Bool} {c c' : List ℤ} {d' : ℕ}
    (h : reversal allow c (degree c) = .ok (c', d', true)) (x z : ℤ) :
    binaryForm c' x z = binaryForm c z x := by
  refine binaryForm_eq_of_getD_eq_getD_sub rfl
    (by rw [degree_eq_of_reversal_eq_ok h, add_mod_two_eq_of_reversal_eq_ok h]) (fun i hi ↦ ?_) x z
  rw [getD_eq_of_reversal_eq_ok h, ite_eq_left hi]

end Setup

/-! ### The map of a reversed search -/

namespace Sieve

/-- The map of the reversal is an involution on the triples `(x, y, z)` with `z > 0` or
`(x, z) = (1, 0)`, among them the normalized points. -/
theorem swapPoint_swapPoint {q : ℤ × ℤ × ℤ} (hn : 0 < q.2.2 ∨ q.2.2 = 0 ∧ q.1 = 1) :
    swapPoint (swapPoint q) = q := by
  obtain ⟨a, y, b⟩ := q
  dsimp only at hn
  simp only [swapPoint]
  split_ifs <;> simp_all <;> lia

/-- The map of the reversal is injective on the triples `(x, y, z)` with `z > 0` or
`(x, z) = (1, 0)` (`Ratpoints.Sieve.swapPoint_swapPoint`). -/
theorem swapPoint_inj {q q' : ℤ × ℤ × ℤ} (hn : 0 < q.2.2 ∨ q.2.2 = 0 ∧ q.1 = 1)
    (hn' : 0 < q'.2.2 ∨ q'.2.2 = 0 ∧ q'.1 = 1) :
    swapPoint q = swapPoint q' ↔ q = q' :=
  ⟨fun h ↦ by rw [← swapPoint_swapPoint hn, h, swapPoint_swapPoint hn'],
    fun h ↦ congr(swapPoint $h)⟩

end Sieve

/-- The map of the reversal keeps the pairs `(x, z)` of normalized points of height at most `H`:
it exchanges `x` and `z`, negating both for `x < 0`. -/
theorem IsNormalizedPair.swapPoint {H : ℕ} {q : ℤ × ℤ × ℤ} (h : IsNormalizedPair H q.1 q.2.2) :
    IsNormalizedPair H (Sieve.swapPoint q).1 (Sieve.swapPoint q).2.2 := by
  obtain ⟨a, y, b⟩ := q
  obtain ⟨hg, hn, ha, hb⟩ := h
  dsimp only at hg hn ha hb
  simp only [Sieve.swapPoint]
  split_ifs with h0
  · refine ⟨by rwa [Int.gcd_comm], ?_, by grind, by grind⟩
    rcases h0.lt_or_eq with h0 | rfl
    · exact .inl h0
    · rw [Int.gcd_zero_left] at hg
      exact .inr ⟨rfl, by lia⟩
  · exact ⟨by simpa [Int.gcd_comm] using hg, .inl (by lia), by grind, by grind⟩

namespace Sieve

/-- A point of a curve whose binary form is that of `c` with `x` and `z` exchanged gives a point of
the curve of `c`: since the degree of `Ratpoints.binaryForm` is even, `F(-x, -z) = F(x, z)`, and
the map keeps the normalized pairs (`Ratpoints.IsNormalizedPair.swapPoint`). -/
theorem isPoint_swapPoint {c c' : List ℤ} (hsw : ∀ x z, binaryForm c' x z = binaryForm c z x)
    {H : ℕ} {q : ℤ × ℤ × ℤ} (hq : IsPoint c' H q) : IsPoint c H (swapPoint q) := by
  refine ⟨?_, IsNormalizedPair.swapPoint hq.2⟩
  obtain ⟨a, y, b⟩ := q
  have hy : y ^ 2 = binaryForm c b a := hq.1.trans (hsw a b)
  simp only [swapPoint]
  split_ifs
  exacts [hy, by rwa [binaryForm_neg_neg]]

-- A list of the points of a curve whose binary form is that of `c` with `x` and `z` exchanged,
-- mapped by `Ratpoints.Sieve.swapPoint`, is a list of the points of `c`.
private theorem mem_map_swapPoint_iff {c c' : List ℤ}
    (hsw : ∀ x z, binaryForm c' x z = binaryForm c z x) {H : ℕ} {L : List (ℤ × ℤ × ℤ)}
    (hL : ∀ q, q ∈ L ↔ IsPoint c' H q) {p : ℤ × ℤ × ℤ} :
    p ∈ L.map swapPoint ↔ IsPoint c H p := by
  refine ⟨fun h ↦ ?_, fun h ↦ List.mem_map.mpr ⟨_, (hL _).mpr ?_, swapPoint_swapPoint h.2.2.1⟩⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    exact isPoint_swapPoint hsw ((hL q).mp hq)
  · exact isPoint_swapPoint (fun x z ↦ (hsw z x).symm) h

/-- The brute-force reference of a curve whose binary form is that of `c` with `x` and `z`
exchanged, mapped by `Ratpoints.Sieve.swapPoint`, is a permutation of the reference of `c`: the map
sends the points of the one curve one to one onto those of the other, and neither list has
duplicates. -/
theorem perm_map_swapPoint_bruteForce {c c' : List ℤ}
    (hsw : ∀ x z, binaryForm c' x z = binaryForm c z x) (H : ℕ) :
    ((bruteForce c' H).map swapPoint).Perm (bruteForce c H) :=
  List.perm_map_of_nodup (nodup_bruteForce c' H) (nodup_bruteForce c H)
    (fun x hx y hy ↦ (swapPoint_inj (mem_bruteForce_iff.mp hx).2.2.1
      (mem_bruteForce_iff.mp hy).2.2.1).mp)
    fun q ↦ by rw [mem_bruteForce_iff, ← List.mem_map, mem_map_swapPoint_iff hsw fun _ ↦
      mem_bruteForce_iff]

end Sieve

end Ratpoints

end
