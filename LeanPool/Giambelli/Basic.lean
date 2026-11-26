/-
Copyright (c) 2026 Paul-Olivier Dehaye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Olivier Dehaye
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Tactic.LinearCombination

/-!
# Giambelli's identity for an `(h, e)` pair

For a partition `λ` with Durfee square of side `d` and Frobenius coordinates
`λ = (α₀, …, α_{d−1} | β₀, …, β_{d−1})`, `α_i = λ_i − i − 1`, `β_j = λ′_j − j − 1`, Giambelli's
identity says `s_λ = det (s_{(α_i | β_j)})_{i, j < d}`, where `s_{(a | b)}` is the hook
`(a + 1, 1^b)`.

The identity is a consequence of the Jacobi–Trudi formula and of `H(X) E(−X) = 1` alone, so this
file proves it for any pair of symbols `h, e : ℤ → R` vanishing below `0`, with `e₀ = 1` and
`Σ_r (−1)^{N−r} h_r e_{N−r} = [N = 0]` (`Giambelli.HEPair`), for the Jacobi–Trudi determinant
`jt h λ = det (h_{λ_i − i + j})` (`Giambelli.giambelli_jt`).

## Proof

Multiply the Jacobi–Trudi matrix on the right by the unitriangular matrix
`E′ = ((−1)^{j+k} e_{k−j})_{j,k}`. Row `i` of the product depends only on `p = λ_i − i`:

* if `p ≤ 0` (`i ≥ d`) it is the unit row at column `−p = i − λ_i` (`rowF_of_nonpos`);
* if `p > 0` (`i < d`, `p = α_i + 1`) its entry in column `k` is `(−1)^k g(α_i, k)`, with
  `g(a, b) = Σ_{r ≤ a} (−1)^r h_{a−r} e_{b+1+r}` (`rowF_of_pos`).

The columns `i − λ_i` (`d ≤ i < n`) and `β_j` (`j < d`) partition `{0, …, n−1}` (Frobenius
complementarity, `frobB_ne`), so expanding along the unit rows leaves the `d × d` minor on the
columns `β_j` (`det_unitRows`). The signs cancel. Applied to a hook this gives
`jt (a | b) = g(a, b)` (`jt_hook`), hence Giambelli (`giambelli_jt'`).

## Main results

* `Giambelli.det_unitRows`: expanding a determinant along rows that are unit vectors.
* `Giambelli.det_submatrix_rev`: reversing the columns costs `(−1)^{n(n−1)/2}`.
* `Giambelli.giambelli_jt`, `Giambelli.jt_hook`, `Giambelli.giambelli_jt'`: Giambelli's identity
  for Jacobi–Trudi determinants of any `(h, e)` pair.
-/

@[expose] public section

open Finset Matrix

namespace Giambelli

variable {R : Type*} [CommRing R]

/-! ## Signs -/

/-- `(−1)^k` for `k ∈ ℤ`. -/
noncomputable def sg (R : Type*) [CommRing R] (k : ℤ) : R := (((Int.negOnePow k : ℤˣ) : ℤ) : R)

theorem sg_add (k l : ℤ) : sg R (k + l) = sg R k * sg R l := by
  simp [sg, Int.negOnePow_add]

theorem sg_neg (k : ℤ) : sg R (-k) = sg R k := by
  simp [sg, Int.negOnePow_neg]

theorem sg_sub (k l : ℤ) : sg R (k - l) = sg R k * sg R l := by
  rw [sub_eq_add_neg, sg_add, sg_neg]

theorem sg_natCast (n : ℕ) : sg R n = (-1) ^ n := by
  simp [sg]

theorem sg_two_mul (k : ℤ) : sg R (2 * k) = 1 := by
  simp [sg, Int.negOnePow_two_mul]

theorem sg_mul_self (k : ℤ) : sg R k * sg R k = 1 := by
  rw [← sg_add, ← two_mul, sg_two_mul]

/-! ## Expanding along unit rows -/

/-- **Expansion along unit rows.** Let the last `k` rows of `M` be unit rows, row `d + i` at
column `c_i` (`c` increasing), and let `b` enumerate the other columns increasingly. Then
`det M = (−1)^{Σ_j (b_j − j)} det (M_{i, b_j})_{i, j < d}`. -/
theorem det_unitRows {d : ℕ} : ∀ (k : ℕ) (M : Matrix (Fin (d + k)) (Fin (d + k)) R)
    (b : Fin d → Fin (d + k)) (c : Fin k → Fin (d + k)), StrictMono b → StrictMono c →
    (∀ j i, b j ≠ c i) → (∀ y, (∃ j, b j = y) ∨ (∃ i, c i = y)) →
    (∀ i y, M (Fin.natAdd d i) y = if y = c i then 1 else 0) →
    det M = sg R (∑ j, ((b j : ℤ) - j)) * det (of fun i j => M (Fin.castAdd k i) (b j))
  | 0, M, b, c, hb, hc, hbc, hcov, hM => by
    have hsurj : Function.Surjective b := fun y => by
      rcases hcov y with h | ⟨i, -⟩
      · exact h
      · exact i.elim0
    have hid : ∀ j, b j = j := by
      have := congrArg (fun f : Fin d ≃o Fin d => (f : Fin d → Fin d))
        (Subsingleton.elim (StrictMono.orderIsoOfSurjective b hb hsurj) (OrderIso.refl _))
      intro j
      exact congrFun this j
    have hsum : ∑ j : Fin d, ((b j : ℤ) - j) = 0 := sum_eq_zero fun j _ => by rw [hid j]; ring
    rw [hsum, sg, Int.negOnePow_zero]
    simp only [Units.val_one, Int.cast_one, one_mul]
    congr 1
    ext i j
    simp [hid j]
  | k + 1, M, b, c, hb, hc, hbc, hcov, hM => by
    set C := c (Fin.last k) with hC
    -- Laplace along the last row
    have hlast : (Fin.natAdd d (Fin.last k) : Fin (d + (k + 1))) = Fin.last (d + k) := by
      ext; simp
    have hexp : det M = (-1) ^ ((d + k : ℕ) + (C : ℕ)) *
        det (M.submatrix (Fin.last (d + k)).succAbove C.succAbove) := by
      refine (det_succ_row M (Fin.last (d + k))).trans ((Fintype.sum_eq_single C ?_).trans ?_)
      · intro y hy
        rw [← hlast, hM, ite_eq_right hy, mul_zero, zero_mul]
      · rw [← hlast, hM, ite_eq_left rfl, mul_one, hlast, Fin.val_last]
    -- the reduced data
    have hcC : ∀ i : Fin k, c i.castSucc < C := fun i => hc (Fin.castSucc_lt_last i)
    have hbC : ∀ j, b j ≠ C := fun j => hbc j _
    choose b' hb' using fun j => Fin.exists_succAbove_eq (hbC j)
    choose c' hc' using fun i : Fin k => Fin.exists_succAbove_eq (hcC i).ne
    have hb'm : StrictMono b' := fun j j' h => by
      have := hb h
      rw [← hb' j, ← hb' j'] at this
      exact (Fin.strictMono_succAbove C).lt_iff_lt.mp this
    have hc'm : StrictMono c' := fun i i' h => by
      have := hc (Fin.castSucc_lt_castSucc_iff.mpr h)
      rw [← hc' i, ← hc' i'] at this
      exact (Fin.strictMono_succAbove C).lt_iff_lt.mp this
    have hbc' : ∀ j i, b' j ≠ c' i := fun j i h => hbc j i.castSucc (by rw [← hb' j, ← hc' i, h])
    have hcov' : ∀ z, (∃ j, b' j = z) ∨ (∃ i, c' i = z) := by
      intro z
      rcases hcov (C.succAbove z) with ⟨j, hj⟩ | ⟨i, hi⟩
      · exact Or.inl ⟨j, Fin.succAbove_right_injective (by rw [hb' j, hj])⟩
      · refine Or.inr ?_
        rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
        · exact ⟨i', Fin.succAbove_right_injective (by rw [hc' i', hi])⟩
        · exact absurd hi.symm (Fin.succAbove_ne C z)
    set M' := M.submatrix (Fin.last (d + k)).succAbove C.succAbove with hM'def
    have hM' : ∀ i y, M' (Fin.natAdd d i) y = if y = c' i then 1 else 0 := by
      intro i y
      have hrow : (Fin.last (d + k)).succAbove (Fin.natAdd d i) = Fin.natAdd d i.castSucc := by
        rw [Fin.succAbove_last]; ext; simp
      simp only [hM'def, submatrix_apply, hrow, hM]
      congr 1
      exact propext ⟨fun h => Fin.succAbove_right_injective (h.trans (hc' i).symm),
        fun h => h ▸ hc' i⟩
    have IH := det_unitRows k M' b' c' hb'm hc'm hbc' hcov' hM'
    have hminor : (of fun i j => M' (Fin.castAdd k i) (b' j)) =
        of fun i j => M (Fin.castAdd (k + 1) i) (b j) := by
      ext i j
      simp only [hM'def, of_apply, submatrix_apply, hb' j, Fin.succAbove_last]
      congr 1
    -- the count of the columns above `C`
    have hcount : #{j | C < b j} = d + k - (C : ℕ) := by
      have : (univ.filter fun j => C < b j).map ⟨b, hb.injective⟩ = Finset.Ioi C := by
        ext y
        simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk,
          Finset.mem_Ioi]
        constructor
        · rintro ⟨j, hj, rfl⟩; exact hj
        · intro hy
          rcases hcov y with ⟨j, rfl⟩ | ⟨i, rfl⟩
          · exact ⟨j, hy, rfl⟩
          · exact absurd hy (not_lt.mpr (hc.monotone (Fin.le_last i)))
      rw [← card_map, this, Fin.card_Ioi]; omega
    have hval : ∀ j, ((b j : ℕ) : ℤ) = (b' j : ℕ) + if C < b j then 1 else 0 := by
      intro j
      rw [← hb' j]
      by_cases h : (b' j).castSucc < C
      · rw [Fin.succAbove_of_castSucc_lt _ _ h, ite_eq_right (not_lt.mpr h.le)]; simp
      · rw [not_lt] at h
        rw [Fin.succAbove_of_le_castSucc _ _ h, ite_eq_left (by
          rw [Fin.lt_def, Fin.val_succ]; rw [Fin.le_def, Fin.val_castSucc] at h; omega)]
        simp [Fin.val_succ]
    have hsum : ∑ j, ((b j : ℤ) - j) = ∑ j, ((b' j : ℤ) - j) + ((d + k : ℕ) - (C : ℕ) : ℤ) := by
      have hCle : (C : ℕ) ≤ d + k := Nat.lt_succ_iff.mp C.isLt
      rw [show ((d + k : ℕ) - (C : ℕ) : ℤ) = ((d + k - (C : ℕ) : ℕ) : ℤ) by push_cast [hCle]; ring,
        ← hcount, card_filter, Nat.cast_sum, ← sum_add_distrib]
      refine sum_congr rfl fun j _ => ?_
      rw [hval j]; split_ifs <;> push_cast <;> ring
    have hs : ((-1 : R) ^ (d + k + (C : ℕ))) = sg R (((d + k : ℕ) : ℤ) - ((C : ℕ) : ℤ)) := by
      rw [← sg_natCast, sg_sub,
        show (((d + k + (C : ℕ) : ℕ)) : ℤ) = ((d + k : ℕ) : ℤ) + ((C : ℕ) : ℤ) by
        push_cast; ring, sg_add]
    rw [hexp, IH, hminor, hsum, sg_add, hs]
    ring

/-- **Reversing the columns** multiplies the determinant by `(−1)^{n(n−1)/2} = (−1)^{Σ_{j<n} j}`. -/
theorem det_submatrix_rev : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) R),
    det (M.submatrix id Fin.rev) = sg R (∑ j : Fin n, (j : ℤ)) * det M
  | 0, M => by simp [sg]
  | n + 1, M => by
    rw [det_succ_column _ 0, det_succ_column M (Fin.last n),
      Fin.sum_univ_succ (f := fun j : Fin (n + 1) => (j : ℤ)),
      mul_sum]
    refine sum_congr rfl fun i _ => ?_
    have hsub : ((M.submatrix id Fin.rev).submatrix i.succAbove (0 : Fin (n + 1)).succAbove) =
        (M.submatrix i.succAbove (Fin.last n).succAbove).submatrix id Fin.rev := by
      ext a b
      simp only [submatrix_apply, id, Fin.succAbove_zero, Fin.succAbove_last]
      congr 1
      ext; simp [Fin.rev]
    rw [hsub, det_submatrix_rev n, submatrix_apply, id, Fin.rev_zero]
    simp only [Fin.val_zero, Fin.val_last, Fin.val_succ, Nat.cast_add, Nat.cast_one, add_zero,
      sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [← sg_natCast, ← sg_natCast, sg_add, sg_add (∑ j : Fin n, (j : ℤ))]
    have h0 : sg R ((0 : ℕ) : ℤ) = 1 := by simp [sg]
    rw [h0]
    simp only [Nat.cast_add, sg_add]
    linear_combination (-(sg R (i : ℕ) * M i (Fin.last n) * sg R (∑ j : Fin n, ((j : ℕ) : ℤ)) *
      det (M.submatrix i.succAbove (Fin.last n).succAbove))) * sg_mul_self (R := R) (n : ℤ)

theorem prod_sg {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, sg R (f i) = sg R (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sg]
  | insert x s hx ih => rw [prod_insert hx, sum_insert hx, sg_add, ih]

/-! ## Pairs of symbols `h, e` with `H(X) E(−X) = 1` -/

/-- Symbols `h, e : ℤ → R`, zero below `0`, with `e₀ = 1` and
`Σ_r (−1)^{N−r} h_r e_{N−r} = [N = 0]`. -/
structure HEPair (h e : ℤ → R) : Prop where
  /-- `h_k = 0` for `k < 0`. -/
  h_neg : ∀ k < 0, h k = 0
  /-- `e_k = 0` for `k < 0`. -/
  e_neg : ∀ k < 0, e k = 0
  /-- `e_0 = 1`. -/
  e_zero : e 0 = 1
  /-- `H(X) E(−X) = 1`. -/
  conv : ∀ N : ℕ, ∑ r ∈ range (N + 1), sg R ((N : ℤ) - r) * h r * e ((N : ℤ) - r) =
    if N = 0 then 1 else 0

/-- The Jacobi–Trudi determinant `det (h_{λ_i − i + j})_{i, j < n}`. -/
noncomputable def jt (h : ℤ → R) {n : ℕ} (lam : Fin n → ℕ) : R :=
  det (of fun i j : Fin n => h ((lam i : ℤ) - i + j))

/-- The hook symbol `g(a, b) = Σ_{r ≤ a} (−1)^r h_{a−r} e_{b+1+r}`. -/
noncomputable def hookV (h e : ℤ → R) (a b : ℕ) : R :=
  ∑ r ∈ range (a + 1), sg R r * h ((a : ℤ) - r) * e ((b : ℤ) + 1 + r)

/-- Entry `(p, k)` of `JT · E′`, for a row with `λ_i − i = p`. -/
noncomputable def rowF (h e : ℤ → R) (p : ℤ) (k : ℕ) : R :=
  ∑ j ∈ range (k + 1), h (p + j) * (sg R ((j : ℤ) + k) * e ((k : ℤ) - j))

variable {h e : ℤ → R}

/-- Rows below the Durfee square become unit rows. -/
theorem rowF_of_nonpos (hp : HEPair h e) {p : ℤ} (hp0 : p ≤ 0) (k : ℕ) :
    rowF h e p k = if (k : ℤ) = -p then 1 else 0 := by
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, p = -q := ⟨(-p).toNat, by omega⟩
  by_cases hk : q ≤ k
  · obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [rowF, show q + N + 1 = q + (N + 1) by ring, sum_range_add,
      sum_eq_zero (fun j hj => by rw [hp.h_neg _ (by simp at hj; omega), zero_mul]), zero_add]
    rw [if_congr (by push_cast; omega : ((q + N : ℕ) : ℤ) = -(-(q : ℤ)) ↔ N = 0) rfl rfl,
      ← hp.conv N]
    refine sum_congr rfl fun r _ => ?_
    have e1 : -(q : ℤ) + ((q + r : ℕ) : ℤ) = r := by push_cast; ring
    have e2 : ((q + N : ℕ) : ℤ) - ((q + r : ℕ) : ℤ) = (N : ℤ) - r := by push_cast; ring
    have e3 : sg R (((q + r : ℕ) : ℤ) + ((q + N : ℕ) : ℤ)) = sg R ((N : ℤ) - r) := by
      rw [show ((q + r : ℕ) : ℤ) + ((q + N : ℕ) : ℤ) = 2 * (q + r) + ((N : ℤ) - r) by
          push_cast; ring,
        sg_add, sg_two_mul, one_mul]
    rw [e1, e2, e3]; ring
  · rw [ite_eq_right (by omega)]
    exact sum_eq_zero fun j hj => by rw [hp.h_neg _ (by simp at hj; omega), zero_mul]

/-- Rows in the Durfee square: column `k` carries `(−1)^k g(a, k)`. -/
theorem rowF_of_pos (hp : HEPair h e) (a k : ℕ) :
    rowF h e ((a : ℤ) + 1) k = sg R k * hookV h e a k := by
  have hc := hp.conv (a + 1 + k)
  rw [ite_eq_right (by omega), show a + 1 + k + 1 = (a + 1) + (k + 1) by ring, sum_range_add,
    ← sum_range_reflect] at hc
  have h1 : ∑ s ∈ range (a + 1), sg R (((a + 1 + k : ℕ) : ℤ) - ((a + 1 - 1 - s : ℕ) : ℤ)) *
      h ((a + 1 - 1 - s : ℕ) : ℤ) * e (((a + 1 + k : ℕ) : ℤ) - ((a + 1 - 1 - s : ℕ) : ℤ)) =
      -(sg R k * hookV h e a k) := by
    rw [hookV, mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun s hs => ?_
    have hs' := mem_range.mp hs
    have c1 : ((a + 1 - 1 - s : ℕ) : ℤ) = (a : ℤ) - s := by omega
    have c2 : ((a + 1 + k : ℕ) : ℤ) - ((a : ℤ) - s) = (k : ℤ) + 1 + s := by push_cast; ring
    rw [c1, c2, sg_add, sg_add]
    have : sg R 1 = -1 := by simp [sg]
    rw [this]; ring
  have h2 : ∑ j ∈ range (k + 1), sg R (((a + 1 + k : ℕ) : ℤ) - ((a + 1 + j : ℕ) : ℤ)) *
      h ((a + 1 + j : ℕ) : ℤ) * e (((a + 1 + k : ℕ) : ℤ) - ((a + 1 + j : ℕ) : ℤ)) =
      rowF h e ((a : ℤ) + 1) k := by
    refine sum_congr rfl fun j _ => ?_
    have c1 : ((a + 1 + k : ℕ) : ℤ) - ((a + 1 + j : ℕ) : ℤ) = (k : ℤ) - j := by push_cast; ring
    have c2 : ((a + 1 + j : ℕ) : ℤ) = (a : ℤ) + 1 + j := by push_cast; ring
    rw [c1, c2, sg_sub, sg_add]; ring
  rw [h1, h2] at hc
  linear_combination hc

/-! ## Frobenius coordinates -/

section Frobenius

variable {n : ℕ} (lam : Fin n → ℕ)

/-- Row `i` of `λ`, `0` beyond `n`. -/
def rowL (i : ℕ) : ℕ := if hi : i < n then lam ⟨i, hi⟩ else 0

/-- Column `j` of `λ`: `λ′_j = #{i | j < λ_i}`. -/
def colL (j : ℕ) : ℕ := #{i | j < lam i}

/-- The side `d` of the Durfee square: `#{i | i < λ_i}`. -/
def durfee : ℕ := #{i : Fin n | (i : ℕ) < lam i}

/-- The arms `α_i = λ_i − i − 1`. -/
def frobA (i : ℕ) : ℕ := rowL lam i - i - 1

/-- The legs `β_j = λ′_j − j − 1`. -/
def frobB (j : ℕ) : ℕ := colL lam j - j - 1

variable {lam}

theorem rowL_fin (i : Fin n) : rowL lam i = lam i := by simp [rowL]

theorem durfee_le : durfee lam ≤ n := (card_filter_le _ _).trans (by simp)

/-- `i` is in the Durfee square iff `i < λ_i`. -/
theorem lt_durfee_iff (hl : Antitone lam) (i : ℕ) : i < durfee lam ↔ i < rowL lam i := by
  by_cases hi : i < n
  · rw [rowL, dite_eq_left hi]
    constructor
    · intro h
      by_contra hn
      have : durfee lam ≤ i := by
        calc durfee lam ≤ #(Iio (⟨i, hi⟩ : Fin n)) := card_le_card fun x hx => by
              simp only [mem_filter, mem_univ, true_and] at hx
              rw [mem_Iio]
              by_contra hge
              exact hn (lt_of_le_of_lt (not_lt.mp hge) (lt_of_lt_of_le hx (hl (not_lt.mp hge))))
          _ = i := by simp
      omega
    · intro h
      calc i < #(Iic (⟨i, hi⟩ : Fin n)) := by simp
        _ ≤ durfee lam := card_le_card fun x hx => by
              simp only [mem_filter, mem_univ, true_and]
              have hx' : x ≤ ⟨i, hi⟩ := mem_Iic.mp hx
              exact lt_of_le_of_lt hx' (lt_of_lt_of_le h (hl hx'))
  · rw [rowL, dite_eq_right hi]
    have := durfee_le (lam := lam)
    omega

theorem le_colL (hl : Antitone lam) {j x : ℕ} (hx : x < n) (h : j < rowL lam x) :
    x + 1 ≤ colL lam j := by
  rw [rowL, dite_eq_left hx] at h
  calc x + 1 = #(Iic (⟨x, hx⟩ : Fin n)) := by simp
    _ ≤ _ := card_le_card fun i hi => by
        simp only [mem_filter, mem_univ, true_and]
        exact lt_of_lt_of_le h (hl (mem_Iic.mp hi))

theorem colL_le (hl : Antitone lam) {j x : ℕ} (hx : x < n) (h : rowL lam x ≤ j) :
    colL lam j ≤ x := by
  rw [rowL, dite_eq_left hx] at h
  calc colL lam j ≤ #(Iio (⟨x, hx⟩ : Fin n)) := card_le_card fun i hi => by
        simp only [mem_filter, mem_univ, true_and] at hi
        rw [mem_Iio]
        by_contra hge
        exact absurd (lt_of_lt_of_le hi (hl (not_lt.mp hge))) (by omega)
    _ = x := by simp

theorem colL_le_n (j : ℕ) : colL lam j ≤ n := (card_filter_le _ _).trans (by simp)

theorem colL_anti (j j' : ℕ) (h : j ≤ j') : colL lam j' ≤ colL lam j :=
  card_le_card fun i hi => by
    simp only [mem_filter, mem_univ, true_and] at hi ⊢; omega

/-- Inside the Durfee square, `λ′_j ≥ j + 1`. -/
theorem succ_le_colL (hl : Antitone lam) {j : ℕ} (hj : j < durfee lam) : j + 1 ≤ colL lam j := by
  have h1 := (lt_durfee_iff hl j).mp hj
  have hjn : j < n := lt_of_lt_of_le hj durfee_le
  exact le_colL hl hjn h1

/-- The legs are strictly decreasing. -/
theorem frobB_lt (hl : Antitone lam) {j j' : ℕ} (hjj : j < j') (hj' : j' < durfee lam) :
    frobB lam j' < frobB lam j := by
  have := succ_le_colL hl hj'
  have := colL_anti (lam := lam) j j' hjj.le
  simp only [frobB]; omega

theorem frobB_lt_n (hl : Antitone lam) {j : ℕ} (hj : j < durfee lam) : frobB lam j < n := by
  have := succ_le_colL hl hj
  have := colL_le_n (lam := lam) j
  simp only [frobB]; omega

/-- **Frobenius complementarity**: a leg `β_j` (`j < d`) is never `x − λ_x` (`d ≤ x < n`). -/
theorem frobB_ne (hl : Antitone lam) {j x : ℕ} (hj : j < durfee lam) (hx : durfee lam ≤ x)
    (hxn : x < n) :
    frobB lam j ≠ x - rowL lam x := by
  have hrx : rowL lam x ≤ x := not_lt.mp fun h => absurd ((lt_durfee_iff hl x).mpr h) (by omega)
  simp only [frobB]
  by_cases hjx : j < rowL lam x
  · have := le_colL hl hxn hjx; omega
  · have := colL_le hl hxn (not_lt.mp hjx); omega

theorem rowL_anti (hl : Antitone lam) {x x' : ℕ} (h : x ≤ x') : rowL lam x' ≤ rowL lam x := by
  unfold rowL
  split_ifs with h1 h2 h2
  · exact hl (Fin.mk_le_mk.mpr h)
  · omega
  · exact Nat.zero_le _
  · exact le_rfl

end Frobenius

/-! ## Giambelli for an `(h, e)` pair -/

/-- **Giambelli's identity** for the Jacobi–Trudi determinant of any `(h, e)` pair:
`det (h_{λ_i − i + j}) = det (g(α_i, β_j))_{i, j < d}`. -/
theorem giambelli_jt (hp : HEPair h e) {n : ℕ} {lam : Fin n → ℕ} (hl : Antitone lam) :
    jt h lam = det (of fun i j : Fin (durfee lam) => hookV h e (frobA lam i) (frobB lam j)) := by
  set d := durfee lam with hd
  have hdn : d ≤ n := durfee_le
  -- the unitriangular factor `E′`
  set E' : Matrix (Fin n) (Fin n) R := of fun j k => sg R ((j : ℤ) + k) * e ((k : ℤ) - j) with hE'
  have hE : det E' = 1 := by
    rw [det_of_isUpperTriangular]
    · exact prod_eq_one fun j _ => by simp [hE', hp.e_zero, ← two_mul, sg_two_mul]
    · intro j k hjk
      simp only [hE', of_apply]
      rw [hp.e_neg _ (by have : (k : ℕ) < j := hjk; omega), mul_zero]
  set J : Matrix (Fin n) (Fin n) R := of fun i j : Fin n => h ((lam i : ℤ) - i + j) with hJ
  have hP : ∀ x y : Fin n, (J * E') x y = rowF h e ((lam x : ℤ) - x) y := by
    intro x y
    simp only [Matrix.mul_apply, hJ, hE', of_apply]
    rw [rowF, Fin.sum_univ_eq_sum_range (fun j => h ((lam x : ℤ) - x + j) *
      (sg R ((j : ℤ) + y) * e ((y : ℤ) - j))) n]
    symm
    refine sum_subset (fun j hj => by simp at hj ⊢; omega) fun j hj hj' => ?_
    simp only [mem_range] at hj hj'
    rw [hp.e_neg _ (by omega), mul_zero, mul_zero]
  have hn : d + (n - d) = n := by omega
  set Q : ℕ → ℕ → R := fun x y => rowF h e ((rowL lam x : ℤ) - x) y with hQ
  have hdet : jt h lam = det (of fun x y : Fin (d + (n - d)) => Q x y) := by
    rw [jt, ← hJ, ← mul_one (det J), ← hE, ← det_mul, ← det_submatrix_equiv_self (finCongr hn)]
    congr 1
    ext x y
    rw [submatrix_apply, hP, of_apply, hQ]
    simp [rowL, show (x : ℕ) < n by omega]
    rfl
  -- the legs, increasing, and the unit columns
  have hbB : ∀ j : Fin d, frobB lam (d - 1 - j) < d + (n - d) := fun j => by
    have := frobB_lt_n hl (lam := lam) (j := d - 1 - j) (by omega); omega
  let b : Fin d → Fin (d + (n - d)) := fun j => ⟨frobB lam (d - 1 - j), hbB j⟩
  let c : Fin (n - d) → Fin (d + (n - d)) := fun i => ⟨(d + i) - rowL lam (d + i), by omega⟩
  have hrx : ∀ x, d ≤ x → rowL lam x ≤ x := fun x hx =>
    not_lt.mp fun h => absurd ((lt_durfee_iff hl x).mpr h) (by omega)
  have hb : StrictMono b := fun j j' h => by
    simp only [b, Fin.mk_lt_mk]
    exact frobB_lt hl (by have : (j : ℕ) < j' := h; omega) (by omega)
  have hc : StrictMono c := fun i i' h => by
    have h' : (i : ℕ) < i' := h
    have := rowL_anti hl (lam := lam) (show d + (i : ℕ) ≤ d + i' by omega)
    have := hrx (d + i) (by omega)
    simp only [c, Fin.mk_lt_mk]; omega
  have hbc : ∀ j i, b j ≠ c i := fun j i h => by
    have := congrArg Fin.val h
    simp only [b, c] at this
    exact frobB_ne hl (by omega) (by omega) (by omega) this
  have hcov : ∀ y, (∃ j, b j = y) ∨ (∃ i, c i = y) := by
    have hU : univ.image b ∪ univ.image c = univ := by
      apply eq_univ_of_card
      rw [card_union_of_disjoint, card_image_of_injective _ hb.injective,
        card_image_of_injective _ hc.injective]
      · simp
      · rw [disjoint_left]
        intro y hy hy'
        obtain ⟨j, -, rfl⟩ := mem_image.mp hy
        obtain ⟨i, -, hi⟩ := mem_image.mp hy'
        exact hbc j i hi.symm
    intro y
    have := hU ▸ mem_univ y
    rcases mem_union.mp this with h | h
    · obtain ⟨j, -, hj⟩ := mem_image.mp h; exact Or.inl ⟨j, hj⟩
    · obtain ⟨i, -, hi⟩ := mem_image.mp h; exact Or.inr ⟨i, hi⟩
  have hM : ∀ (i : Fin (n - d)) y, (of fun x y : Fin (d + (n - d)) => Q x y) (Fin.natAdd d i) y =
      if y = c i then 1 else 0 := by
    intro i y
    have := hrx (d + i) (by omega)
    simp only [of_apply, hQ, Fin.val_natAdd]
    rw [rowF_of_nonpos hp (by omega)]
    congr 1
    apply propext
    rw [Fin.ext_iff]
    simp only [c]
    omega
  rw [hdet, det_unitRows (n - d) _ b c hb hc hbc hcov hM]
  -- the minor on the legs
  have hrow : ∀ (i : Fin d) (j : Fin d),
      (of fun x y : Fin (d + (n - d)) => Q x y) (Fin.castAdd (n - d) i) (b j) =
      sg R (b j : ℕ) * hookV h e (frobA lam i) (frobB lam (Fin.rev j)) := by
    intro i j
    have hi := (lt_durfee_iff hl i).mp i.2
    simp only [of_apply, hQ, Fin.val_castAdd]
    rw [show ((rowL lam i : ℕ) : ℤ) - (i : ℕ) = ((frobA lam i : ℕ) : ℤ) + 1 by
        simp only [frobA]; omega,
      rowF_of_pos hp]
    simp only [b, Fin.val_rev]
    rw [show d - ((j : ℕ) + 1) = d - 1 - j by omega]
  rw [show (of fun i j : Fin d =>
        (of fun x y : Fin (d + (n - d)) => Q x y) (Fin.castAdd (n - d) i) (b j)) =
      of fun i j => sg R (b j : ℕ) *
        (of fun i j : Fin d => hookV h e (frobA lam i) (frobB lam j)).submatrix
        id Fin.rev i j by ext i j; rw [of_apply, hrow]; rfl,
    det_mul_row, det_submatrix_rev, prod_sg, ← mul_assoc, ← mul_assoc, ← sg_add, ← sg_add]
  rw [show ∑ j : Fin d, (((b j : ℕ) : ℤ) - (j : ℕ)) + ∑ j : Fin d, ((b j : ℕ) : ℤ) +
        ∑ j : Fin d, ((j : ℕ) : ℤ)
      = 2 * ∑ j : Fin d, ((b j : ℕ) : ℤ) by rw [sum_sub_distrib]; ring, sg_two_mul, one_mul]

/-- The hook `(a + 1, 1^b)`, as `b + 1` rows. -/
def hookShape (a b : ℕ) : Fin (b + 1) → ℕ := fun i => if (i : ℕ) = 0 then a + 1 else 1

theorem hookShape_antitone (a b : ℕ) : Antitone (hookShape a b) := fun i j _ => by
  simp only [hookShape]; split_ifs <;> omega

theorem durfee_hookShape (a b : ℕ) : durfee (hookShape a b) = 1 := by
  rw [durfee, show (univ.filter fun i : Fin (b + 1) => (i : ℕ) < hookShape a b i) = {0} by
    ext i; rw [mem_filter, mem_singleton, Fin.ext_iff]
    simp only [mem_univ, true_and, hookShape, Fin.val_zero]
    split_ifs <;> omega]
  rfl

/-- **The hook value**: `jt (a + 1, 1^b) = g(a, b)`. -/
theorem jt_hook (hp : HEPair h e) (a b : ℕ) : jt h (hookShape a b) = hookV h e a b := by
  rw [giambelli_jt hp (hookShape_antitone a b),
    det_eq_elem_of_card_eq_one (by simp [durfee_hookShape]) ⟨0, by simp [durfee_hookShape]⟩]
  have hA : frobA (hookShape a b) 0 = a := by simp [frobA, rowL, hookShape]
  have hB : frobB (hookShape a b) 0 = b := by
    simp only [frobB, colL]
    rw [filter_true_of_mem (fun x _ => by simp only [hookShape]; split_ifs <;> omega)]
    simp
  change hookV h e (frobA _ 0) (frobB _ 0) = _
  rw [hA, hB]

/-- **Giambelli's identity** for any `(h, e)` pair: `jt λ = det (jt (α_i | β_j))_{i, j < d}`. -/
theorem giambelli_jt' (hp : HEPair h e) {n : ℕ} {lam : Fin n → ℕ} (hl : Antitone lam) :
    jt h lam =
      det (of fun i j : Fin (durfee lam) => jt h (hookShape (frobA lam i) (frobB lam j))) := by
  rw [giambelli_jt hp hl]
  simp only [jt_hook hp]

end Giambelli
