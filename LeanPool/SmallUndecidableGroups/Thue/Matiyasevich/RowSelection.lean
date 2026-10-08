/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Thue.Matiyasevich.PriorityStage

/-!
The row-selection combinatorics behind the displayed identity on page 49.
`selectOdd` keeps positions `1,3,5,...`; iterating it `u` times keeps the
positions congruent to `2^u - 1` modulo `2^u`.
-/

@[expose] public section

namespace Undecidability
namespace Thue
namespace Matiyasevich1993
namespace Priority
namespace RowSelection

/-- Keep every second entry, starting with the second. -/
def selectOdd {α : Type*} : List α → List α
  | _ :: y :: rest => y :: selectOdd rest
  | _ => []

/-- Iterate `selectOdd`. -/
def thin {α : Type*} : ℕ → List α → List α
  | 0, W => W
  | u + 1, W => selectOdd (thin u W)

@[simp] theorem selectOdd_nil {α : Type*} : selectOdd ([] : List α) = [] := rfl

@[simp] theorem selectOdd_cons_cons {α : Type*} (x y : α) (W : List α) :
    selectOdd (x :: y :: W) = y :: selectOdd W := rfl

@[simp] theorem thin_succ {α : Type*} (u : ℕ) (W : List α) :
    thin (u + 1) W = selectOdd (thin u W) := rfl

@[simp] theorem thin_nil {α : Type*} (u : ℕ) : thin u ([] : List α) = [] := by
  induction u with
  | zero => rfl
  | succ u ih => rw [thin_succ, ih, selectOdd_nil]

theorem selectOdd_length {α : Type*} (W : List α) :
    (selectOdd W).length = W.length / 2 := by
  induction W using List.twoStepInduction with
  | nil => simp [selectOdd]
  | singleton x => simp [selectOdd]
  | cons_cons x y W ih _ =>
      simp only [selectOdd_cons_cons, List.length_cons, ih]
      omega

theorem selectOdd_getD {α : Type*} (W : List α) (i : ℕ) (d : α) :
    (selectOdd W).getD i d = W.getD (2 * i + 1) d := by
  induction W using List.twoStepInduction generalizing i with
  | nil => simp [selectOdd]
  | singleton x =>
      cases i <;> simp [selectOdd]
  | cons_cons x y W ih _ =>
      cases i with
      | zero => simp [selectOdd]
      | succ i =>
          simpa [selectOdd, Nat.mul_succ, Nat.add_assoc] using ih (i := i)

theorem thin_length {α : Type*} (u : ℕ) (W : List α) :
    (thin u W).length = W.length / 2 ^ u := by
  induction u with
  | zero => simp [thin]
  | succ u ih =>
      rw [thin_succ, selectOdd_length, ih, Nat.div_div_eq_div_mul]
      simp [pow_succ, Nat.mul_comm]

theorem thin_getD {α : Type*} (u : ℕ) (W : List α) (i : ℕ) (d : α) :
    (thin u W).getD i d = W.getD (2 ^ u * (i + 1) - 1) d := by
  induction u generalizing i with
  | zero => simp [thin]
  | succ u ih =>
      rw [thin_succ, selectOdd_getD, ih]
      congr 1
      simp only [pow_succ]
      rw [show 2 * i + 1 + 1 = 2 * (i + 1) by omega]
      simp [Nat.mul_assoc]

theorem selectOdd_append_of_even {α : Type*} (X Y : List α)
    (heven : 2 ∣ X.length) :
    selectOdd (X ++ Y) = selectOdd X ++ selectOdd Y := by
  induction X using List.twoStepInduction with
  | nil => rfl
  | singleton x =>
      obtain ⟨k, hk⟩ := heven
      simp at hk
      omega
  | cons_cons x y X ih _ =>
      have htail : 2 ∣ X.length := by
        obtain ⟨k, hk⟩ := heven
        refine ⟨k - 1, ?_⟩
        simp only [List.length_cons] at hk
        omega
      simp [selectOdd, ih htail]

theorem thin_append_of_dvd {α : Type*} (u : ℕ) (X Y : List α)
    (hdiv : 2 ^ u ∣ X.length) :
    thin u (X ++ Y) = thin u X ++ thin u Y := by
  induction u generalizing X with
  | zero => rfl
  | succ u ih =>
      obtain ⟨k, hk⟩ := hdiv
      have hdiv' : 2 ^ u ∣ X.length := by
        refine ⟨2 * k, ?_⟩
        rw [hk, pow_succ]
        simp [Nat.mul_assoc]
      have heven : 2 ∣ (thin u X).length := by
        refine ⟨k, ?_⟩
        rw [thin_length, hk, pow_succ]
        simp [Nat.mul_assoc]
      simp only [thin_succ]
      rw [ih X hdiv']
      exact selectOdd_append_of_even (thin u X) (thin u Y) heven

theorem thin_succ_comm {α : Type*} (u : ℕ) (W : List α) :
    thin (u + 1) W = thin u (selectOdd W) := by
  induction u with
  | zero => rfl
  | succ u ih =>
      rw [thin_succ, ih, thin_succ]

/-! ### Aligned expansion -/

/-- Insert `2^u - 1` zeroes before every binary letter.  The original
letters then occupy precisely the positions congruent to `2^u - 1` modulo
`2^u`. -/
def expand (u : ℕ) : List (Fin 2) → List (Fin 2)
  | [] => []
  | x :: W => List.replicate (2 ^ u - 1) 0 ++ x :: expand u W

@[simp] theorem expand_cons (u : ℕ) (x : Fin 2) (W : List (Fin 2)) :
    expand u (x :: W) =
      List.replicate (2 ^ u - 1) 0 ++ x :: expand u W := rfl

theorem expand_length (u : ℕ) (W : List (Fin 2)) :
    (expand u W).length = W.length * 2 ^ u := by
  induction W with
  | nil => simp [expand]
  | cons x W ih =>
      simp only [expand_cons, List.length_append, List.length_replicate,
        List.length_cons, ih]
      have hpow : 0 < 2 ^ u := pow_pos (by omega) u
      rw [Nat.succ_mul]
      omega

theorem expand_length_dvd (u : ℕ) (W : List (Fin 2)) :
    2 ^ u ∣ (expand u W).length := by
  refine ⟨W.length, ?_⟩
  rw [expand_length, Nat.mul_comm]

theorem selectOdd_expandBlock (k : ℕ) (x : Fin 2) :
    selectOdd (List.replicate (2 * k + 1) 0 ++ [x]) =
      List.replicate k 0 ++ [x] := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show 2 * (k + 1) + 1 = 2 + (2 * k + 1) by omega,
        List.replicate_add]
      change selectOdd
          ((0 : Fin 2) :: 0 :: (List.replicate (2 * k + 1) 0 ++ [x])) =
        0 :: (List.replicate k 0 ++ [x])
      rw [selectOdd_cons_cons, ih]

theorem thin_expandBlock (u : ℕ) (x : Fin 2) :
    thin u (List.replicate (2 ^ u - 1) 0 ++ [x]) = [x] := by
  induction u with
  | zero => rfl
  | succ u ih =>
      rw [thin_succ_comm]
      have hpow : 0 < 2 ^ u := pow_pos (by omega) u
      rw [show 2 ^ (u + 1) - 1 = 2 * (2 ^ u - 1) + 1 by
        rw [pow_succ]
        omega]
      rw [selectOdd_expandBlock, ih]

/-- `thin` is a left inverse to aligned expansion. -/
@[simp] theorem thin_expand (u : ℕ) (W : List (Fin 2)) :
    thin u (expand u W) = W := by
  induction W with
  | nil => exact thin_nil u
  | cons x W ih =>
      rw [expand_cons]
      change thin u
        (List.replicate (2 ^ u - 1) 0 ++ ([x] ++ expand u W)) = x :: W
      rw [← List.append_assoc]
      rw [thin_append_of_dvd]
      · rw [thin_expandBlock, ih]
        rfl
      · simp only [List.length_append, List.length_replicate,
          List.length_singleton]
        rw [Nat.sub_add_cancel (by
          exact pow_pos (by decide : 0 < (2 : ℕ)) u)]

/-! ### Reading a column-major transpose -/

theorem column_getD {t : ℕ} (rows : Fin t → List (Fin 2))
    (col : ℕ) (i : Fin t) :
    (column rows col).getD i.val 0 = (rows i).getD col 0 := by
  simp [column, i.isLt]

theorem columnsFrom_getD {t : ℕ} (rows : Fin t → List (Fin 2))
    (start width col : ℕ) (i : Fin t) (hcol : col < width) :
    (columnsFrom rows start width).getD (col * t + i.val) 0 =
      (rows i).getD (start + col) 0 := by
  induction width generalizing start col with
  | zero => omega
  | succ width ih =>
      cases col with
      | zero =>
          rw [columnsFrom_succ]
          simp only [zero_mul, zero_add]
          rw [List.getD_append (column rows start)
            (columnsFrom rows (start + 1) width) 0 i.val]
          · simpa using column_getD rows start i
          · rw [column_length]
            exact i.isLt
      | succ col =>
          rw [columnsFrom_succ]
          rw [List.getD_append_right (column rows start)
            (columnsFrom rows (start + 1) width) 0
            ((col + 1) * t + i.val)]
          · have hcol' : col < width := by omega
            have h := ih (start := start + 1) (col := col) hcol'
            simpa [column_length, Nat.succ_mul, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] using h
          · rw [column_length]
            rw [Nat.succ_mul]
            omega

theorem transpose_getD {t width : ℕ}
    (rows : Fin t → List (Fin 2)) (col : ℕ) (i : Fin t)
    (hcol : col < width) :
    (transpose width rows).getD (col * t + i.val) 0 =
      (rows i).getD col 0 := by
  simpa [transpose] using columnsFrom_getD rows 0 width col i hcol

/-! ### The padded row selected by `e^u` -/

/-- Padded transpose whose last sampled padding symbol is an arbitrary bit `z`. -/
def paddedTransposeLast {t : ℕ} (width : ℕ)
    (rows : Fin t → List (Fin 2)) (j : Fin t) (z : Fin 2) : List (Fin 2) :=
  List.replicate (t - 1 - j.val) 0 ++
    transpose width rows ++ List.replicate j.val 0 ++ [z]

theorem paddedTransposeLast_length {t width : ℕ}
    (rows : Fin t → List (Fin 2)) (j : Fin t) (z : Fin 2) :
    (paddedTransposeLast width rows j z).length = (width + 1) * t := by
  simp only [paddedTransposeLast, List.length_append, List.length_replicate,
    List.length_singleton, transpose_length]
  have hj : j.val < t := j.isLt
  rw [Nat.add_mul]
  omega

theorem paddedTransposeLast_getD_row {t width : ℕ}
    (rows : Fin t → List (Fin 2)) (j : Fin t) (z : Fin 2) (ht : 0 < t)
    (col : ℕ) (hcol : col < width) :
    (paddedTransposeLast width rows j z).getD (t * (col + 1) - 1) 0 =
      (rows j).getD col 0 := by
  have hmul : t * (col + 1) = t * col + t := by
    simp [Nat.mul_add]
  have hleft : t - 1 - j.val ≤ t * (col + 1) - 1 := by
    rw [hmul]
    omega
  have hshift :
      t * (col + 1) - 1 - (t - 1 - j.val) = col * t + j.val := by
    rw [hmul, Nat.mul_comm t col]
    omega
  rw [show paddedTransposeLast width rows j z =
      List.replicate (t - 1 - j.val) 0 ++
        (transpose width rows ++ (List.replicate j.val 0 ++ [z])) by
    simp [paddedTransposeLast, List.append_assoc]]
  rw [List.getD_append_right
    (List.replicate (t - 1 - j.val) 0)
    (transpose width rows ++ (List.replicate j.val 0 ++ [z])) 0
    (t * (col + 1) - 1)]
  · rw [List.length_replicate, hshift]
    rw [List.getD_append (transpose width rows)
      (List.replicate j.val 0 ++ [z]) 0 (col * t + j.val)]
    · exact transpose_getD rows col j hcol
    · rw [transpose_length]
      have hstep : col * t + j.val < (col + 1) * t := by
        rw [Nat.succ_mul]
        omega
      have hbound : (col + 1) * t ≤ width * t :=
        Nat.mul_le_mul_right t (Nat.succ_le_iff.mpr hcol)
      exact hstep.trans_le hbound
  · simpa using hleft

theorem paddedTransposeLast_getD_last {t width : ℕ}
    (rows : Fin t → List (Fin 2)) (j : Fin t) (z : Fin 2) (ht : 0 < t) :
    (paddedTransposeLast width rows j z).getD
      (t * (width + 1) - 1) 0 = z := by
  have hmul : t * (width + 1) = t * width + t := by
    simp [Nat.mul_add]
  have hleft : t - 1 - j.val ≤ t * (width + 1) - 1 := by
    rw [hmul]
    omega
  have hshift :
      t * (width + 1) - 1 - (t - 1 - j.val) = width * t + j.val := by
    rw [hmul, Nat.mul_comm t width]
    omega
  rw [show paddedTransposeLast width rows j z =
      List.replicate (t - 1 - j.val) 0 ++
        (transpose width rows ++ (List.replicate j.val 0 ++ [z])) by
    simp [paddedTransposeLast, List.append_assoc]]
  rw [List.getD_append_right
    (List.replicate (t - 1 - j.val) 0)
    (transpose width rows ++ (List.replicate j.val 0 ++ [z])) 0
    (t * (width + 1) - 1)]
  · rw [List.length_replicate, hshift]
    rw [List.getD_append_right (transpose width rows)
      (List.replicate j.val 0 ++ [z]) 0 (width * t + j.val)]
    · rw [transpose_length, Nat.add_sub_cancel_left]
      rw [List.getD_append_right (List.replicate j.val 0) [z] 0 j.val]
      · simp
      · simp
    · rw [transpose_length]
      omega
  · simpa using hleft

/-- General row selection with an arbitrary final sampled bit. -/
theorem thin_paddedTranspose_last (u width : ℕ)
    (rows : Fin (2 ^ u) → List (Fin 2)) (j : Fin (2 ^ u))
    (z : Fin 2) (hlen : ∀ i, (rows i).length = width) :
    thin u (paddedTransposeLast width rows j z) = rows j ++ [z] := by
  apply List.ext_getElem
  · rw [thin_length, paddedTransposeLast_length]
    simp [hlen j]
  · intro n hthin htarget
    have hgetD :
        (thin u (paddedTransposeLast width rows j z)).getD n 0 =
          (rows j ++ [z]).getD n 0 := by
      rw [thin_getD]
      by_cases hn : n < width
      · calc
          (paddedTransposeLast width rows j z).getD
              (2 ^ u * (n + 1) - 1) 0 =
              (rows j).getD n 0 :=
            paddedTransposeLast_getD_row rows j z
              (pow_pos (by omega) u) n hn
          _ = (rows j ++ [z]).getD n 0 := by
            rw [List.getD_append (rows j) [z] 0 n (by
              simpa [hlen j] using hn)]
      · have hnle : n ≤ width := by
          have : n < width + 1 := by simpa [hlen j] using htarget
          omega
        have hnwidth : n = width := by omega
        subst n
        calc
          (paddedTransposeLast width rows j z).getD
              (2 ^ u * (width + 1) - 1) 0 = z :=
            paddedTransposeLast_getD_last rows j z (pow_pos (by omega) u)
          _ = (rows j ++ [z]).getD width 0 := by
            rw [List.getD_append_right (rows j) [z] 0 width (by
              simp [hlen j])]
            simp [hlen j]
    exact (List.getD_eq_getElem _ _ hthin).symm.trans
      (hgetD.trans (List.getD_eq_getElem _ _ htarget))

/-! ### Priority normalization performs the sampling -/

theorem pushE_liftBinary_even (W : List (Fin 2)) (v : ℕ)
    (heven : 2 ∣ W.length) :
    pushE (liftBinary W ++ List.replicate v e) =
      liftBinary (selectOdd W) ++ List.replicate (v + 1) e := by
  induction W using List.twoStepInduction with
  | nil =>
      simp [liftBinary, selectOdd, List.replicate_succ]
  | singleton x =>
      obtain ⟨k, hk⟩ := heven
      simp at hk
      omega
  | cons_cons x y W ih _ =>
      have htail : 2 ∣ W.length := by
        obtain ⟨k, hk⟩ := heven
        refine ⟨k - 1, ?_⟩
        simp only [List.length_cons] at hk
        omega
      have hih := ih htail
      fin_cases x <;> fin_cases y
      · change pushE (a :: a ::
            (liftBinary W ++ List.replicate v e)) =
          a :: (liftBinary (selectOdd W) ++ List.replicate (v + 1) e)
        rw [pushE_aa, hih]
      · change pushE (a :: b ::
            (liftBinary W ++ List.replicate v e)) =
          b :: (liftBinary (selectOdd W) ++ List.replicate (v + 1) e)
        rw [pushE_ab, hih]
      · change pushE (b :: a ::
            (liftBinary W ++ List.replicate v e)) =
          a :: (liftBinary (selectOdd W) ++ List.replicate (v + 1) e)
        rw [pushE_ba, hih]
      · change pushE (b :: b ::
            (liftBinary W ++ List.replicate v e)) =
          b :: (liftBinary (selectOdd W) ++ List.replicate (v + 1) e)
        rw [pushE_bb, hih]

/-- An initial block `e^u` implements `thin u` on a binary word whose
length is a multiple of `2^u`. -/
theorem firstNormal_replicate_e_liftBinary (u : ℕ) (W : List (Fin 2))
    (hdiv : 2 ^ u ∣ W.length) :
    firstNormal (List.replicate u e ++ liftBinary W) =
      liftBinary (thin u W) ++ List.replicate u e := by
  induction u generalizing W with
  | zero =>
      simpa [thin, firstNormal] using firstNormal_liftBinary_append W []
  | succ u ih =>
      obtain ⟨k, hk⟩ := hdiv
      have hdiv' : 2 ^ u ∣ W.length := by
        refine ⟨2 * k, ?_⟩
        rw [hk, pow_succ]
        simp [Nat.mul_assoc]
      have heven : 2 ∣ (thin u W).length := by
        refine ⟨k, ?_⟩
        rw [thin_length, hk, pow_succ]
        simp [Nat.mul_assoc]
      rw [List.replicate_succ, List.cons_append, firstNormal_e_cons,
        ih W hdiv', thin_succ]
      exact pushE_liftBinary_even (thin u W) u heven

/-! ### The last column -/

theorem columnsFrom_last {t : ℕ}
    (rows : Fin t → List (Fin 2)) (start k : ℕ) :
    columnsFrom rows start (k + 1) =
      columnsFrom rows start k ++ column rows (start + k) := by
  induction k generalizing start with
  | zero => simp [columnsFrom]
  | succ k ih =>
      change column rows start ++ columnsFrom rows (start + 1) (k + 1) =
        (column rows start ++ columnsFrom rows (start + 1) k) ++
          column rows (start + (k + 1))
      rw [ih, List.append_assoc]
      congr 2
      congr 1
      omega

theorem column_last {t width : ℕ}
    (rows : Fin t → List (Fin 2))
    (hwidth : 0 < width)
    (hlen : ∀ i, (rows i).length = width)
    (hend : ∀ i, ∃ init, rows i = init ++ [(1 : Fin 2)]) :
    column rows (width - 1) = List.replicate t 1 := by
  unfold column
  have hfun :
      (fun i : Fin t => (rows i).getD (width - 1) 0) =
        fun _ => (1 : Fin 2) := by
    funext i
    obtain ⟨init, hi⟩ := hend i
    have hinit : init.length = width - 1 := by
      have h := hlen i
      rw [hi] at h
      simp only [List.length_append, List.length_singleton] at h
      omega
    rw [hi, ← hinit]
    simp
  rw [hfun, List.ofFn_const]

/-- If every nonempty rectangular row ends in the binary letter `1`, then
the column-major transpose also ends in `1` (the final entry of its final
column). -/
theorem transpose_ends_b {t width : ℕ}
    (rows : Fin t → List (Fin 2))
    (ht : 0 < t) (hwidth : 0 < width)
    (hlen : ∀ i, (rows i).length = width)
    (hend : ∀ i, ∃ init, rows i = init ++ [(1 : Fin 2)]) :
    ∃ init, transpose width rows = init ++ [(1 : Fin 2)] := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  obtain ⟨width, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hwidth)
  rw [transpose, columnsFrom_last]
  have hcol : column rows width = List.replicate (t + 1) 1 := by
    simpa using column_last rows (by omega) hlen hend
  simp only [Nat.zero_add]
  rw [hcol, List.replicate_succ']
  refine ⟨columnsFrom rows 0 width ++ List.replicate t 1, ?_⟩
  simp only [List.append_assoc]

theorem liftBinary_transpose_ends_b {t width : ℕ}
    (rows : Fin t → List (Fin 2))
    (ht : 0 < t) (hwidth : 0 < width)
    (hlen : ∀ i, (rows i).length = width)
    (hend : ∀ i, ∃ init, rows i = init ++ [(1 : Fin 2)]) :
    ∃ init, liftBinary (transpose width rows) = init ++ [b] := by
  obtain ⟨init, hinit⟩ := transpose_ends_b rows ht hwidth hlen hend
  refine ⟨liftBinary init, ?_⟩
  rw [hinit, liftBinary_append]
  simp [liftBinary, liftBit, b]

end RowSelection
end Priority
end Matiyasevich1993
end Thue
end Undecidability

namespace Undecidability
namespace Thue
namespace Matiyasevich1993
namespace Priority
namespace RowSelection

/-!
An affine variant of `thin`.  Whereas `thin u` keeps the positions
`2^u - 1, 2 * 2^u - 1, ...`, `affineSample u j` keeps the positions
`j, j + 2^u, ...`.  This makes the phase-neutrality of a transposed block
of length `width * 2^u` explicit.
-/

/-- Keep the entries whose zero-based indices are congruent to `j` modulo
`2^u`. -/
def affineSample (u : ℕ) (j : Fin (2 ^ u)) (W : List (Fin 2)) :
    List (Fin 2) :=
  thin u (List.replicate (2 ^ u - 1 - j.val) 0 ++ W)

theorem affineSample_length (u : ℕ) (j : Fin (2 ^ u))
    (W : List (Fin 2)) :
    (affineSample u j W).length =
      (2 ^ u - 1 - j.val + W.length) / 2 ^ u := by
  rw [affineSample, thin_length]
  simp only [List.length_append, List.length_replicate]

theorem affineSample_getD (u : ℕ) (j : Fin (2 ^ u))
    (W : List (Fin 2)) (k : ℕ) :
    (affineSample u j W).getD k 0 =
      W.getD (2 ^ u * k + j.val) 0 := by
  rw [affineSample, thin_getD]
  have hpow : 0 < 2 ^ u := pow_pos (by omega) u
  have hj : j.val < 2 ^ u := j.isLt
  have hjle : j.val ≤ 2 ^ u - 1 := by omega
  have hprefix_le : 2 ^ u - 1 - j.val ≤ 2 ^ u - 1 :=
    Nat.sub_le _ _
  have hperiod_le : 2 ^ u ≤ 2 ^ u * (k + 1) := by
    calc
      2 ^ u = 2 ^ u * 1 := by simp
      _ ≤ 2 ^ u * (k + 1) := Nat.mul_le_mul_left _ (by omega)
  have hprefix :
      2 ^ u - 1 - j.val ≤ 2 ^ u * (k + 1) - 1 :=
    hprefix_le.trans (Nat.sub_le_sub_right hperiod_le 1)
  rw [List.getD_append_right
    (List.replicate (2 ^ u - 1 - j.val) 0) W 0
    (2 ^ u * (k + 1) - 1)]
  · simp only [List.length_replicate]
    rw [show 2 ^ u * (k + 1) - 1 - (2 ^ u - 1 - j.val) =
        2 ^ u * k + j.val by
      rw [Nat.mul_succ]
      have hcancel : 2 ^ u - 1 - j.val + j.val = 2 ^ u - 1 :=
        Nat.sub_add_cancel hjle
      omega]
  · simpa using hprefix

/-- A column-major transpose occupies a whole number of sampling periods.
Sampling it at phase `j`, followed by an arbitrary suffix, returns row `j`
followed by the suffix sampled at the unchanged phase. -/
theorem affineSample_transpose_append
    (u width : ℕ) (rows : Fin (2 ^ u) → List (Fin 2))
    (j : Fin (2 ^ u)) (R : List (Fin 2))
    (hlen : ∀ i, (rows i).length = width) :
    affineSample u j (transpose width rows ++ R) =
      rows j ++ affineSample u j R := by
  apply List.ext_getElem
  · rw [affineSample_length, List.length_append, transpose_length,
      List.length_append, hlen, affineSample_length]
    have hpow : 0 < 2 ^ u := pow_pos (by omega) u
    have harith :
        2 ^ u - 1 - j.val + (width * 2 ^ u + R.length) =
          (2 ^ u - 1 - j.val + R.length) + width * 2 ^ u := by
      omega
    rw [harith, Nat.add_mul_div_right _ _ hpow]
    omega
  · intro k hkLeft hkRight
    have hgetD :
        (affineSample u j (transpose width rows ++ R)).getD k 0 =
          (rows j ++ affineSample u j R).getD k 0 := by
      rw [affineSample_getD]
      by_cases hk : k < width
      · rw [List.getD_append (transpose width rows) R 0
            (2 ^ u * k + j.val)]
        · rw [show 2 ^ u * k + j.val = k * 2 ^ u + j.val by
              rw [Nat.mul_comm]]
          rw [transpose_getD rows k j hk]
          rw [List.getD_append (rows j) (affineSample u j R) 0 k
            (by simpa [hlen j] using hk)]
        · rw [transpose_length]
          calc
            2 ^ u * k + j.val < 2 ^ u * k + 2 ^ u :=
              Nat.add_lt_add_left j.isLt _
            _ = (k + 1) * 2 ^ u := by
              rw [Nat.add_mul, one_mul, Nat.mul_comm (2 ^ u) k]
            _ ≤ width * 2 ^ u :=
              Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hk)
      · have hwidth : width ≤ k := by omega
        rw [List.getD_append_right (transpose width rows) R 0
            (2 ^ u * k + j.val)]
        · rw [transpose_length]
          have hshift :
              2 ^ u * k + j.val - width * 2 ^ u =
                2 ^ u * (k - width) + j.val := by
            have hkdecomp : width + (k - width) = k :=
              Nat.add_sub_of_le hwidth
            have hmul :
                2 ^ u * k =
                  2 ^ u * width + 2 ^ u * (k - width) := by
              calc
                2 ^ u * k = 2 ^ u * (width + (k - width)) := by
                  rw [hkdecomp]
                _ = 2 ^ u * width + 2 ^ u * (k - width) :=
                  Nat.mul_add _ _ _
            calc
              2 ^ u * k + j.val - width * 2 ^ u =
                  (width * 2 ^ u +
                    (2 ^ u * (k - width) + j.val)) - width * 2 ^ u := by
                      rw [hmul, Nat.mul_comm (2 ^ u) width]
                      omega
              _ = 2 ^ u * (k - width) + j.val := by
                omega
          rw [hshift, ← affineSample_getD]
          rw [List.getD_append_right (rows j) (affineSample u j R) 0 k
            (by simpa [hlen j] using hwidth)]
          congr 2
          rw [hlen j]
        · rw [transpose_length]
          calc
            width * 2 ^ u ≤ k * 2 ^ u :=
              Nat.mul_le_mul_right _ hwidth
            _ = 2 ^ u * k := Nat.mul_comm _ _
            _ ≤ 2 ^ u * k + j.val := Nat.le_add_right _ _
    exact (List.getD_eq_getElem _ _ hkLeft).symm.trans
      (hgetD.trans (List.getD_eq_getElem _ _ hkRight))

/-- The inclusion of a row index into the upper half of the next power-of-two block. -/
def highPhase (u : ℕ) (j : Fin (2 ^ u)) : Fin (2 ^ (u + 1)) :=
  ⟨j.val + 2 ^ u, by
    rw [pow_succ]
    have := j.isLt
    omega⟩

/-- The inclusion of a row index into the lower half of the next power-of-two block. -/
def lowPhase (u : ℕ) (j : Fin (2 ^ u)) : Fin (2 ^ (u + 1)) :=
  ⟨j.val, by
    rw [pow_succ]
    have := j.isLt
    have hpow : 0 < 2 ^ u := pow_pos (by omega) u
    omega⟩

/-- Applying one further odd-position selection to an affine sample chooses
the upper lift of its phase. -/
private theorem selectOdd_affineSample_high
    (u : ℕ) (j : Fin (2 ^ u)) (W : List (Fin 2)) :
    selectOdd (affineSample u j W) =
      affineSample (u + 1) (highPhase u j) W := by
  have hprefix :
      2 ^ (u + 1) - 1 - (highPhase u j).val =
        2 ^ u - 1 - j.val := by
    change 2 ^ (u + 1) - 1 - (j.val + 2 ^ u) =
      2 ^ u - 1 - j.val
    rw [pow_succ]
    have := j.isLt
    omega
  unfold affineSample
  rw [hprefix, thin_succ]

/-- If one extra letter precedes an affine sample, odd-position selection
discards that letter and chooses the lower lift of the phase. -/
private theorem selectOdd_cons_affineSample_low
    (u : ℕ) (x : Fin 2) (j : Fin (2 ^ u)) (W : List (Fin 2)) :
    selectOdd (x :: affineSample u j W) =
      affineSample (u + 1) (lowPhase u j) W := by
  have hprefix :
      2 ^ (u + 1) - 1 - (lowPhase u j).val =
        2 ^ u + (2 ^ u - 1 - j.val) := by
    change 2 ^ (u + 1) - 1 - j.val =
      2 ^ u + (2 ^ u - 1 - j.val)
    rw [pow_succ]
    have := j.isLt
    omega
  have hreplicate :
      List.replicate
          (2 ^ (u + 1) - 1 - (lowPhase u j).val) (0 : Fin 2) =
        List.replicate (2 ^ u) 0 ++
          List.replicate (2 ^ u - 1 - j.val) 0 := by
    rw [hprefix, List.replicate_add]
  have hperiod :
      thin u (List.replicate (2 ^ u) (0 : Fin 2)) = [0] := by
    have hword :
        List.replicate (2 ^ u) (0 : Fin 2) =
          List.replicate (2 ^ u - 1) 0 ++ [0] := by
      have hpow : 0 < 2 ^ u := pow_pos (by omega) u
      calc
        List.replicate (2 ^ u) (0 : Fin 2) =
            List.replicate ((2 ^ u - 1) + 1) 0 := by
              congr 2
              omega
        _ = List.replicate (2 ^ u - 1) 0 ++ [0] := by
          rw [List.replicate_add]
          rfl
    rw [hword]
    exact thin_expandBlock u 0
  unfold affineSample
  rw [thin_succ, hreplicate, List.append_assoc,
    thin_append_of_dvd u (List.replicate (2 ^ u) 0)
      (List.replicate (2 ^ u - 1 - j.val) 0 ++ W) (by simp),
    hperiod]
  change selectOdd
      (x :: thin u (List.replicate (2 ^ u - 1 - j.val) 0 ++ W)) =
    selectOdd
      (0 :: thin u (List.replicate (2 ^ u - 1 - j.val) 0 ++ W))
  cases thin u (List.replicate (2 ^ u - 1 - j.val) 0 ++ W) <;> rfl

/-- Prefixing an affine sample and applying `selectOdd` updates only the
finite prefix and lifts the sampling phase by one binary digit.  For an even
prefix length the new phase is `j + 2^u`; for an odd prefix length it is `j`.
-/
theorem selectOdd_prefix_affineSample (u : ℕ)
    (P : List (Fin 2)) (j : Fin (2 ^ u)) :
    ∃ P' : List (Fin 2), ∃ j' : Fin (2 ^ (u + 1)), ∀ W,
      selectOdd (P ++ affineSample u j W) =
        P' ++ affineSample (u + 1) j' W := by
  induction P using List.twoStepInduction with
  | nil =>
      refine ⟨[], highPhase u j, ?_⟩
      intro W
      simpa using selectOdd_affineSample_high u j W
  | singleton x =>
      refine ⟨[], lowPhase u j, ?_⟩
      intro W
      simpa using selectOdd_cons_affineSample_low u x j W
  | cons_cons x y P ih _ =>
      obtain ⟨P', j', hP'⟩ := ih
      refine ⟨y :: P', j', ?_⟩
      intro W
      rw [show (x :: y :: P) ++ affineSample u j W =
          x :: y :: (P ++ affineSample u j W) by rfl,
        selectOdd_cons_cons, hP' W]
      rfl

end RowSelection
end Priority
end Matiyasevich1993
end Thue
end Undecidability
