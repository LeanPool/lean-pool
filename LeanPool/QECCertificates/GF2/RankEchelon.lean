/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module
public import LeanPool.QECCertificates.GF2.RankCertificate

/-!
# An append-only echelon rank routine (usable rank readings on wide matrices)

## Why it is needed

`rowReduce` (`GF2/RowReduce.lean`) returns a **mutually reduced** set of pivot rows: every
time a new pivot is inserted, the new pivot column is back-substituted into **all previous
rows** (the `D.map` of `insertPivot`). The consequence is that the **large new pivot row
`w` is copied into every previous row element**, and the next call to `reduceAgainst`
traverses those copies one by one, so the term size **grows multiplicatively with each
round**. On width 24, 13×13 `foldl` steps over 24 coordinates should take well under a
second, but the measured cost falls off a cliff at about 7 pivots (more than 200 s without
converging, peak working set above 200 GB); width 18 is only just feasible and width 24 is
unusable.

This module provides an **append-only, non-back-substituting** companion routine, in which
previous rows are left untouched when a new row joins. Mathematically it is still a correct
**echelon form**: the new row is 0 on **every earlier** pivot column (guaranteed by the
fold inside `reduceAgainst`, see `reduceAgainst_get_piv_eq_zero`), so the pivot columns are
pairwise distinct, and taking the **least** index then proves the rows linearly
independent.

## Relation to `rowReduce`

`rankEchelon_eq_length_rowReduce`: the two routines return the same number and the same row
space, so the rank is `rankEchelon`. Downstream rank and `k` claims can therefore **switch
backends** without any change to the mathematics, while `rowReduce` and all of its
downstream theorems (canonical-form uniqueness in `GF2/Canonical.lean` relies on the RREF
produced by back-substitution) are left **untouched**.

## A discipline for the implementation (read before editing)

`stepA` must be a **separate `def`**, and the main loop must be written as
`List.foldl stepA []`. Inlining `if hw : reduceAgainst D v = 0 then … else …` **into the
structural recursion** makes the elaborator hang (measured: more than 3 minutes with no
output, a 3.2 GB working set on a single core), whereas the same logic split into a
separate `def` goes through at once.

## Main results

* `spanL_rowList_echelonFrom`: the row space is unchanged (the code is not modified).
* `linearIndependent_get_of_echelon`: the rows of the echelon form are linearly
  independent.
* `finrank_spanL_eq_length_echelonFrom` / `rankEchelon_eq_length_rowReduce`: the **rank
  readings**.
-/

@[expose] public section

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-! ## Append-only pivot insertion and the main loop -/

/-- **Append** a pivot row to a list of pivot rows: previous rows are left untouched,
unlike the back-substitution performed by `insertPivot`. -/
def insertPivotA (D : List (PivRow n)) (w : Vec n) (p : Fin n) : List (PivRow n) :=
  D ++ [(w, p)]

/-- One step: reduce `v` against the current state and, if the result is nonzero,
**append** it as a new pivot row. -/
def stepA (D : List (PivRow n)) (v : Vec n) : List (PivRow n) :=
  if hw : reduceAgainst D v = 0 then D
  else insertPivotA D (reduceAgainst D v) (leadIdx (reduceAgainst D v) hw)

/-- The echelon form obtained by appending row by row (the main loop of this module). -/
def echelonFrom (L : List (Vec n)) : List (PivRow n) := L.foldl stepA []

/-- **The rank routine**: the number of rows of the append-only echelon form. -/
def rankEchelon (L : List (Vec n)) : ℕ := (echelonFrom L).length

/-! ## Invariance of the row space -/

lemma rowList_insertPivotA (D : List (PivRow n)) (w : Vec n) (p : Fin n) :
    rowList (insertPivotA D w p) = rowList D ++ [w] := by
  simp [rowList, insertPivotA, List.map_append]

/-- Appending spans the same row space as appending the original, unreduced row: the
reduced vector lies in the original row space. -/
lemma spanL_rowList_stepA (D : List (PivRow n)) (v : Vec n) :
    spanL (rowList (stepA D v)) = spanL (rowList D ++ [v]) := by
  unfold stepA
  split
  · rename_i hw
    have hv : v ∈ spanL (rowList D) := by
      have h := add_reduceAgainst_mem D v
      rw [hw, add_zero] at h
      exact h
    have hsup : Submodule.span (ZMod 2) ({v} : Set (Vec n)) ≤ spanL (rowList D) :=
      Submodule.span_le.2 fun x hx => by
        have hx' : x = v := by simpa using hx
        rw [hx']; exact hv
    rw [spanL_append_singleton, sup_eq_left.mpr hsup]
  · rename_i hw
    rw [rowList_insertPivotA]
    exact spanL_append_eq_of_add_mem (add_reduceAgainst_mem D v)

/-- A generalized form of the main loop: starting from `D` and consuming `L`, the row
space is exactly that of `rowList D ++ L`. -/
lemma spanL_rowList_foldl_stepA (D : List (PivRow n)) (L : List (Vec n)) :
    spanL (rowList (L.foldl stepA D)) = spanL (rowList D ++ L) := by
  induction L generalizing D with
  | nil => simp
  | cons v rest ih =>
      rw [List.foldl_cons, ih (stepA D v)]
      calc spanL (rowList (stepA D v) ++ rest)
          = spanL (rowList (stepA D v)) ⊔ spanL rest := spanL_append _ _
        _ = spanL (rowList D ++ [v]) ⊔ spanL rest := by rw [spanL_rowList_stepA]
        _ = (spanL (rowList D) ⊔ spanL [v]) ⊔ spanL rest := by rw [spanL_append]
        _ = spanL (rowList D) ⊔ (spanL [v] ⊔ spanL rest) := sup_assoc _ _ _
        _ = spanL (rowList D) ⊔ spanL ([v] ++ rest) := by rw [spanL_append]
        _ = spanL (rowList D ++ (v :: rest)) := (spanL_append _ _).symm

/-- **Invariance of the row space**: the append-only echelon form spans the same row
space as the original list of rows, and so defines the same code. -/
theorem spanL_rowList_echelonFrom (L : List (Vec n)) :
    spanL (rowList (echelonFrom L)) = spanL L := by
  have h := spanL_rowList_foldl_stepA ([] : List (PivRow n)) L
  simpa [echelonFrom] using h

/-! ## The echelon invariants

The append-only echelon form satisfies two properties. These are weaker than `IsReduced`:
they do not require an earlier row to be 0 on a later pivot column, and that is exactly the
price of dropping back-substitution.

* `EchSelf`: every row is 1 on its own pivot column
* `EchPair`: a **later** row is 0 on the pivot columns of **all earlier** rows.

`EchPair` is a product of the fold inside `reduceAgainst`: while the `j`-th row is being
processed, every already processed row is cleared **one at a time** on its own pivot
column, and adding further rows cannot reintroduce anything, because every row added is 0
on **all earlier** pivot columns (see `reduceAgainst_get_piv_eq_zero`). -/

/-- Every row is 1 on its own pivot column. -/
def EchSelf (D : List (PivRow n)) : Prop := ∀ i : Fin D.length, (D.get i).1 (D.get i).2 = 1

/-- A later row is 0 on the pivot columns of all earlier rows. -/
def EchPair (D : List (PivRow n)) : Prop :=
  ∀ i j : Fin D.length, i < j → (D.get j).1 (D.get i).2 = 0

lemma EchSelf.tail {r : PivRow n} {D : List (PivRow n)} (h : EchSelf (r :: D)) : EchSelf D := by
  intro i
  have hh := h i.succ
  simpa [List.get_cons_succ'] using hh

lemma EchPair.tail {r : PivRow n} {D : List (PivRow n)} (h : EchPair (r :: D)) : EchPair D := by
  intro i j hij
  have hh := h i.succ j.succ (by simpa using hij)
  simpa [List.get_cons_succ'] using hh

/-- A direct consequence of `EchPair`: every row after the head row is 0 on the pivot
column of the head row. -/
lemma EchPair.head_rows {r : PivRow n} {D : List (PivRow n)} (h : EchPair (r :: D)) :
    ∀ r' ∈ D, r'.1 r.2 = 0 := by
  intro r' hr'
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hr'
  have hlt : (0 : Fin (D.length + 1)) < i.succ := by simp
  have hh := h 0 i.succ hlt
  rw [List.get_cons_zero, List.get_cons_succ'] at hh
  rw [← hi]
  exact hh

/-- **The key step**: once the fold inside `reduceAgainst` has finished, the accumulator
is 0 on **every** pivot column of that state.

The induction separates the head row from the rest. For the remaining rows it uses the
induction hypothesis, which holds for an arbitrary starting vector; for the pivot column of
the head row it uses the fact that the remaining rows are all 0 on that column, so the fold
does not change it, together with the starting vector already being zero there. -/
lemma reduceAgainst_get_piv_eq_zero {D : List (PivRow n)} (v : Vec n) (h1 : EchSelf D)
    (h2 : EchPair D) : ∀ i : Fin D.length, (reduceAgainst D v) (D.get i).2 = 0 := by
  induction D generalizing v with
  | nil => intro i; exact i.elim0
  | cons r D ih =>
      rw [reduceAgainst_cons]
      intro i
      revert i
      refine Fin.cases ?_ ?_
      · simp only [List.get_cons_zero]
        refine reduceAgainst_eq_zero_of_rows_zero (hrows := h2.head_rows) ?_
        have hr : r.1 r.2 = 1 := by
          have hh := h1 (0 : Fin (D.length + 1))
          simpa [List.get_cons_zero] using hh
        rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hr, mul_one]
        exact CharTwo.add_self_eq_zero (v r.2)
      · simp only [List.get_cons_succ']
        exact ih _ h1.tail h2.tail

/-! ## Linear independence of the echelon rows -/

/-- **The rows of an echelon form are linearly independent**.

Take the **least index `j` whose coefficient in the linear combination is nonzero** and
evaluate on the pivot column of row `j`: terms with index below `j` have coefficient 0, and
rows with index above `j` are 0 on that column by `EchPair`, so the combination takes the
value `g j ≠ 0` there, contradicting the combination being zero. -/
theorem linearIndependent_get_of_echelon {D : List (PivRow n)} (h1 : EchSelf D) (h2 : EchPair D) :
    LinearIndependent (ZMod 2) (fun i : Fin D.length => (D.get i).1) := by
  rw [linearIndependent_iff']
  intro s g hsum
  by_contra hcon
  push Not at hcon
  obtain ⟨i₀, hi₀, hne₀⟩ := hcon
  have ht : (s.filter (fun a => g a ≠ 0)).Nonempty :=
    ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, hne₀⟩⟩
  set j := (s.filter (fun a => g a ≠ 0)).min' ht with hj
  have hjmem : j ∈ s ∧ g j ≠ 0 := Finset.mem_filter.mp (Finset.min'_mem _ ht)
  have hmin : ∀ a ∈ s, g a ≠ 0 → j ≤ a := fun a ha hae =>
    Finset.min'_le _ a (Finset.mem_filter.mpr ⟨ha, hae⟩)
  have hcol := congrFun hsum ((D.get j).2)
  rw [Finset.sum_apply] at hcol
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcol
  have hcongr : ∑ a ∈ s, g a * ((D.get a).1 ((D.get j).2))
      = ∑ a ∈ s, g a * (if a = j then (1 : ZMod 2) else 0) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    by_cases haj : a = j
    · rw [haj, ite_eq_left rfl, mul_one, h1 j, mul_one]
    · rcases lt_trichotomy j a with hlt | heq | hgt
      · rw [h2 j a hlt, ite_eq_right haj, mul_zero]
      · exact absurd heq.symm haj
      · have hg0 : g a = 0 := by
          by_contra hg
          exact absurd (hmin a ha hg) (not_le.mpr hgt)
        rw [hg0]; simp
  rw [hcongr] at hcol
  have hcollapse : ∑ a ∈ s, g a * (if a = j then (1 : ZMod 2) else 0) = g j := by
    have hh := Finset.sum_eq_single (s := s)
      (f := fun a => g a * (if a = j then (1 : ZMod 2) else 0)) j
      (fun b _ hne => by rw [ite_eq_right hne, mul_zero])
      (fun hnot => absurd hjmem.1 hnot)
    rwa [ite_eq_left rfl, mul_one] at hh
  rw [hcollapse] at hcol
  exact hjmem.2 hcol

/-! ## Preservation of the invariants by `stepA` and the main loop -/

lemma echSelf_nil : EchSelf ([] : List (PivRow n)) := by intro i; exact i.elim0

lemma echPair_nil : EchPair ([] : List (PivRow n)) := by intro i; exact i.elim0

lemma length_append_singleton (D : List (PivRow n)) (x : PivRow n) :
    (D ++ [x]).length = D.length + 1 := by simp [List.length_append]

/-- The `i`-th element of `(D ++ [x])`, for `i` within `D`, is the `i`-th element of
`D`.

For a variable `D`, `(D ++ [x]).length` is **not** defeq to `D.length + 1`, so the index is
written out explicitly as `⟨i.val, _⟩` rather than with `Fin.cast`, which avoids moving
proofs around at the level of `Fin`. -/
lemma get_append_singleton_cast (D : List (PivRow n)) (x : PivRow n) (i : Fin D.length) :
    (D ++ [x]).get ⟨i.val, by have h := length_append_singleton D x; have := i.isLt; omega⟩ =
      D.get i := by
  simp only [List.get_eq_getElem, List.getElem_append_left i.isLt]

/-- The last element of `(D ++ [x])` is `x`. -/
lemma get_append_singleton_last (D : List (PivRow n)) (x : PivRow n) :
    (D ++ [x]).get ⟨D.length, by have h := length_append_singleton D x; omega⟩ = x := by
  simp only [List.get_eq_getElem, List.getElem_append_right (Nat.le_refl D.length),
    Nat.sub_self, List.getElem_cons_zero]

lemma EchSelf_append (D : List (PivRow n)) (x : PivRow n) (hD : EchSelf D)
    (hx : x.1 x.2 = 1) : EchSelf (D ++ [x]) := by
  intro i
  rw [List.get_eq_getElem]
  by_cases h : (i : ℕ) < D.length
  · rw [List.getElem_append_left h]
    simpa [List.get_eq_getElem] using hD ⟨i.val, h⟩
  · have hlast : (D ++ [x])[(i : ℕ)] = x := by
      rw [List.getElem_append_right (by omega : D.length ≤ (i : ℕ))]
      simp [show (i : ℕ) - D.length = 0 from by
        have := length_append_singleton D x; omega]
    rw [hlast]
    exact hx

lemma EchPair_append (D : List (PivRow n)) (x : PivRow n) (hD : EchPair D)
    (hx : ∀ i : Fin D.length, x.1 (D.get i).2 = 0) : EchPair (D ++ [x]) := by
  intro i j hij
  simp only [List.get_eq_getElem]
  by_cases hj : (j : ℕ) < D.length
  · have hi : (i : ℕ) < D.length := by omega
    rw [List.getElem_append_left hj, List.getElem_append_left hi]
    exact hD ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij
  · have hjlast : (D ++ [x])[(j : ℕ)] = x := by
      rw [List.getElem_append_right (by omega : D.length ≤ (j : ℕ))]
      simp [show (j : ℕ) - D.length = 0 from by
        have := length_append_singleton D x; omega]
    have hi : (i : ℕ) < D.length := by
      have := length_append_singleton D x; omega
    rw [hjlast, List.getElem_append_left hi]
    simpa [List.get_eq_getElem] using hx ⟨i.val, hi⟩

lemma EchSelf_stepA {D : List (PivRow n)} (h1 : EchSelf D) (v : Vec n) :
    EchSelf (stepA D v) := by
  unfold stepA
  split
  · exact h1
  · rename_i hw
    exact EchSelf_append D _ h1 (leadIdx_eq_one (reduceAgainst D v) hw)

lemma EchPair_stepA {D : List (PivRow n)} (h1 : EchSelf D) (h2 : EchPair D) (v : Vec n) :
    EchPair (stepA D v) := by
  unfold stepA
  split
  · exact h2
  · rename_i hw
    exact EchPair_append D _ h2 fun i => reduceAgainst_get_piv_eq_zero v h1 h2 i

lemma echSelf_echelonFrom_foldl (D : List (PivRow n)) (L : List (Vec n))
    (h1 : EchSelf D) (h2 : EchPair D) :
    EchSelf (L.foldl stepA D) ∧ EchPair (L.foldl stepA D) := by
  induction L generalizing D with
  | nil => exact ⟨h1, h2⟩
  | cons v rest ih =>
      rw [List.foldl_cons]
      exact ih (stepA D v) (EchSelf_stepA h1 v) (EchPair_stepA h1 h2 v)

/-- The append-only echelon form satisfies the two invariants. -/
theorem echelonFrom_ech (L : List (Vec n)) :
    EchSelf (echelonFrom L) ∧ EchPair (echelonFrom L) :=
  echSelf_echelonFrom_foldl [] L echSelf_nil echPair_nil

/-! ## Rank readings -/

/-- **The rank equals the number of rows of the append-only echelon form**. -/
theorem finrank_spanL_eq_length_echelonFrom (L : List (Vec n)) :
    Module.finrank (ZMod 2) (spanL L) = (echelonFrom L).length := by
  have h := echelonFrom_ech L
  have hcard := finrank_span_eq_card (linearIndependent_get_of_echelon h.1 h.2)
  rw [range_get_eq_rowList] at hcard
  have hcard' : Module.finrank (ZMod 2) (spanL (rowList (echelonFrom L)))
      = Fintype.card (Fin (echelonFrom L).length) := hcard
  rw [Fintype.card_fin] at hcard'
  rw [← spanL_rowList_echelonFrom L]
  exact hcard'

/-- **The bridge theorem**: the append-only echelon form and `rowReduce` give the same
rank.

Both are outputs of the same greedy pivot count, with the same row space, and in both cases
the number of rows is the rank. Downstream rank and `k` claims can therefore **switch
backends** without any change to the mathematics; `rowReduce` and its downstream users
(canonical-form uniqueness in `GF2/Canonical.lean` relies on the RREF produced by
back-substitution) are untouched. -/
theorem rankEchelon_eq_length_rowReduce (L : List (Vec n)) :
    rankEchelon L = (rowReduce L).length := by
  rw [rankEchelon, ← finrank_spanL_eq_length_rowReduce L,
    finrank_spanL_eq_length_echelonFrom L]

/-- The interface in matrix form: the rank of a parity-check matrix. -/
theorem Matrix.rank_eq_rankEchelon {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    M.rank = rankEchelon (List.ofFn fun i => M i) := by
  rw [Matrix.rank_eq_length_rowReduce, rankEchelon_eq_length_rowReduce]

/-! ## A fast backend for the membership test (`echelonFrom` in place of `rowReduce`)

`inSpanB` in `GF2/Membership.lean` decides row-space membership from the output of
`rowReduce`. Where the test is recomputed **for every candidate**, as in the weight-bounded
enumeration of `lightCand`, this is a difference of orders of magnitude: on width 24,
`rowReduce` takes more than 200 s from the 7th row onwards, whereas `echelonFrom` takes
milliseconds.

**The key observation**: the membership test does **not** need the **full reduction** (RREF)
produced by `rowReduce`; **the append-only echelon form suffices**. The elimination argument
inside `reduceAgainst` uses only `EchPair`, that is, a later row being 0 on an earlier row's
pivot column, and the step that the RREF used to carry (a vector that lies in the row space
and is 0 on every pivot column must be zero) is supplied instead by taking the **least index
in the coefficient representation**. -/

/-- **In echelon form, all pivot columns zero implies zero**: if `w` lies in the span of
`rowList D` and is 0 on **every** pivot column of `D`, then `w = 0`.

The argument: take a coefficient representation `w = Σ cᵢ rᵢ` and let `j` be the **least**
index with `cⱼ ≠ 0`. Evaluating on `pⱼ`, the terms with `i > j` vanish by `EchPair` and
those with `i < j` have coefficient 0, so `w pⱼ = cⱼ ≠ 0`, contradicting the hypothesis.
This is exactly the part that the symmetry condition (R2) of `IsReduced` used to carry. -/
theorem eq_zero_of_mem_spanL_of_piv_eq_zero {D : List (PivRow n)} (h1 : EchSelf D)
    (h2 : EchPair D) {w : Vec n} (hw : w ∈ spanL (rowList D))
    (h0 : ∀ i : Fin D.length, w (D.get i).2 = 0) : w = 0 := by
  have hspan : spanL (rowList D)
      = Submodule.span (ZMod 2) (Set.range fun i : Fin D.length => (D.get i).1) := by
    rw [spanL, range_get_eq_rowList D]
  have hw' : w ∈ Submodule.span (ZMod 2)
      (Set.range fun i : Fin D.length => (D.get i).1) := by
    rw [← hspan]
    exact hw
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)
    (v := fun i : Fin D.length => (D.get i).1) (x := w)).mp hw'
  by_contra hw0
  have hex : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (by rw [← hc]; exact Finset.sum_eq_zero fun i _ => by rw [h i, zero_smul])
  obtain ⟨i₀, hi₀⟩ := hex
  have ht : (Finset.univ.filter (fun a => c a ≠ 0)).Nonempty :=
    ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hi₀⟩⟩
  set j := (Finset.univ.filter (fun a => c a ≠ 0)).min' ht with hj
  have hjne : c j ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem _ ht)).2
  have hmin : ∀ a, c a ≠ 0 → j ≤ a := fun a ha =>
    Finset.min'_le _ a (Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩)
  have hcol := congrFun hc ((D.get j).2)
  rw [Finset.sum_apply] at hcol
  simp only [Pi.smul_apply, smul_eq_mul] at hcol
  have hcongr : ∑ i, c i * ((D.get i).1 ((D.get j).2))
      = ∑ i, c i * (if i = j then (1 : ZMod 2) else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hij : i = j
    · rw [hij, ite_eq_left rfl, mul_one, h1 j, mul_one]
    · rcases lt_trichotomy i j with hlt | heq | hgt
      · -- Minimality kills earlier coefficients; the echelon condition controls later rows.
        have hc0 : c i = 0 := by
          by_contra hc'
          exact absurd (hmin i hc') (not_le.mpr hlt)
        rw [hc0]; simp
      · exact absurd heq hij
      · rw [h2 j i hgt, ite_eq_right hij, mul_zero]
  rw [hcongr] at hcol
  have hcollapse : ∑ i, c i * (if i = j then (1 : ZMod 2) else 0) = c j := by
    have hh := Finset.sum_eq_single (s := Finset.univ)
      (f := fun i => c i * (if i = j then (1 : ZMod 2) else 0)) j
      (fun b _ hne => by rw [ite_eq_right hne, mul_zero])
      (fun hnot => absurd (Finset.mem_univ j) hnot)
    rwa [ite_eq_left rfl, mul_one] at hh
  rw [hcollapse] at hcol
  exact hjne (by rw [hcol, h0 j])

/-- **The reduction vanishes exactly on the row space (echelon backend)**: the output of
`echelonFrom` annihilates the span of the original list of rows.

This is parallel to `reduceAgainst_eq_zero_of_mem_spanL` in `GF2/Membership.lean`, the
`IsReduced` version, but the hypotheses here use only `EchSelf` and `EchPair`; the step that
the RREF used to carry is supplied by `eq_zero_of_mem_spanL_of_piv_eq_zero`. -/
theorem reduceAgainst_echelonFrom_eq_zero_of_mem_spanL {L : List (Vec n)} {v : Vec n}
    (hv : v ∈ spanL L) : reduceAgainst (echelonFrom L) v = 0 := by
  have hech := echelonFrom_ech L
  have hmem : v + reduceAgainst (echelonFrom L) v ∈ spanL L := by
    have h := add_reduceAgainst_mem (echelonFrom L) v
    rwa [spanL_rowList_echelonFrom] at h
  refine eq_zero_of_mem_spanL_of_piv_eq_zero hech.1 hech.2 ?_
    (reduceAgainst_get_piv_eq_zero v hech.1 hech.2)
  rw [spanL_rowList_echelonFrom]
  have hsplit : (v + reduceAgainst (echelonFrom L) v) + v
      = reduceAgainst (echelonFrom L) v := by
    rw [add_assoc, add_add_same_right]
  rw [← hsplit]
  exact Submodule.add_mem _ hmem hv

/-! ## Computable membership test: echelon backend

The same mathematical content and the same interface shape as `inSpanB` in
`GF2/Membership.lean`, with only the reduction backend changed. Where the test is run once
per candidate, as in the weight-bounded enumeration of `lightCand`, which has 2325
candidates for $[[24,3,4]]$, this is a difference of orders of magnitude: on width 24,
`rowReduce` fails to converge after the 7th row and takes more than 200 s, whereas
`echelonFrom` takes milliseconds. -/

/-- **Computable row-space membership test (echelon backend)**. -/
def inSpanEch (L : List (Vec n)) (v : Vec n) : Bool :=
  decide (reduceAgainst (echelonFrom L) v = 0)

theorem inSpanEch_sound {L : List (Vec n)} {v : Vec n} (h : inSpanEch L v = true) :
    v ∈ spanL L := by
  unfold inSpanEch at h
  rw [decide_eq_true_eq] at h
  have hmem : v + reduceAgainst (echelonFrom L) v ∈ spanL (rowList (echelonFrom L)) :=
    add_reduceAgainst_mem (echelonFrom L) v
  rw [h, add_zero] at hmem
  rwa [spanL_rowList_echelonFrom] at hmem

theorem inSpanEch_complete {L : List (Vec n)} {v : Vec n} (hv : v ∈ spanL L) :
    inSpanEch L v = true := by
  unfold inSpanEch
  rw [decide_eq_true_eq]
  exact reduceAgainst_echelonFrom_eq_zero_of_mem_spanL hv

/-- **Semantic equivalence of the membership test (echelon backend)**: the same Boolean
value as `inSpanB`. -/
theorem inSpanEch_iff (L : List (Vec n)) (v : Vec n) :
    inSpanEch L v = true ↔ v ∈ spanL L :=
  ⟨inSpanEch_sound, inSpanEch_complete⟩

/-! ## Explicit rank certificates

The cost of row reduction rises steeply with **width**. Where the width is large enough that
`rowReduce` and `echelonFrom` no longer finish, the rank can still be obtained **by checking
a certificate**. There is a cheap criterion on each side:

* **Lower bound**: produce a list `D` of candidate rows with **pairwise distinct pivots**,
  each of them lying in `spanL L`. If those rows are **defined** as linear combinations of
  rows of `L`, assembled term by term with `Submodule.add_mem`, membership is algebraic and
  independent of the width, while distinctness of the pivots is a finite check that `decide`
  can perform. Hence `D.length ≤ dim spanL L`
  (`length_le_finrank_spanL_of_certificate`).
* **Upper bound**: produce **redundant generators**, that is, write `L` as `A ++ B` and
  prove that every row of `B` lies in `spanL A`; then `dim spanL L ≤ A.length`
  (`finrank_spanL_append_le_of_mem`). Each redundancy is a single equality check of the
  form "this row is a sum of rows", which `decide` can perform.

Both are **row-by-row or relation-by-relation** checks, so their cost is linear in the
width; an instance at width 98 comes with the companion development, where row reduction is
not available (see its module header). -/

/-- **The dimension of `spanL A` is at most the length of `A`**: `A` is a generating
set. -/
theorem finrank_spanL_le_length (A : List (Vec n)) :
    Module.finrank (ZMod 2) (spanL A) ≤ A.length := by
  have h : spanL A = Submodule.span (ZMod 2) (Set.range fun i : Fin A.length => A.get i) := by
    rw [spanL]
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    exact List.mem_iff_get
  rw [h]
  calc Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range fun i : Fin A.length => A.get i))
      ≤ (Set.range (fun i : Fin A.length => A.get i)).toFinset.card := finrank_span_le_card _
    _ = Fintype.card ↑(Set.range fun i : Fin A.length => A.get i) := Set.toFinset_card _
    _ ≤ Fintype.card (Fin A.length) := Fintype.card_range_le _
    _ = A.length := Fintype.card_fin _

/-- **A rank upper bound from redundant generators (set form)**: if every row of `L`
lies in `spanL A`, then `dim spanL L ≤ A.length`. The list `A` need not be a prefix of `L`,
since `spanL` sees only the underlying set, so picking `head` rows of `L` that span the whole
list and having the whole list generated by those `head` generators come to the same thing.
The parity-check matrix of `BB144` has its first 66 rows of deficient rank (rank 64), so
only this form applies. -/
theorem finrank_spanL_le_of_mem_of_subset {A L : List (Vec n)}
    (h : ∀ v ∈ L, v ∈ spanL A) :
    Module.finrank (ZMod 2) (spanL L) ≤ A.length := by
  have hle : spanL L ≤ spanL A := Submodule.span_le.mpr h
  exact le_trans (Submodule.finrank_mono hle) (finrank_spanL_le_length A)

/-- **A rank upper bound from redundant generators (prefix form)**: write the list of
rows as `A ++ B`; if every row of `B` lies in `spanL A`, then the dimension of the whole
list is at most `A.length`. -/
theorem finrank_spanL_append_le_of_mem (A B : List (Vec n))
    (h : ∀ v ∈ B, v ∈ spanL A) :
    Module.finrank (ZMod 2) (spanL (A ++ B)) ≤ A.length := by
  have hA : ∀ v ∈ A ++ B, v ∈ spanL A := by
    intro v hv
    rw [List.mem_append] at hv
    rcases hv with hv | hv
    · exact subset_spanL hv
    · exact h v hv
  exact finrank_spanL_le_of_mem_of_subset hA

/-- **A rank lower bound from a certificate**: if every row of `D` lies in `spanL L` and
`D` satisfies the echelon invariants, then `D.length ≤ dim spanL L`. -/
theorem length_le_finrank_spanL_of_certificate {L : List (Vec n)} {D : List (PivRow n)}
    (hsub : ∀ i : Fin D.length, (D.get i).1 ∈ spanL L)
    (h1 : EchSelf D) (h2 : EchPair D) :
    D.length ≤ Module.finrank (ZMod 2) (spanL L) := by
  have hcard := finrank_span_eq_card (linearIndependent_get_of_echelon h1 h2)
  rw [range_get_eq_rowList] at hcard
  have hcard' : Module.finrank (ZMod 2) (spanL (rowList D)) = Fintype.card (Fin D.length) := hcard
  rw [Fintype.card_fin] at hcard'
  have hle : spanL (rowList D) ≤ spanL L := by
    rw [spanL, Submodule.span_le]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    exact hsub i
  calc D.length = Module.finrank (ZMod 2) (spanL (rowList D)) := hcard'.symm
    _ ≤ Module.finrank (ZMod 2) (spanL L) := Submodule.finrank_mono hle

/-- **Negative form (echelon backend)**: consumed on the lower-bound side. -/
theorem inSpanEch_eq_false_iff (L : List (Vec n)) (v : Vec n) :
    inSpanEch L v = false ↔ v ∉ spanL L := by
  constructor
  · intro h hv
    rw [(inSpanEch_iff L v).mpr hv] at h
    exact absurd h (by decide)
  · intro h
    cases hb : inSpanEch L v with
    | false => rfl
    | true => exact absurd ((inSpanEch_iff L v).mp hb) h

end QECCertificates
