/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module
public import LeanPool.QECCertificates.GF2.Basic

/-!
# Verified GF(2) row reduction

LeanQEC lists "row reduction itself is not formalized" as its most concrete remaining
engineering gap: "A verified row-reduction routine would close this remaining
preprocessor step." This module supplies that step, turning the **row simplification**
of a parity-check matrix into a machine-checked algorithm, so that the preprocessing no
longer requires trusting an external script.

## Invariants

The state of the reduction is a list of **pivot rows** `PivRow n = Vec n × Fin n`,
a row vector together with the column at which it pivots. `IsReduced D` requires:

* **(R1)** every row takes the value 1 at its own pivot column
* **(R2)** every row takes the value 0 at the pivot column of every **other** row.

(R2) is **symmetric**: it does not presuppose an order on the rows, so the result is
independent of the elimination order. This is what makes all the correctness proofs
below go through.

## Main results

* `reduceAgainst_apply_piv`: the reduced vector is 0 at every pivot column.
* `add_reduceAgainst_mem`: `v + reduceAgainst D v` lies in the row space of `D`.
* `spanL_rowReduce`: **the row space is unchanged**, so the code is not modified.
* `isReduced_rowReduce`: the output satisfies `IsReduced`.
-/

@[expose] public section

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-- A pivot row: a row vector together with the column at which it pivots, that is, its leading
    nonzero entry. -/
abbrev PivRow (n : ℕ) := Vec n × Fin n

/-- The row part of a list of pivot rows. -/
def rowList (D : List (PivRow n)) : List (Vec n) := D.map (·.1)

@[simp] lemma rowList_nil : rowList ([] : List (PivRow n)) = [] := rfl
@[simp] lemma rowList_cons (ri : PivRow n) (D : List (PivRow n)) :
    rowList (ri :: D) = ri.1 :: rowList D := rfl
@[simp] lemma rowList_append (D E : List (PivRow n)) :
    rowList (D ++ E) = rowList D ++ rowList E := List.map_append

/-- **The mutual-reduction invariant**: (R1) every row is 1 at its own pivot column, and (R2)
    every row is 0 at the pivot column of every other row. -/
def IsReduced (D : List (PivRow n)) : Prop :=
  (∀ ri ∈ D, ri.1 ri.2 = 1) ∧ (∀ ri ∈ D, ∀ rj ∈ D, ri ≠ rj → ri.1 rj.2 = 0)

lemma isReduced_nil : IsReduced ([] : List (PivRow n)) := ⟨by simp, by simp⟩

/-- Immediate consequence of (R2): the pivot columns are pairwise distinct. -/
lemma IsReduced.pivot_inj {D : List (PivRow n)} (h : IsReduced D) :
    ∀ ri ∈ D, ∀ rj ∈ D, ri.2 = rj.2 → ri = rj := by
  intro ri hri rj hrj hij
  by_contra hne
  have h1 := h.1 ri hri
  have h2 := h.2 ri hri rj hrj hne
  rw [← hij] at h2
  rw [h1] at h2
  exact one_ne_zero h2

/-! ## Reduction: clearing a row at every pivot column -/

/-- Eliminate `v` at its pivot column using each row of `D`. Over GF(2) the coefficient is exactly
    the component of `v` at that column. -/
def reduceAgainst (D : List (PivRow n)) (v : Vec n) : Vec n :=
  D.foldl (fun w ri => w + (w ri.2) • ri.1) v

@[simp] lemma reduceAgainst_nil (v : Vec n) : reduceAgainst ([] : List (PivRow n)) v = v := rfl

lemma reduceAgainst_cons (ri : PivRow n) (D : List (PivRow n)) (v : Vec n) :
    reduceAgainst (ri :: D) v = reduceAgainst D (v + (v ri.2) • ri.1) := by
  simp [reduceAgainst, List.foldl_cons]

/-- If every row of `D` is 0 at column `q` and `v q = 0`, then the reduced vector is still 0 at
    position `q`. -/
lemma reduceAgainst_eq_zero_of_rows_zero {D : List (PivRow n)} {q : Fin n} {v : Vec n}
    (hrows : ∀ ri ∈ D, ri.1 q = 0) (hv : v q = 0) : reduceAgainst D v q = 0 := by
  induction D generalizing v with
  | nil => simpa using hv
  | cons ri D ih =>
      rw [reduceAgainst_cons]
      refine ih ?_ ?_
      · intro rk hrk
        exact hrows rk (List.mem_cons_of_mem ri hrk)
      · rw [Pi.add_apply, Pi.smul_apply, hrows ri (List.mem_cons_self ..), smul_eq_mul, hv,
          mul_zero, add_zero]

/-- **Core lemma**: when `D` is mutually reduced, the reduced vector is 0 at every pivot column. -/
lemma reduceAgainst_apply_piv {D : List (PivRow n)} (hD : IsReduced D) (v : Vec n) :
    ∀ ri ∈ D, reduceAgainst D v ri.2 = 0 := by
  revert hD
  induction D generalizing v with
  | nil => intro _ ri hri; exact absurd hri (by simp)
  | cons r D ih =>
      intro hD
      have hD' : IsReduced D :=
        ⟨fun ri hri => hD.1 ri (List.mem_cons_of_mem r hri),
         fun ri hri rj hrj hne =>
           hD.2 ri (List.mem_cons_of_mem r hri) rj (List.mem_cons_of_mem r hrj) hne⟩
      rw [reduceAgainst_cons]
      intro ri hri
      rcases List.mem_cons.mp hri with hri_eq | hriD
      · rw [hri_eq]
        by_cases hrD : r ∈ D
        · exact ih _ hD' r hrD
        · refine reduceAgainst_eq_zero_of_rows_zero ?_
            (addSmul_zero_coord v r.1 r.2 (hD.1 r (List.mem_cons_self ..)))
          intro rk hrk
          exact hD.2 rk (List.mem_cons_of_mem r hrk) r (List.mem_cons_self ..)
            (fun h => hrD (h ▸ hrk))
      · exact ih _ hD' ri hriD

/-- **Where the reduced part lands**: `v + reduceAgainst D v` is a linear combination of the row
    vectors of `D`. -/
lemma add_reduceAgainst_mem (D : List (PivRow n)) (v : Vec n) :
    v + reduceAgainst D v ∈ spanL (rowList D) := by
  induction D generalizing v with
  | nil => simp
  | cons r D ih =>
      rw [reduceAgainst_cons]
      have hr : r.1 ∈ spanL (rowList (r :: D)) := subset_spanL (by simp)
      have hih : (v + (v r.2) • r.1) + reduceAgainst D (v + (v r.2) • r.1) ∈ spanL (rowList D) :=
        ih _
      have hih' : (v + (v r.2) • r.1) + reduceAgainst D (v + (v r.2) • r.1)
          ∈ spanL (rowList (r :: D)) :=
        spanL_mono_of_subset (by intro x hx; exact List.mem_cons_of_mem r.1 hx) hih
      have hmem := Submodule.add_mem _ (Submodule.smul_mem _ (v r.2) hr) hih'
      have key : v + reduceAgainst D (v + (v r.2) • r.1)
          = (v r.2) • r.1 + ((v + (v r.2) • r.1) + reduceAgainst D (v + (v r.2) • r.1)) := by
        rw [← add_assoc]
        congr 1
        exact (add_add_same_right ((v r.2) • r.1) v).symm
      rw [key]
      exact hmem

/-! ## Choosing a pivot and inserting -/

lemma support_nonempty {v : Vec n} (h : v ≠ 0) :
    (Finset.univ.filter (fun i => v i ≠ 0)).Nonempty := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (funext hc)
  exact ⟨i, by simp [hi]⟩

/-- The position of the first nonzero component, defined when `v ≠ 0`. -/
def leadIdx (v : Vec n) (h : v ≠ 0) : Fin n :=
  (Finset.univ.filter (fun i => v i ≠ 0)).min' (support_nonempty h)

lemma leadIdx_spec (v : Vec n) (h : v ≠ 0) : v (leadIdx v h) ≠ 0 := by
  unfold leadIdx
  have hm := Finset.min'_mem (Finset.univ.filter (fun i => v i ≠ 0)) (support_nonempty h)
  simpa using hm

lemma leadIdx_eq_one (v : Vec n) (h : v ≠ 0) : v (leadIdx v h) = 1 :=
  eq_one_of_ne_zero (leadIdx_spec v h)

/-- Insert the new row `w`, whose pivot column is `p`, into the set of pivot rows: first clear the
    old rows at column `p`, then append `w`. -/
def insertPivot (D : List (PivRow n)) (w : Vec n) (p : Fin n) : List (PivRow n) :=
  D.map (fun ri => (ri.1 + (ri.1 p) • w, ri.2)) ++ [(w, p)]

lemma rowList_insertPivot (D : List (PivRow n)) (w : Vec n) (p : Fin n) :
    rowList (insertPivot D w p) = (rowList D).map (fun r => r + (r p) • w) ++ [w] := by
  simp [rowList, insertPivot, List.map_map, Function.comp_def]

/-- Insertion does not change the row space. -/
lemma spanL_rowList_insertPivot (D : List (PivRow n)) (w : Vec n) (p : Fin n) :
    spanL (rowList (insertPivot D w p)) = spanL (rowList D ++ [w]) := by
  rw [rowList_insertPivot]
  exact spanL_map_addSmul_append _ _ _

/-- Insertion preserves the mutual-reduction invariant: it requires `w` to be 0 at every pivot
    column of `D` and 1 at the new pivot column. -/
lemma isReduced_insertPivot {D : List (PivRow n)} (hD : IsReduced D) {w : Vec n} {p : Fin n}
    (hp : w p = 1) (hz : ∀ ri ∈ D, w ri.2 = 0) : IsReduced (insertPivot D w p) := by
  constructor
  · intro rj hrj
    rcases List.mem_append.mp hrj with hmap | hsingle
    · obtain ⟨ri, hri, rfl⟩ := List.mem_map.mp hmap
      change (ri.1 + (ri.1 p) • w) ri.2 = 1
      rw [Pi.add_apply, Pi.smul_apply, hz ri hri, smul_eq_mul, mul_zero, add_zero]
      exact hD.1 ri hri
    · have hw : rj = (w, p) := by simpa using hsingle
      rw [hw]; exact hp
  · intro ri hri rj hrj hne
    rcases List.mem_append.mp hri with hmi | hsi <;> rcases List.mem_append.mp hrj with hmj | hsj
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmi
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hmj
      have hab : a.2 ≠ b.2 := by
        intro hcon
        exact hne (by rw [hD.pivot_inj a ha b hb hcon])
      change (a.1 + (a.1 p) • w) b.2 = 0
      rw [Pi.add_apply, Pi.smul_apply, hz b hb, smul_eq_mul, mul_zero, add_zero]
      exact hD.2 a ha b hb (fun h => hab (by rw [h]))
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmi
      have hwj : rj = (w, p) := by simpa using hsj
      subst hwj
      change (a.1 + (a.1 p) • w) p = 0
      rw [Pi.add_apply, Pi.smul_apply, hp, smul_eq_mul, mul_one]
      exact CharTwo.add_self_eq_zero (a.1 p)
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmj
      have hwi : ri = (w, p) := by simpa using hsi
      subst hwi
      exact hz a ha
    · have hwi : ri = (w, p) := by simpa using hsi
      have hwj : rj = (w, p) := by simpa using hsj
      exact absurd (hwi.trans hwj.symm) hne

/-! ## The main loop -/

/-- One step: reduce `v` and, if the result is nonzero, insert it as a new pivot row. -/
def step (D : List (PivRow n)) (v : Vec n) : List (PivRow n) :=
  if hw : reduceAgainst D v = 0 then D
  else insertPivot D (reduceAgainst D v) (leadIdx (reduceAgainst D v) hw)

lemma spanL_rowList_step (D : List (PivRow n)) (v : Vec n) :
    spanL (rowList (step D v)) = spanL (rowList D ++ [v]) := by
  unfold step
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
    rw [spanL_rowList_insertPivot]
    exact spanL_append_eq_of_add_mem (add_reduceAgainst_mem D v)

lemma isReduced_step {D : List (PivRow n)} (hD : IsReduced D) (v : Vec n) :
    IsReduced (step D v) := by
  unfold step
  split
  · exact hD
  · rename_i hw
    exact isReduced_insertPivot hD (leadIdx_eq_one (reduceAgainst D v) hw)
      (reduceAgainst_apply_piv hD v)

/-- Insert the rows of `rest` one by one, starting from the accumulated state `D`. -/
def rowReduceFrom (D : List (PivRow n)) : List (Vec n) → List (PivRow n)
  | [] => D
  | v :: rest => rowReduceFrom (step D v) rest

@[simp] lemma rowReduceFrom_nil (D : List (PivRow n)) : rowReduceFrom D [] = D := rfl

@[simp] lemma rowReduceFrom_cons (D : List (PivRow n)) (v : Vec n) (rest : List (Vec n)) :
    rowReduceFrom D (v :: rest) = rowReduceFrom (step D v) rest := rfl

lemma spanL_rowList_rowReduceFrom (D : List (PivRow n)) (rest : List (Vec n)) :
    spanL (rowList (rowReduceFrom D rest)) = spanL (rowList D ++ rest) := by
  induction rest generalizing D with
  | nil => simp
  | cons v rest ih =>
      rw [rowReduceFrom_cons, ih]
      have hassoc : rowList D ++ (v :: rest) = (rowList D ++ [v]) ++ rest := by
        rw [List.append_assoc]; rfl
      rw [hassoc, spanL_append, spanL_append, spanL_rowList_step]

lemma isReduced_rowReduceFrom {D : List (PivRow n)} (hD : IsReduced D) (rest : List (Vec n)) :
    IsReduced (rowReduceFrom D rest) := by
  induction rest generalizing D with
  | nil => exact hD
  | cons v rest ih => rw [rowReduceFrom_cons]; exact ih (isReduced_step hD v)

/-- **Verified row reduction**: reduce a list of rows to a mutually reduced set of pivot rows. -/
def rowReduce (L : List (Vec n)) : List (PivRow n) := rowReduceFrom [] L

/-- **The row space is unchanged**: elimination does not change the row space, hence does not
    change the code it defines. -/
theorem spanL_rowReduce (L : List (Vec n)) : spanL (rowList (rowReduce L)) = spanL L := by
  have h := spanL_rowList_rowReduceFrom ([] : List (PivRow n)) L
  simpa [rowReduce] using h

/-- **The output is mutually reduced**: the result is a set of pivot rows, each of them 1 at its
    own pivot column and 0 at the others. -/
theorem isReduced_rowReduce (L : List (Vec n)) : IsReduced (rowReduce L) :=
  isReduced_rowReduceFrom isReduced_nil L

end QECCertificates
