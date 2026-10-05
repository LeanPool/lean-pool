/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module
public import LeanPool.QECCertificates.GF2.RankCertificate

/-!
# Canonical form uniqueness: the elimination output of a row space is a canonical invariant

An earlier module supplies the trusted row reduction `rowReduce` (the row space is preserved and
the output is mutually reduced) and proves that its length is the rank. This module adds the last
piece: **the elimination output is the canonical form of the row space**, that is, two row lists
spanning the same row space have the **same set of rows** after elimination. Whether two codes
agree can then be decided by the kernel by comparing elimination outputs directly, instead of
expanding to $2^n$ vectors and comparing them one by one.

## Why `IsEchelon` is needed

`IsReduced` **alone** does not determine the canonical form: for `[(r, p)]`, every non-zero
component column `p` of `r` satisfies the mutual-reduction invariant ((R2) imposes no constraint
when there is a single row). What the row space really determines is
**pivot column = the first non-zero column of the row** (`leadIdx`), and an elimination output
satisfies exactly that. It is recorded as a separate structural invariant:

`IsEchelon D := IsReduced D ∧ every row is zero before its pivot column`.

## Skeleton of the proof

1. **Read-off** (`readOff`): `readOff D w = Σ_{ri ∈ D} (w ri.2) • ri.1`. When `D` is mutually
   reduced this is the **identity map** on the row space (`readOff_eq_of_mem_spanL`, proved by
   `Submodule.span_induction`: it is the identity on the generators and linear under addition and
   scalar multiplication). This lemma translates "an element of the row space" into "its values on
   the pivot columns", and it is the entry point for every structural assertion.
2. **The row-space characterisation of the pivot set** (`exists_piv_eq_leadIdx_of_mem_spanL`): the
   first non-zero column of **any** non-zero element of the row space is a pivot column of `D`.
   The proof is the read-off computed term by term: take the pivot row whose coefficient is
   non-zero and whose pivot is smallest; pivot rows above it vanish in that column (`IsEchelon`)
   and the coefficients below it are zero.
3. **Putting the two together**: when two echelon row lists span the same row space, the
   characterisation above pins the two pivot sets to the same set (`hPiv12`/`hPiv21`), and
   read-off together with (R1)/(R2) then pins each row as well.

## Main results

* `readOff_eq_of_mem_spanL`: the read-off is the identity on the row space.
* `pivRow_mem_iff_of_spanL_eq`: **canonical form uniqueness**.
* `isEchelon_rowReduce`, `rowReduce_mem_iff_of_spanL_eq`: the output set of `rowReduce` depends
  only on the row space (it is a canonical invariant).
-/

@[expose] public section

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-! ## Read-off -/

/-- **Read-off**: recombines the values of `w` on its pivot columns, following the pivot rows of
    `D`.
When `D` is mutually reduced it is the identity map on the row space. -/
def readOff (D : List (PivRow n)) (w : Vec n) : Vec n :=
  ∑ ri ∈ D.toFinset, (w ri.2) • ri.1

@[simp] lemma readOff_nil (w : Vec n) : readOff ([] : List (PivRow n)) w = 0 := by
  simp [readOff]

/-- Componentwise form: the smul expanded into scalar multiplication. -/
lemma readOff_apply (D : List (PivRow n)) (w : Vec n) (i : Fin n) :
    readOff D w i = ∑ ri ∈ D.toFinset, (w ri.2) * (ri.1 i) := by
  rw [readOff, Finset.sum_apply]
  exact Finset.sum_congr rfl fun ri _ => by rw [Pi.smul_apply, smul_eq_mul]

lemma readOff_add (D : List (PivRow n)) (x y : Vec n) :
    readOff D (x + y) = readOff D x + readOff D y := by
  simp only [readOff]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ri _ => by rw [Pi.add_apply, add_smul]

lemma readOff_smul (D : List (PivRow n)) (c : ZMod 2) (x : Vec n) :
    readOff D (c • x) = c • readOff D x := by
  simp only [readOff]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun ri _ => by
    rw [Pi.smul_apply, smul_eq_mul, smul_smul]

/-- **Main lemma (read-off = identity)**: when `D` is mutually reduced, the read-off is the identity
map on the row space of `D`.

The proof follows `Submodule.span_induction`: on a generator, the pivot column of `ri` collapses the
sum to a single term (the remaining terms are killed by (R2)); the zero, addition and scalar cases
are given by `readOff_add`/`readOff_smul`. -/
theorem readOff_eq_of_mem_spanL {D : List (PivRow n)} (hD : IsReduced D) {w : Vec n}
    (hw : w ∈ spanL (rowList D)) : readOff D w = w := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · intro x hx
    obtain ⟨ri, hri, hri1⟩ := List.mem_map.mp hx
    rw [← hri1]
    simp only [readOff]
    refine (Finset.sum_eq_single (s := D.toFinset)
      (f := fun rj : PivRow n => (ri.1 rj.2) • rj.1) ri ?_ ?_).trans ?_
    · intro rj hrj hne
      rw [hD.2 ri hri rj (List.mem_toFinset.mp hrj) hne.symm, zero_smul]
    · intro hnot
      exact absurd (List.mem_toFinset.mpr hri) hnot
    · rw [hD.1 ri hri, one_smul]
  · simp only [readOff]
    refine Finset.sum_eq_zero fun ri _ => ?_
    rw [Pi.zero_apply, zero_smul]
  · intro x y _ _ hx hy
    rw [readOff_add, hx, hy]
  · intro c x _ hx
    rw [readOff_smul, hx]

/-- **The vanishing lemma**: an element of the row space that takes the value zero on every pivot
column is the zero vector.
(A corollary of the read-off, and the direct form of "the values on the pivot columns determine
everything".) -/
lemma eq_zero_of_mem_spanL_of_piv_zero {D : List (PivRow n)} (hD : IsReduced D) {w : Vec n}
    (hw : w ∈ spanL (rowList D)) (h0 : ∀ ri ∈ D, w ri.2 = 0) : w = 0 := by
  rw [← readOff_eq_of_mem_spanL hD hw]
  simp only [readOff]
  exact Finset.sum_eq_zero fun ri hri => by
    rw [h0 ri (List.mem_toFinset.mp hri), zero_smul]

/-! ## The echelon structure: the pivot column is the first non-zero column -/

/-- **Echelon and mutually reduced**: `IsReduced` together with "everything before the pivot column
is zero".

The second condition pins the pivot column to `leadIdx` (the first non-zero column of the row).
Without it, `[(r, p)]` (with `p` any non-zero component column of `r`) is mutually reduced, and the
canonical form is not unique. -/
def IsEchelon (D : List (PivRow n)) : Prop :=
  IsReduced D ∧ ∀ ri ∈ D, ∀ i : Fin n, i < ri.2 → ri.1 i = 0

/-- A row that takes the value 1 on its pivot column is non-zero. -/
lemma ne_zero_of_piv_eq_one {v : Vec n} {p : Fin n} (h : v p = 1) : v ≠ 0 :=
  fun hzero => by rw [hzero, Pi.zero_apply] at h; exact one_ne_zero h.symm

lemma leadIdx_le_of_ne_zero {v : Vec n} (h : v ≠ 0) {i : Fin n} (hi : v i ≠ 0) :
    leadIdx v h ≤ i :=
  Finset.min'_le _ i (by simp [hi])

/-- Everything before `leadIdx` is zero. -/
lemma eq_zero_of_lt_leadIdx {v : Vec n} (h : v ≠ 0) {i : Fin n} (hi : i < leadIdx v h) :
    v i = 0 := by
  by_contra hne
  exact absurd (leadIdx_le_of_ne_zero h hne) (not_le.mpr hi)

/-- The pivot column of an echelon row list is the `leadIdx` of its row. -/
lemma leadIdx_eq_piv_of_isEchelon {D : List (PivRow n)} (h : IsEchelon D) {ri : PivRow n}
    (hri : ri ∈ D) {hne : ri.1 ≠ 0} : leadIdx ri.1 hne = ri.2 := by
  refine le_antisymm ?_ ?_
  · exact leadIdx_le_of_ne_zero hne (by rw [h.1.1 ri hri]; exact one_ne_zero)
  · by_contra hlt
    exact absurd (h.2 ri hri (leadIdx ri.1 hne) (not_le.mp hlt)) (leadIdx_spec ri.1 hne)

/-! ## The row-space characterisation of the pivot set -/

/-- **Main lemma (pivot characterisation)**: in the row space spanned by an echelon row list, the
first non-zero column of any non-zero element is one of the pivot columns of that list.

The characterisation uses only the row space itself, so it turns the "pivot set" into an
**invariant of the row space**, and canonical form uniqueness follows. -/
theorem exists_piv_eq_leadIdx_of_mem_spanL {D : List (PivRow n)} (hD : IsEchelon D)
    {w : Vec n} (hw : w ∈ spanL (rowList D)) (hw0 : w ≠ 0) :
    ∃ ri ∈ D, ri.2 = leadIdx w hw0 := by
  have hwr : w = readOff D w := (readOff_eq_of_mem_spanL hD.1 hw).symm
  let S : Finset (PivRow n) := D.toFinset.filter (fun ri => w ri.2 ≠ 0)
  have hSne : S.Nonempty := by
    by_contra hemp
    have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hemp
    refine hw0 ?_
    rw [hwr]
    simp only [readOff]
    refine Finset.sum_eq_zero fun ri hri => ?_
    by_cases hc : w ri.2 = 0
    · rw [hc, zero_smul]
    · exfalso
      have hmemS : ri ∈ S := Finset.mem_filter.mpr ⟨hri, hc⟩
      rw [hSempty] at hmemS
      exact absurd hmemS (Finset.notMem_empty ri)
  obtain ⟨ri₀, hri₀S, hmin⟩ := Finset.exists_min_image S (fun ri => ri.2) hSne
  have hri₀D : ri₀ ∈ D := List.mem_toFinset.mp (Finset.mem_filter.mp hri₀S).1
  have hcoef : w ri₀.2 ≠ 0 := (Finset.mem_filter.mp hri₀S).2
  have hzero : ∀ i : Fin n, w i ≠ 0 → ri₀.2 ≤ i := by
    intro i hi
    by_contra hlt
    have hlt' : i < ri₀.2 := not_le.mp hlt
    refine hi ?_
    rw [hwr, readOff_apply]
    refine Finset.sum_eq_zero fun ri hri => ?_
    by_cases hc : w ri.2 = 0
    · rw [hc, zero_mul]
    · have hriS : ri ∈ S := Finset.mem_filter.mpr ⟨hri, hc⟩
      rw [hD.2 ri (List.mem_toFinset.mp hri) i
        (lt_of_lt_of_le hlt' (hmin ri hriS)), mul_zero]
  refine ⟨ri₀, hri₀D, ?_⟩
  have hlead : leadIdx w hw0 = ri₀.2 :=
    le_antisymm (leadIdx_le_of_ne_zero hw0 hcoef) (hzero (leadIdx w hw0) (leadIdx_spec w hw0))
  exact hlead.symm

/-! ## Canonical form uniqueness -/

/-- **Canonical form uniqueness**: two echelon mutually reduced row lists that span the same row
    space
have the same set of rows.

Hence the output of `rowReduce` is a **canonical invariant** of the row space: two codes agree
exactly when the row sets of their elimination outputs agree (`rowReduce_mem_iff_of_spanL_eq`). -/
theorem pivRow_mem_iff_of_spanL_eq {D₁ D₂ : List (PivRow n)} (h₁ : IsEchelon D₁)
    (h₂ : IsEchelon D₂) (hspan : spanL (rowList D₁) = spanL (rowList D₂)) :
    ∀ x : PivRow n, x ∈ D₁ ↔ x ∈ D₂ := by
  have hPiv12 : ∀ ri ∈ D₁, ∃ rj ∈ D₂, rj.2 = ri.2 := by
    intro ri hri
    have hne : ri.1 ≠ 0 := ne_zero_of_piv_eq_one (h₁.1.1 ri hri)
    have hmem : ri.1 ∈ spanL (rowList D₂) :=
      hspan ▸ subset_spanL (List.mem_map_of_mem hri)
    obtain ⟨rj, hrj, hrj2⟩ := exists_piv_eq_leadIdx_of_mem_spanL h₂ hmem hne
    exact ⟨rj, hrj, by rw [hrj2, leadIdx_eq_piv_of_isEchelon h₁ hri (hne := hne)]⟩
  have hPiv21 : ∀ rj ∈ D₂, ∃ ri ∈ D₁, ri.2 = rj.2 := by
    intro rj hrj
    have hne : rj.1 ≠ 0 := ne_zero_of_piv_eq_one (h₂.1.1 rj hrj)
    have hmem : rj.1 ∈ spanL (rowList D₁) :=
      hspan ▸ subset_spanL (List.mem_map_of_mem hrj)
    obtain ⟨ri, hri, hri2⟩ := exists_piv_eq_leadIdx_of_mem_spanL h₁ hmem hne
    exact ⟨ri, hri, by rw [hri2, leadIdx_eq_piv_of_isEchelon h₂ hrj (hne := hne)]⟩
  have hPivSet : (D₁.map (·.2)).toFinset = (D₂.map (·.2)).toFinset := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro p hp
      rw [List.mem_toFinset, List.mem_map] at hp
      obtain ⟨ri, hri, rfl⟩ := hp
      obtain ⟨rj, hrj, hrj2⟩ := hPiv12 ri hri
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨rj, hrj, hrj2⟩)
    · intro p hp
      rw [List.mem_toFinset, List.mem_map] at hp
      obtain ⟨rj, hrj, rfl⟩ := hp
      obtain ⟨ri, hri, hri2⟩ := hPiv21 rj hrj
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨ri, hri, hri2⟩)
  have hRow : ∀ x ∈ D₁, ∃ rj ∈ D₂, x = rj := by
    intro x hx
    obtain ⟨rj, hrj, hrj2⟩ := hPiv12 x hx
    have hxmem : x.1 ∈ spanL (rowList D₂) := hspan ▸ subset_spanL (List.mem_map_of_mem hx)
    have hrow : x.1 = rj.1 := by
      rw [← readOff_eq_of_mem_spanL h₂.1 hxmem]
      simp only [readOff]
      refine (Finset.sum_eq_single (s := D₂.toFinset)
        (f := fun rk : PivRow n => (x.1 rk.2) • rk.1) rj ?_ ?_).trans ?_
      · intro rk hrk hne
        have hrkD : rk ∈ D₂ := List.mem_toFinset.mp hrk
        have hmemP : rk.2 ∈ (D₁.map (·.2)).toFinset := by
          rw [hPivSet]
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨rk, hrkD, rfl⟩)
        rw [List.mem_toFinset, List.mem_map] at hmemP
        obtain ⟨ri, hri, hri2⟩ := hmemP
        have hne' : ri ≠ x := by
          intro heq
          have hpiv : rk.2 = rj.2 := by rw [← hri2, heq, ← hrj2]
          exact hne (h₂.1.pivot_inj rk hrkD rj hrj hpiv)
        rw [← hri2, h₁.1.2 x hx ri hri hne'.symm, zero_smul]
      · intro hnot
        exact absurd (List.mem_toFinset.mpr hrj) hnot
      · rw [hrj2, h₁.1.1 x hx, one_smul]
    exact ⟨rj, hrj, Prod.ext hrow hrj2.symm⟩
  intro x
  constructor
  · intro hx
    obtain ⟨rj, hrj, rfl⟩ := hRow x hx
    exact hrj
  · intro hx
    obtain ⟨ri, hri, hri2⟩ := hPiv21 x hx
    have hxmem : x.1 ∈ spanL (rowList D₁) := hspan ▸ subset_spanL (List.mem_map_of_mem hx)
    have hrow : x.1 = ri.1 := by
      rw [← readOff_eq_of_mem_spanL h₁.1 hxmem]
      simp only [readOff]
      refine (Finset.sum_eq_single (s := D₁.toFinset)
        (f := fun rk : PivRow n => (x.1 rk.2) • rk.1) ri ?_ ?_).trans ?_
      · intro rk hrk hne
        have hrkD : rk ∈ D₁ := List.mem_toFinset.mp hrk
        have hmemP : rk.2 ∈ (D₂.map (·.2)).toFinset := by
          rw [← hPivSet]
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨rk, hrkD, rfl⟩)
        rw [List.mem_toFinset, List.mem_map] at hmemP
        obtain ⟨rj, hrj, hrj2⟩ := hmemP
        have hne' : rj ≠ x := by
          intro heq
          have hpiv : rk.2 = ri.2 := by rw [← hrj2, heq, ← hri2]
          exact hne (h₁.1.pivot_inj rk hrkD ri hri hpiv)
        rw [← hrj2, h₂.1.2 x hx rj hrj hne'.symm, zero_smul]
      · intro hnot
        exact absurd (List.mem_toFinset.mpr hri) hnot
      · rw [hri2, h₂.1.1 x hx, one_smul]
    have hxeq : x = ri := Prod.ext hrow hri2.symm
    rw [hxeq]
    exact hri

/-! ## Canonical invariance of the elimination output -/

/-- **The elimination output is an echelon mutually reduced row list**: its pivot columns are
    exactly
the `leadIdx` values at insertion time. -/
theorem isEchelon_rowReduce (L : List (Vec n)) : IsEchelon (rowReduce L) := by
  have key : ∀ (D : List (PivRow n)) (rest : List (Vec n)), IsEchelon D →
      IsEchelon (rowReduceFrom D rest) := by
    intro D rest
    induction rest generalizing D with
    | nil => intro h; exact h
    | cons v rest ih =>
        intro h
        rw [rowReduceFrom_cons]
        refine ih (D := step D v) ?_
        unfold step
        split
        · exact h
        · rename_i hw
          constructor
          · have hred := isReduced_insertPivot (D := D) (w := reduceAgainst D v)
              (p := leadIdx (reduceAgainst D v) hw) h.1
              (leadIdx_eq_one (reduceAgainst D v) hw) (reduceAgainst_apply_piv h.1 v)
            simpa [insertPivot] using hred
          · intro ri hri i hi
            rw [insertPivot] at hri
            rcases List.mem_append.mp hri with hmap | hsingle
            · obtain ⟨rk, hrk, rfl⟩ := List.mem_map.mp hmap
              change (rk.1 + (rk.1 (leadIdx (reduceAgainst D v) hw))
                • reduceAgainst D v) i = 0
              rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              rcases lt_trichotomy (leadIdx (reduceAgainst D v) hw) rk.2 with hlt | heq | hgt
              · rw [h.2 rk hrk _ hlt, zero_mul, add_zero, h.2 rk hrk i hi]
              · rw [heq, h.1.1 rk hrk, one_mul]
                have hi' : i < leadIdx (reduceAgainst D v) hw := by rw [heq]; exact hi
                rw [eq_zero_of_lt_leadIdx hw hi', h.2 rk hrk i hi, add_zero]
              · rw [eq_zero_of_lt_leadIdx hw (lt_of_lt_of_le hi hgt.le), mul_zero, add_zero,
                  h.2 rk hrk i hi]
            · have hrw : ri = (reduceAgainst D v, leadIdx (reduceAgainst D v) hw) := by
                simpa using hsingle
              rw [hrw] at hi ⊢
              exact eq_zero_of_lt_leadIdx hw hi
  exact key [] L ⟨isReduced_nil, by simp⟩

/-- **Canonical invariance (main theorem)**: two row lists with the same row space have the same set
of rows after elimination.

This is the **decidable criterion**, inside the kernel, for whether two codes are the same: compare
the row sets of their elimination outputs. -/
theorem rowReduce_mem_iff_of_spanL_eq {L₁ L₂ : List (Vec n)} (h : spanL L₁ = spanL L₂)
    (x : PivRow n) : x ∈ rowReduce L₁ ↔ x ∈ rowReduce L₂ :=
  pivRow_mem_iff_of_spanL_eq (isEchelon_rowReduce L₁) (isEchelon_rowReduce L₂)
    (by rw [spanL_rowReduce, spanL_rowReduce, h]) x

end QECCertificates
