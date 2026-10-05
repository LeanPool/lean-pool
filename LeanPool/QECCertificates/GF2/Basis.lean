/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module
public import LeanPool.QECCertificates.GF2.Basic

/-!
# Basis-vector sums: the two reduction lemmas

Check matrices are assembled from literals in two ways. Sometimes a row is written as a
`Matrix` and read entry by entry; sometimes, when every row touches a fixed number of block
columns, it is written as the GF(2) **sum of basis vectors** `e a` over its support, and
the whole file's comparisons collapse to a handful of terms. This module holds the five
lemmas the second style rests on. They are generic in `n` and mention no code.

## Main results

* `e_dotProduct`: a basis vector pairs with `v` to the component of `v` at that position.
* `dotProduct_e_sum`: pairing a sum of basis vectors with `v` reads the components of `v`
  on that support — a check-row comparison costs `|A|` terms, not `n`.
* `sum_e_apply`: evaluating a basis-vector sum on a **duplicate-free** support is `1`
  exactly on the support.
* `dot_map_e`: pairing two basis-vector sums gives the parity of the intersection of the
  two supports.
* `dotProduct_e`: the commuted form of `e_dotProduct`, with the basis vector on the right of
  the pairing.

## Where the duplicate-free hypothesis comes from

The three lemmas that mention `Nodup` are stated that way on purpose: without it a repeated
basis vector cancels, and the coordinate formula `if a ∈ l then 1 else 0` would be wrong.
Every call site here builds supports from a `List` that is proved duplicate-free once
(`..._nodup`), so the hypothesis is discharged at the point where the code's data enters,
not at each use. -/

@[expose] public section

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-- A basis vector pairs with `v` to the component of `v` at that position. -/
lemma e_dotProduct (a : Fin n) (v : Vec n) : e a ⬝ᵥ v = v a := by
  rw [dotProduct, Finset.sum_eq_single a]
  · simp [e]
  · intro b _ hb; simp [e, hb]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- **Dot-product reduction**: pairing a sum of basis vectors with `v` reads the components
of `v` on that support, so a check-row comparison costs `|A|` terms, not `n`. -/
lemma dotProduct_e_sum (A : List (Fin n)) (v : Vec n) :
    ((A.map e).sum) ⬝ᵥ v = (A.map v).sum := by
  induction A with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, add_dotProduct,
        e_dotProduct, ih]

/-- **Evaluating a basis-vector sum on a duplicate-free support**: a coordinate is `1`
exactly when it lies on the support. -/
lemma sum_e_apply (l : List (Fin n)) (h : l.Nodup) (a : Fin n) :
    ((l.map e).sum : Vec n) a = if a ∈ l then 1 else 0 := by
  induction l with
  | nil => simp
  | cons b t ih =>
      obtain ⟨hb, ht⟩ := List.nodup_cons.mp h
      rw [List.map_cons, List.sum_cons, Pi.add_apply, ih ht]
      by_cases hab : a = b
      · subst hab; simp [hb, e, List.mem_cons]
      · have hzero : (e b) a = 0 := by simp [e, hab]
        rw [hzero, zero_add]
        simp [List.mem_cons, hab]

/-- **Pairing two basis-vector sums**: the value is the parity of the intersection of the
two supports. This is the lemma that keeps a check-row comparison at `|A|` terms. -/
lemma dot_map_e (A B : List (Fin n)) (hB : B.Nodup) :
    ((A.map e).sum) ⬝ᵥ ((B.map e).sum) = ((A.filter (fun a => a ∈ B)).length : ZMod 2) := by
  rw [dotProduct_e_sum]
  induction A with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.sum_cons, List.filter_cons, ih, sum_e_apply B hB a]
      by_cases ha : a ∈ B
      · simp [ha]
        ring
      · simp [ha]

/-- The commuted form: a basis vector on the **right** of a pairing. Two call sites want this
shape rather than the one above, and stating it once keeps them from rediscovering it. -/
lemma dotProduct_e (v : Vec n) (a : Fin n) : v ⬝ᵥ e a = v a := by
  rw [dotProduct_comm]; exact e_dotProduct a v

end QECCertificates
