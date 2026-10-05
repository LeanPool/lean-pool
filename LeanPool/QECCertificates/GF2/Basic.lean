/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module
public import LeanPool.QECCertificates.RowspaceKernel

/-!
# GF(2) vector algebra primitives (coding-theory layer)

This module is the linear-algebra basis of the coding-theory layer: it collects the
parity-check matrices, stabilizers and logical operators of a quantum error-correcting
code into the GF(2) vector space `Vec n = Fin n → ZMod 2`, and supplies the primitives
that row reduction and kernel-basis extraction are built from.

**Alignment with LeanQEC**: the row-space object is LeanQEC's `Matrix.certificateRowSpace`, reused
directly (it is defined as `Submodule.span (Set.range M)`); this module's `spanL` is the
equivalent formulation on the row-list side, and the bridge lemma
`Matrix.rowSpace_eq_spanL_ofFn` connects the two. The row-space theorems already
available in LeanQEC therefore apply directly to the row lists of this package.

## Main definitions

* `Vec n`: a GF(2) vector of length `n` (a bit string).
* `spanL L`: the subspace spanned by a list of rows, that is, the row space.
* `addSmul v r c`: adds `c • r` to `v`. Over GF(2), taking `c = v i` and `r i = 1`
  clears the `i`-th coordinate.

## Main results

* `addSmul_apply`: the componentwise formula `(v + c • r) i = v i + c * r i`.
* `addSmul_cancel`: in characteristic 2, `(v + c • r) + c • r = v`; row operations are
  invertible.
* `spanL_map_addSmul_append`: applying that operation to a whole list of rows and then
  appending the new row leaves the row space unchanged.
* `Matrix.rowSpace_eq_spanL_ofFn`: the bridge to the LeanQEC row-space representation.
-/

@[expose] public section

namespace QECCertificates

open scoped BigOperators

/-- A GF(2) vector of length `n`. Under the symplectic representation a single Pauli
operator of a quantum error-correcting code is a pair of such vectors. -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}

/-! ## Generic utilities, shared by the modules that assemble matrices from literals

The three definitions `e`, `zeroRows` and `add_eq_zero_iff_eq` live here rather than in
any particular code family: they are **general-purpose tools**, needed by every module
that assembles a parity-check matrix from literals or that uses the characteristic-2
cancellation law, so the instance-level modules do not each carry a copy of their own. -/

/-- The unit vector at the `i`-th coordinate of GF(2) (a basis of `Vec n`). -/
def e {n : ℕ} (i : Fin n) : Vec n := fun j => if j = i then 1 else 0

/-- The zero-row matrix: a classical code takes it as the row-space argument of
`minWeightKernelOutsideRowSpace` (giving `certificateRowSpace = ⊥`), so that set reduces to the
nonzero vectors in the kernel. -/
def zeroRows (n : ℕ) : Matrix (Fin 0) (Fin n) (ZMod 2) := fun i => i.elim0

/-- In characteristic 2, `a + b = 0 ↔ a = b`. -/
lemma add_eq_zero_iff_eq (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    rw [← CharTwo.add_self_eq_zero b] at h
    exact add_right_cancel_iff.mp h
  · intro h
    rw [h, CharTwo.add_self_eq_zero]

/-- The support: the positions of the nonzero components. -/
def support (v : Vec n) : Finset (Fin n) := Finset.univ.filter (fun i => v i ≠ 0)

@[simp] lemma mem_support {v : Vec n} {i : Fin n} : i ∈ support v ↔ v i ≠ 0 := by
  simp [support]

/-- The weight used for the code distance: the size of the support, agreeing with
`hammingNorm` of mathlib and LeanQEC. -/
lemma weight_eq_hammingNorm (v : Vec n) : (support v).card = hammingNorm v := by
  simp [support, hammingNorm]

/-- Characteristic 2: a vector over GF(2) added to itself is zero. -/
@[simp] lemma add_self (v : Vec n) : v + v = 0 := by
  funext i; exact CharTwo.add_self_eq_zero (v i)

/-- Over GF(2), nonzero means 1. -/
lemma eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

/-! ## Row space -/

/-- The subspace spanned by a list of rows, that is, the row space. The generating set is
the set of elements of the list, which can be exchanged for the `Set.range` formulation
(see `spanL_ofFn_eq_span_range`). -/
def spanL (L : List (Vec n)) : Submodule (ZMod 2) (Vec n) :=
  Submodule.span (ZMod 2) {x | x ∈ L}

lemma mem_spanL {L : List (Vec n)} {x : Vec n} :
    x ∈ spanL L ↔ x ∈ Submodule.span (ZMod 2) {y | y ∈ L} := Iff.rfl

lemma subset_spanL {L : List (Vec n)} {x : Vec n} (h : x ∈ L) : x ∈ spanL L :=
  Submodule.subset_span h

lemma spanL_nil : spanL ([] : List (Vec n)) = ⊥ := by
  have h : {x : Vec n | x ∈ ([] : List (Vec n))} = ∅ := by
    ext x; simp
  rw [spanL, h, Submodule.span_empty]

/-- The row space of an appended list is the supremum of the row spaces of the two
parts. -/
lemma spanL_append (A B : List (Vec n)) : spanL (A ++ B) = spanL A ⊔ spanL B := by
  have h : {x : Vec n | x ∈ A ++ B} = {x | x ∈ A} ∪ {x | x ∈ B} := by
    ext x; simp [List.mem_append]
  rw [spanL, h, Submodule.span_union]; rfl

/-- The row space spanned by a single vector. -/
lemma spanL_singleton (v : Vec n) : spanL [v] = Submodule.span (ZMod 2) ({v} : Set (Vec n)) := by
  rw [spanL]
  congr 1
  ext x
  change x ∈ [v] ↔ x ∈ ({v} : Set (Vec n))
  simp

/-- The single-row version: the row space after appending one row is the supremum of the
original row space and that row. -/
lemma spanL_append_singleton (A : List (Vec n)) (v : Vec n) :
    spanL (A ++ [v]) = spanL A ⊔ Submodule.span (ZMod 2) ({v} : Set (Vec n)) := by
  rw [spanL_append, spanL_singleton]

/-- The row space is monotone with respect to inclusion of lists. -/
lemma spanL_mono_of_subset {A B : List (Vec n)} (h : A ⊆ B) : spanL A ≤ spanL B :=
  Submodule.span_mono fun _ hx => h hx

/-- The characteristic-2 cancellation identity `(v + w) + v = w`. -/
lemma add_add_left_cancel (v w : Vec n) : (v + w) + v = w := by
  rw [add_assoc, add_comm w v, ← add_assoc, add_self, zero_add]

/-- The characteristic-2 cancellation identity `v + (v + w) = w`. -/
lemma add_add_same_left (v w : Vec n) : v + (v + w) = w := by
  rw [← add_assoc, add_self, zero_add]

/-- The characteristic-2 cancellation identity `v + (w + v) = w`. -/
lemma add_add_same_right (v w : Vec n) : v + (w + v) = w := by
  rw [add_comm w v, add_add_same_left]

/-- If `v + w` lies in the row space of `A`, then appending `w` and appending `v` span
the same row space. (The row produced by elimination differs from the original one by a
vector that is already in the row space, so the row space is unchanged.) -/
lemma mem_spanL_append_singleton_of_add_mem {A : List (Vec n)} {v w : Vec n}
    (h : v + w ∈ spanL A) : w ∈ spanL (A ++ [v]) := by
  have hv : v ∈ spanL (A ++ [v]) := subset_spanL (by simp)
  have hu : v + w ∈ spanL (A ++ [v]) := spanL_mono_of_subset (by intro x hx; simp [hx]) h
  have key : (v + w) + v = w := add_add_left_cancel v w
  exact key ▸ Submodule.add_mem _ hu hv

/-- Equality of the row spaces, obtained from the previous statement. -/
lemma spanL_append_eq_of_add_mem {A : List (Vec n)} {v w : Vec n}
    (h : v + w ∈ spanL A) : spanL (A ++ [w]) = spanL (A ++ [v]) := by
  have hwv : w ∈ spanL (A ++ [v]) := mem_spanL_append_singleton_of_add_mem h
  have hvw : v ∈ spanL (A ++ [w]) :=
    mem_spanL_append_singleton_of_add_mem (A := A) (v := w) (w := v)
      (by simpa [add_comm] using h)
  refine le_antisymm ?_ ?_
  · rw [spanL_append_singleton]
    refine sup_le (spanL_mono_of_subset (by intro x hx; simp [hx])) ?_
    exact Submodule.span_le.2 fun x hx => by
      have hx' : x = w := by simpa using hx
      rw [hx']; exact hwv
  · rw [spanL_append_singleton]
    refine sup_le (spanL_mono_of_subset (by intro x hx; simp [hx])) ?_
    exact Submodule.span_le.2 fun x hx => by
      have hx' : x = v := by simpa using hx
      rw [hx']; exact hvw

/-- The bridge to the `Set.range` formulation: the row space of `List.ofFn f` is the
space spanned by the range of `f`. -/
lemma spanL_ofFn_eq_span_range {m : ℕ} (f : Fin m → Vec n) :
    spanL (List.ofFn f) = Submodule.span (ZMod 2) (Set.range f) := by
  rw [spanL]
  congr 1
  ext x
  change x ∈ List.ofFn f ↔ x ∈ Set.range f
  rw [List.mem_ofFn, Set.mem_range]

/-- **Bridge to LeanQEC**: `Matrix.certificateRowSpace M` (that is, `Submodule.span (Set.range M)`)
equals the `spanL` of the row list of `M`. The row-space theorems of LeanQEC therefore
apply directly to the row lists of this package. -/
theorem Matrix.rowSpace_eq_spanL_ofFn {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    M.certificateRowSpace = spanL (List.ofFn fun i => M i) := by
  change Submodule.span (ZMod 2) (Set.range fun i => M i) = spanL (List.ofFn fun i => M i)
  rw [spanL]
  congr 1
  ext x
  change x ∈ Set.range (fun i => M i) ↔ x ∈ List.ofFn (fun i => M i)
  rw [List.mem_ofFn, Set.mem_range]

/-! ## Elementary row operations -/

/-- Adds `c • r` to `v`. Over GF(2), taking `c = v i` and `r i = 1` clears exactly the
`i`-th coordinate of `v`. -/
def addSmul (v r : Vec n) (c : ZMod 2) : Vec n := v + c • r

@[simp] lemma addSmul_apply (v r : Vec n) (c : ZMod 2) (i : Fin n) :
    addSmul v r c i = v i + c * r i := by
  simp [addSmul, Pi.add_apply, Pi.smul_apply]

/-- With `c = v i` and `r i = 1`, the operation clears the `i`-th coordinate. -/
lemma addSmul_zero_coord (v r : Vec n) (i : Fin n) (hr : r i = 1) :
    addSmul v r (v i) i = 0 := by
  rw [addSmul_apply, hr, mul_one]
  exact CharTwo.add_self_eq_zero (v i)

/-- In characteristic 2 a row operation is invertible: adding and then adding back leaves
the row unchanged. -/
lemma addSmul_cancel (v r : Vec n) (c : ZMod 2) : addSmul v r c + c • r = v := by
  simp only [addSmul]
  rw [add_assoc, add_self, add_zero]

lemma addSmul_mem_span {S : Set (Vec n)} {v r : Vec n} (c : ZMod 2)
    (hv : v ∈ Submodule.span (ZMod 2) S) (hr : r ∈ Submodule.span (ZMod 2) S) :
    addSmul v r c ∈ Submodule.span (ZMod 2) S :=
  Submodule.add_mem _ hv (Submodule.smul_mem _ c hr)

/-! ## A whole-list row operation preserves the row space -/

/-- **Preservation of the row space (whole-list version)**: replacing every row `r` of a
list `A` by `r + f r • w` and then appending `w` at the end gives the same row space as
appending `w` to `A`.

This is the correctness skeleton of row reduction: elimination performs only the one
operation of adding the new row to an old row with a coefficient, which does not change
the spanned subspace and hence does not change the code. -/
theorem spanL_map_addSmul_append (A : List (Vec n)) (w : Vec n) (f : Vec n → ZMod 2) :
    spanL (A.map (fun r => r + f r • w) ++ [w]) = spanL (A ++ [w]) := by
  have hwL : w ∈ spanL (A.map (fun r => r + f r • w) ++ [w]) := subset_spanL (by simp)
  have hwR : w ∈ spanL (A ++ [w]) := subset_spanL (by simp)
  refine le_antisymm ?_ ?_
  · rw [spanL, Submodule.span_le]
    intro x hx
    have hx' : x ∈ A.map (fun r => r + f r • w) ++ [w] := hx
    rw [List.mem_append, List.mem_map] at hx'
    rcases hx' with ⟨r, hr, rfl⟩ | hx'
    · exact addSmul_mem_span _ (subset_spanL (by simp [hr])) hwR
    · exact subset_spanL (by simp [hx'])
  · rw [spanL, Submodule.span_le]
    intro x hx
    have hx' : x ∈ A ++ [w] := hx
    rw [List.mem_append] at hx'
    rcases hx' with hxA | hx'
    · have h1 : x + f x • w ∈ spanL (A.map (fun r => r + f r • w) ++ [w]) :=
        subset_spanL (by simp [List.mem_map_of_mem hxA])
      have h2 : f x • w ∈ spanL (A.map (fun r => r + f r • w) ++ [w]) :=
        Submodule.smul_mem _ _ hwL
      have hmem := Submodule.add_mem _ h1 h2
      simpa [addSmul, add_assoc] using hmem
    · have hxw : x = w := by simpa using hx'
      rw [hxw]; exact hwL

end QECCertificates
