/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module

public import LeanPool.QECCertificates.GF2.RowReduce
public import LeanPool.QECCertificates.RowspaceKernel

/-!
# Computable membership tests: exact distances by kernel reduction

The abstract `Submodule.span` predicate does not by itself provide a computable
membership test. This module supplies a verified decision procedure for finite binary
row spaces and kernels. The abstract minimum-weight definition is noncomputable;
these tests support certificates that can instead be reduced in the kernel. It turns membership
in a row space and membership in a kernel into **Boolean computations that the kernel can
reduce**, and proves that they agree exactly with the subspace semantics.

A lower bound of the form "no logical operator of smaller weight exists" can then be
written as a **closed Boolean equality** whose truth value the kernel obtains by reduction
(`by decide`): no SAT solver, no `native_decide`, no custom axioms. This is the step that
removes the external solver from the trusted base.

## The two tests

* **Row space**: `inSpanB L v := reduceAgainst (rowReduce L) v = 0`. Row reduction sends
  `L` to a mutually reduced set of pivot rows, and those pivots then eliminate `v` column
  by column: `v` lies in the row space exactly when nothing but zero remains. The two
  directions are supplied by `add_reduceAgainst_mem` (where the reduced vector lands) and
  by `reduceAgainst_self_mem` (the reduction vanishes on the generators, and linearity
  extends this to the whole row space).
* **Kernel**: `inKerB M x := ∀ i, (M i) ⬝ᵥ x = 0`, orthogonality row by row, a finite
  conjunction. It is aligned exactly with LeanQEC's
  `mem_ker_iff_dotProd_rows_eq_zero`.

## Main results

* `inSpanB_iff` / `inKerB_iff`: the **semantic equivalence theorems** for the two tests
  (soundness and completeness).
* `reduceAgainst_add` / `reduceAgainst_smul`: the reduction operator is **linear**.
* `reduceAgainst_eq_zero_of_mem_spanL`: the reduction vanishes exactly on the row space.
-/

@[expose] public section

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-! ## Linearity of the reduction operator -/

/-- The reduction maps zero to zero. -/
lemma reduceAgainst_zero (D : List (PivRow n)) : reduceAgainst D (0 : Vec n) = 0 := by
  induction D with
  | nil => rfl
  | cons r D ih =>
      rw [reduceAgainst_cons]
      simpa using ih

/-- The reduction is additive. -/
lemma reduceAgainst_add (D : List (PivRow n)) :
    ∀ u v : Vec n, reduceAgainst D (u + v) = reduceAgainst D u + reduceAgainst D v := by
  induction D with
  | nil => intro u v; rfl
  | cons r D ih =>
      intro u v
      rw [reduceAgainst_cons, reduceAgainst_cons, reduceAgainst_cons]
      have harg : u + v + ((u + v) r.2) • r.1
          = (u + (u r.2) • r.1) + (v + (v r.2) • r.1) := by
        rw [Pi.add_apply, add_smul]
        ac_rfl
      rw [harg]
      exact ih _ _

/-- The reduction is homogeneous over scalars. -/
lemma reduceAgainst_smul (D : List (PivRow n)) :
    ∀ (c : ZMod 2) (v : Vec n), reduceAgainst D (c • v) = c • reduceAgainst D v := by
  induction D with
  | nil => intro c v; rfl
  | cons r D ih =>
      intro c v
      rw [reduceAgainst_cons, reduceAgainst_cons]
      have harg : c • v + ((c • v) r.2) • r.1 = c • (v + (v r.2) • r.1) := by
        rw [Pi.smul_apply, smul_eq_mul, ← smul_smul, smul_add]
      rw [harg]
      exact ih _ _

/-- The reduction operator as a linear map. -/
def reduceAgainstLin (D : List (PivRow n)) : Vec n →ₗ[ZMod 2] Vec n where
  toFun := reduceAgainst D
  map_add' := reduceAgainst_add D
  map_smul' := reduceAgainst_smul D

/-- **The reduction vanishes on the generators**: for a mutually reduced set of pivot
rows, eliminating a row by the set itself sends that row to zero.

This is the precise form of idempotence for row reduction: when the process reaches a
row's own pivot column the row is annihilated outright, and no later row can disturb that
column again, because (R2) keeps every other row zero there. -/
lemma reduceAgainst_self_mem {D : List (PivRow n)} (hD : IsReduced D) {ri : PivRow n}
    (hri : ri ∈ D) : reduceAgainst D ri.1 = 0 := by
  induction D with
  | nil => exact absurd hri (by simp)
  | cons r D ih =>
      rw [reduceAgainst_cons]
      rcases List.mem_cons.mp hri with h_eq | h_mem
      · rw [h_eq, hD.1 r (List.mem_cons_self ..), one_smul, add_self]
        exact reduceAgainst_zero D
      · by_cases hr : ri = r
        · rw [hr, hD.1 r (List.mem_cons_self ..), one_smul, add_self]
          exact reduceAgainst_zero D
        · have hD' : IsReduced D :=
            ⟨fun rj hrj => hD.1 rj (List.mem_cons_of_mem r hrj),
             fun rj hrj rk hrk hne =>
               hD.2 rj (List.mem_cons_of_mem r hrj) rk (List.mem_cons_of_mem r hrk) hne⟩
          rw [hD.2 ri (List.mem_cons_of_mem r h_mem) r (List.mem_cons_self ..) hr, zero_smul,
            add_zero]
          exact ih hD' h_mem

/-- **The reduction vanishes exactly on the row space**: when `D` is mutually reduced,
`reduceAgainst D` annihilates `spanL (rowList D)`.

The proof is the standard argument that linearity plus vanishing on the generators gives
vanishing on the whole span: `spanL (rowList D)` is spanned by `rowList D`, on which
`reduceAgainst D` vanishes, so `spanL (rowList D)` is contained in
`comap (reduceAgainstLin D) ⊥`. -/
lemma reduceAgainst_eq_zero_of_mem_spanL {D : List (PivRow n)} (hD : IsReduced D) {v : Vec n}
    (hv : v ∈ spanL (rowList D)) : reduceAgainst D v = 0 := by
  have hle : spanL (rowList D) ≤ Submodule.comap (reduceAgainstLin D) ⊥ := by
    rw [spanL, Submodule.span_le]
    intro x hx
    have hx' : x ∈ rowList D := hx
    obtain ⟨ri, hri, hri_eq⟩ := List.mem_map.mp hx'
    rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.mem_bot, ← hri_eq]
    exact reduceAgainst_self_mem hD hri
  have hv' : (reduceAgainstLin D) v ∈ (⊥ : Submodule (ZMod 2) (Vec n)) := hle hv
  rw [Submodule.mem_bot] at hv'
  exact hv'

/-! ## The row-space membership test -/

/-- **Computable row-space membership test**: reduce `L` to a mutually reduced set of
pivot rows, then eliminate `v` with those pivots.

Elimination leaves zero exactly when `v` lies in the row space of `L` (`inSpanB_iff`). The
whole test is a fold over a `List`, so the **kernel can reduce it directly**, which turns
the statement that a given vector is not a stabilizer into a closed proposition that a
single `by decide` settles. -/
def inSpanB (L : List (Vec n)) (v : Vec n) : Bool :=
  decide (reduceAgainst (rowReduce L) v = 0)

/-- **Soundness**: if `inSpanB` reports true then `v` really lies in the row space.

Immediate from `add_reduceAgainst_mem` (`v` plus the reduced vector lies in the row space)
once the reduced vector is zero. -/
theorem inSpanB_sound {L : List (Vec n)} {v : Vec n} (h : inSpanB L v = true) :
    v ∈ spanL L := by
  unfold inSpanB at h
  rw [decide_eq_true_eq] at h
  have hmem : v + reduceAgainst (rowReduce L) v ∈ spanL (rowList (rowReduce L)) :=
    add_reduceAgainst_mem (rowReduce L) v
  rw [h, add_zero] at hmem
  rwa [spanL_rowReduce] at hmem

/-- **Completeness**: if `v` lies in the row space then `inSpanB` reports true.

Immediate from `reduceAgainst_eq_zero_of_mem_spanL`, together with invariance of the row
space. -/
theorem inSpanB_complete {L : List (Vec n)} {v : Vec n} (hv : v ∈ spanL L) :
    inSpanB L v = true := by
  unfold inSpanB
  rw [decide_eq_true_eq]
  exact reduceAgainst_eq_zero_of_mem_spanL (isReduced_rowReduce L) (by rwa [spanL_rowReduce])

/-- **Semantic equivalence of the membership test**: the computable test and subspace
membership agree exactly.

This is the **single entry point** for handing distance and rank questions to the kernel:
any Boolean conclusion obtained by `decide` can be translated back into the language of
`Submodule` through this theorem, and so be connected to the existing theorems of
LeanQEC. -/
theorem inSpanB_iff (L : List (Vec n)) (v : Vec n) : inSpanB L v = true ↔ v ∈ spanL L :=
  ⟨inSpanB_sound, inSpanB_complete⟩

/-- **Semantic equivalence, negative form** (consumed on the lower-bound side): reports
false exactly when the vector is not in the row space. -/
theorem inSpanB_eq_false_iff (L : List (Vec n)) (v : Vec n) :
    inSpanB L v = false ↔ v ∉ spanL L := by
  constructor
  · intro h hv
    rw [(inSpanB_iff L v).mpr hv] at h
    exact absurd h (by decide)
  · intro h
    cases hb : inSpanB L v with
    | false => rfl
    | true => exact absurd ((inSpanB_iff L v).mp hb) h

/-! ## The kernel membership test -/

/-- **Computable kernel membership test**: orthogonality with every row of the
parity-check matrix, which over GF(2) is commutation.

The shape matches LeanQEC's `mem_ker_iff_dotProd_rows_eq_zero`: expanding kernel
membership `x ∈ LinearMap.ker M.toLin'` gives exactly this row-by-row conjunction. -/
def inKerB {k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Vec n) : Bool :=
  (List.ofFn fun i : Fin k => decide ((M i) ⬝ᵥ x = 0)).all id

/-- **Semantic equivalence of the kernel test**: `inKerB` reports true exactly when `x`
lies in the kernel as LeanQEC defines it.

The bridging lemma is LeanQEC's own `mem_ker_iff_dotProd_rows_eq_zero`, so the computable
test and the upstream semantics are connected with **no intermediate layer** and no
additional trusted assumption. -/
theorem inKerB_iff {k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Vec n) :
    inKerB M x = true ↔ x ∈ LinearMap.ker M.toLin' := by
  rw [mem_ker_iff_dotProd_rows_eq_zero]
  unfold inKerB
  rw [List.all_eq_true]
  constructor
  · intro h i
    have hmem : decide ((M i) ⬝ᵥ x = 0) ∈
        List.ofFn (fun i : Fin k => decide ((M i) ⬝ᵥ x = 0)) := by
      rw [List.mem_ofFn]; exact ⟨i, rfl⟩
    simpa using h _ hmem
  · intro h b hb
    rw [List.mem_ofFn] at hb
    obtain ⟨i, hi⟩ := hb
    rw [← hi]
    simpa using h i

end QECCertificates
