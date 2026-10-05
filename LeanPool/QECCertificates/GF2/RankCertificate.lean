/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module
public import LeanPool.QECCertificates.GF2.KernelBasis

/-!
# Rank certificates: `finrank (certificateRowSpace H) = #(rows in the row-reduction output)`

The rate/rank accounting had one gap: the row-reduction preprocessing was not formalized.
A trusted row reduction is available, and this module plugs it in as a **rank certificate**:
reduce the parity-check matrix and **count the rows** to obtain its rank, a step that is
checkable inside the kernel.

## Mechanism

The output of `rowReduce` is a set of mutually reduced pivot rows (`IsReduced`). Turning it
into a rank needs two things:

1. **The pivot rows are linearly independent**: evaluating at the pivot column of each row,
   (R1) gives 1 and (R2) gives 0, so a linear combination `∑ cᵢ rᵢ` takes the value `cⱼ` at
   the pivot column of `rⱼ`; hence `∑ cᵢ rᵢ = 0 → cⱼ = 0`.
2. **The rows are pairwise distinct** (otherwise the `Fin D.length` indexing is not
   injective and item 1 fails). This module proves that the output of `rowReduce` satisfies
   the stronger `NodupPiv` (**the pivot columns are pairwise distinct**): at the pivot
   column of a newly inserted row every existing row is 0 while the new row is 1, so the
   new row cannot coincide with any existing row.

Together the two give `finrank (spanL (rowList (rowReduce L))) = (rowReduce L).length`, and
`spanL_rowReduce` then transfers the statement to the original list of rows.

## Main results

* `NodupPiv`: the structural invariant that the pivot columns are pairwise distinct (kept
  throughout `rowReduce`).
* `linearIndependent_rowList_of_isReduced`: a mutually reduced list of rows is linearly
  independent.
* `finrank_spanL_eq_length_rowReduce`: **the rank equals the number of rows of the
  reduction output**.
* `Matrix.rank_eq_length_rowReduce`: the interface to `Matrix.rank` of Mathlib.
-/

@[expose] public section

namespace QECCertificates

open scoped BigOperators

open _root_.Matrix

variable {n : ℕ}

/-! ## The invariant that the pivot columns are pairwise distinct -/

/-- The pivot columns of `D` are pairwise distinct. This is a structural invariant of the
output of `rowReduce`, and the premise for "the number of rows equals the rank" (otherwise
the `Fin D.length` indexing is not injective). -/
def NodupPiv (D : List (PivRow n)) : Prop := (D.map (·.2)).Nodup

lemma nodupPiv_nil : NodupPiv ([] : List (PivRow n)) := by simp [NodupPiv]

/-- Inserting one row only appends `p` to the list of pivot columns. -/
lemma map_piv_insertPivot (D : List (PivRow n)) (w : Vec n) (p : Fin n) :
    (insertPivot D w p).map (·.2) = (D.map (·.2)) ++ [p] := by
  simp [insertPivot, List.map_map, Function.comp_def]

lemma nodupPiv_insertPivot {D : List (PivRow n)} (hD : NodupPiv D) {w : Vec n} {p : Fin n}
    (hp : p ∉ D.map (·.2)) : NodupPiv (insertPivot D w p) := by
  rw [NodupPiv, map_piv_insertPivot, List.nodup_append]
  refine ⟨hD, List.nodup_singleton p, ?_⟩
  intro a ha b hb
  rw [List.mem_singleton] at hb
  subst hb
  exact fun h => hp (h ▸ ha)

lemma nodupPiv_step {D : List (PivRow n)} (hred : IsReduced D) (hD : NodupPiv D) (v : Vec n) :
    NodupPiv (step D v) := by
  unfold step
  split
  · exact hD
  · rename_i hw
    refine nodupPiv_insertPivot hD ?_
    intro hmem
    obtain ⟨ri, hri, hri2⟩ := List.mem_map.mp hmem
    have h1 : reduceAgainst D v ri.2 = 0 := reduceAgainst_apply_piv hred v ri hri
    rw [hri2, leadIdx_eq_one (reduceAgainst D v) hw] at h1
    exact one_ne_zero h1

lemma nodupPiv_rowReduceFrom (D : List (PivRow n)) (rest : List (Vec n)) :
    IsReduced D → NodupPiv D → NodupPiv (rowReduceFrom D rest) := by
  induction rest generalizing D with
  | nil => intro _ hD; exact hD
  | cons v rest ih =>
      intro hred hD
      rw [rowReduceFrom_cons]
      exact ih (step D v) (isReduced_step hred v) (nodupPiv_step hred hD v)

/-- The pivot columns of the output of `rowReduce` are pairwise distinct. -/
theorem nodupPiv_rowReduce (L : List (Vec n)) : NodupPiv (rowReduce L) :=
  nodupPiv_rowReduceFrom [] L isReduced_nil nodupPiv_nil

/-- The tail of a mutually reduced list is again mutually reduced. -/
lemma IsReduced.tail {r : PivRow n} {D : List (PivRow n)} (h : IsReduced (r :: D)) :
    IsReduced D :=
  ⟨fun ri hri => h.1 ri (List.mem_cons_of_mem r hri),
   fun ri hri rj hrj hne =>
      h.2 ri (List.mem_cons_of_mem r hri) rj (List.mem_cons_of_mem r hrj) hne⟩

/-- Pairwise distinct pivot columns imply pairwise distinct rows. -/
lemma nodup_of_nodupPiv (D : List (PivRow n)) :
    IsReduced D → NodupPiv D → D.Nodup := by
  induction D with
  | nil => intro _ _; simp
  | cons r D ih =>
      intro hred h
      rw [List.nodup_cons]
      have hmap : (D.map (·.2)).Nodup := by
        have hh : ((r :: D).map (·.2)).Nodup := h
        rw [List.map_cons, List.nodup_cons] at hh
        exact hh.2
      refine ⟨?_, ih hred.tail hmap⟩
      intro hmem
      have hh : ((r :: D).map (·.2)).Nodup := h
      rw [List.map_cons, List.nodup_cons] at hh
      exact hh.1 (List.mem_map_of_mem hmem)

/-! ## Linear independence of the pivot rows -/

/-- **A mutually reduced list of rows is linearly independent**: evaluating at the pivot
column of each row separates the coefficients. -/
theorem linearIndependent_rowList_of_isReduced {D : List (PivRow n)} (hD : IsReduced D)
    (hnd : NodupPiv D) :
    LinearIndependent (ZMod 2) (fun i : Fin D.length => (D.get i).1) := by
  have hnod : D.Nodup := nodup_of_nodupPiv D hD hnd
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have h := congrFun hsum ((D.get i).2)
  rw [Finset.sum_apply] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  have hcongr : ∑ j ∈ s, g j * ((D.get j).1 ((D.get i).2))
      = ∑ j ∈ s, g j * (if j = i then (1 : ZMod 2) else 0) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hji : j = i
    · rw [hji, ite_eq_left rfl, mul_one, hD.1 (D.get i) (List.get_mem D i), mul_one]
    · have hne : D.get j ≠ D.get i := fun hEq => hji (hnod.get_inj_iff.mp hEq)
      rw [ite_eq_right hji, mul_zero,
        hD.2 (D.get j) (List.get_mem D j) (D.get i) (List.get_mem D i) hne, mul_zero]
  rw [hcongr] at h
  have hcollapse : ∑ j ∈ s, g j * (if j = i then (1 : ZMod 2) else 0) = g i := by
    have hh := Finset.sum_eq_single (s := s)
      (f := fun j => g j * (if j = i then (1 : ZMod 2) else 0)) i
      (fun b _ hne => by rw [ite_eq_right (fun hc => hne hc), mul_zero])
      (fun hnot => absurd hi hnot)
    rwa [ite_eq_left rfl, mul_one] at hh
  rw [hcollapse] at h
  exact h

/-- The range of `D.get` is exactly the list of rows of `D`. -/
lemma range_get_eq_rowList (D : List (PivRow n)) :
    Set.range (fun i : Fin D.length => (D.get i).1) = {x | x ∈ rowList D} := by
  ext x
  rw [Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact List.mem_map_of_mem (List.get_mem D i)
  · intro hx
    have hx' : x ∈ rowList D := hx
    rw [rowList, List.mem_map] at hx'
    obtain ⟨ri, hri, rfl⟩ := hx'
    rw [List.mem_iff_get] at hri
    obtain ⟨i, rfl⟩ := hri
    exact ⟨i, rfl⟩

/-- Pairwise distinct pivot columns imply that the number of pivot columns equals the
number of rows. -/
lemma card_pivCols_eq_length {D : List (PivRow n)} (h : NodupPiv D) :
    (pivCols D).card = D.length := by
  rw [pivCols, List.toFinset_card_of_nodup h, List.length_map]

/-! ## Main theorems -/

/-- **The rank equals the number of rows of the reduction output** (stated for an already
reduced state). -/
theorem finrank_spanL_eq_length_of_isReduced {D : List (PivRow n)} (hD : IsReduced D)
    (hnd : NodupPiv D) :
    Module.finrank (ZMod 2) (spanL (rowList D)) = D.length := by
  have hcard := finrank_span_eq_card (linearIndependent_rowList_of_isReduced hD hnd)
  rw [range_get_eq_rowList] at hcard
  have hcard' : Module.finrank (ZMod 2) (spanL (rowList D)) = Fintype.card (Fin D.length) :=
    hcard
  simpa [Fintype.card_fin] using hcard'

/-- **Rank certificate (main theorem)**: the dimension of the space spanned by the list of
rows equals the number of rows of the row-reduction output.

The list of pivot rows produced by the reduction is itself the certificate: the kernel only
has to count the rows and check `IsReduced` to verify the rank independently, with no need
to trust any external script. -/
theorem finrank_spanL_eq_length_rowReduce (L : List (Vec n)) :
    Module.finrank (ZMod 2) (spanL L) = (rowReduce L).length := by
  rw [← spanL_rowReduce L]
  exact finrank_spanL_eq_length_of_isReduced (isReduced_rowReduce L) (nodupPiv_rowReduce L)

/-- The rank is at most the length of the encoding. -/
theorem length_rowReduce_le (L : List (Vec n)) : (rowReduce L).length ≤ n := by
  rw [← card_pivCols_eq_length (nodupPiv_rowReduce L)]
  calc (pivCols (rowReduce L)).card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
    _ = n := Fintype.card_fin n

/-- `Matrix.rank` of Mathlib is the dimension of the row space. -/
theorem Matrix.rank_eq_finrank_rowSpace {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    M.rank = Module.finrank (ZMod 2) M.certificateRowSpace := by
  rw [Matrix.rank_eq_finrank_span_row]
  rfl

/-- **Rank certificate in matrix form**: reduce the rows of the parity-check matrix and
count them to obtain its rank.

`Matrix.rank` is the entry point through which the LeanQEC side of the distance reduction
reads a rank; this theorem lets the row reduction verified in this package take over that
reading directly. -/
theorem Matrix.rank_eq_length_rowReduce {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    M.rank = (rowReduce (List.ofFn fun i => M i)).length := by
  rw [Matrix.rank_eq_finrank_rowSpace, Matrix.rowSpace_eq_spanL_ofFn]
  exact finrank_spanL_eq_length_rowReduce _

/-! ## A nonzero kernel vector when the rank is not full (the bridge on the threshold side) -/

/-- **Full rank fails $\Longrightarrow$ a nonzero kernel vector**: when
$M.\mathrm{rank}<n$ we have $\ker M\ne0$.

The construction is explicit: after row reduction there are fewer than $n$ pivot columns,
hence a **free column** $j$, and `kerVec` takes the value 1 on that column
(`exists_light_mem_kerL`); it is orthogonal to every row of $M$, so multiplying by $M$ on
the left gives zero.

**This is the bridge on the threshold side**: every factor of
$k=k_1k_2+k_1^\top k_2^\top$ is a $\dim\ker$, whereas what "the kernel is nontrivial"
requires is the **existence of a nonzero kernel vector**, not a dimension. The companion
paper argued this conversion only arithmetically; this theorem puts it into the kernel. -/
theorem exists_ne_zero_mulVec_eq_zero_of_rank_lt {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (h : M.rank < n) : ∃ v : Vec n, M *ᵥ v = 0 ∧ v ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin n, IsFreeCol (rowReduce (List.ofFn fun i => M i)) j := by
    by_contra hcon
    have hall : pivCols (rowReduce (List.ofFn fun i => M i)) = Finset.univ := by
      refine Finset.eq_univ_of_forall fun j => ?_
      by_contra hj
      exact hcon ⟨j, fun ri hri heq => hj (mem_pivCols.mpr ⟨ri, hri, heq⟩)⟩
    have hcard := card_pivCols_eq_length (nodupPiv_rowReduce (List.ofFn fun i => M i))
    rw [hall, Finset.card_univ, Fintype.card_fin] at hcard
    rw [Matrix.rank_eq_length_rowReduce] at h
    omega
  obtain ⟨v, hv, hvne, -⟩ := exists_light_mem_kerL (List.ofFn fun i => M i) hj
  refine ⟨v, ?_, hvne⟩
  have hrow : ∀ i : Fin m, (fun j => M i j) ∈ List.ofFn (fun i => M i) := by
    intro i
    rw [List.mem_ofFn]
    exact ⟨i, rfl⟩
  funext i
  have hdot : (fun j => M i j) ⬝ᵥ v = 0 := (mem_kerL.mp hv) _ (hrow i)
  simpa [Matrix.mulVec] using hdot

end QECCertificates
