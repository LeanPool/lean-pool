/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module
public import LeanPool.QECCertificates.GF2.RowReduce

/-!
# Kernel-basis extraction and completeness

Lean-QEC's kernel basis (a basis of the null space of a parity-check matrix) is produced by
an **external Python script**, and the correctness of that script is not part of the
trusted base: the companion paper states that only the rank and the orthogonality are
checked after the fact. This module supplies a **proof inside the kernel**: a set of
generators is read directly off the pivot structure of row reduction, and
  `ker(H) = span(kernel generators)`

is closed in both directions inside the Lean kernel. With it, the step "the kernel basis is
produced by an external script" drops out of the trusted base.

## Mechanism

Row reduction outputs a mutually reduced set of pivot rows `D` (see `IsReduced`). The pivot
columns are the occupied columns and the remaining columns are the **free columns**. For
each free column `j` the kernel vector is taken to be
  `kerVec D j := e_j + ∑_{r ∈ D} (r_j) · e_{pivot(r)}`

that is, `e_j` corrected along the pivot directions by the entry of each row in column `j`.
Orthogonality comes from (R2): every row takes the value 1 at its own pivot column and 0 at
the pivot columns of the other rows, so the two kinds of contribution cancel exactly.

## Main results

* `kerVec_mem_kerL`: a kernel vector really does lie in the kernel (the soundness
  direction).
* `kerL_le_spanL_kerBasis`: every vector in the kernel is a linear combination of the
  kernel generators (the **completeness direction**).
* `kerL_rowReduce`: `ker H = span (kerBasis (rowReduce H))`, bringing the two sides
  together.
* `hammingNorm_kerVec_le` / `kerVec_ne_zero` / `exists_light_mem_kerL`: the
  **Singleton-type count**; when the kernel is nontrivial it contains a nonzero element of
  weight at most the rank plus one. The frontier argument in the companion paper uses
  exactly this step.
-/

@[expose] public section

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-- The unit vector `e_i` (1 at the `i`-th coordinate and 0 elsewhere). -/
def unitVec (i : Fin n) : Vec n := fun j => if j = i then 1 else 0

@[simp] lemma unitVec_apply (i j : Fin n) : unitVec i j = if j = i then 1 else 0 := rfl

/-! ## Single-term summation helpers (collapsing a column-selection sum to one term) -/

/-- `∑ i, u i * (if i = a then 1 else 0) = u a`. -/
lemma sum_mul_ite_self (u : Vec n) (a : Fin n) :
    ∑ i, u i * (if i = a then (1 : ZMod 2) else 0) = u a := by
  have h := Finset.sum_eq_single (s := Finset.univ)
    (f := fun i => u i * (if i = a then (1 : ZMod 2) else 0)) a
    (fun b _ hne => by rw [ite_eq_right (fun h => hne h), mul_zero])
    (fun hnot => absurd (Finset.mem_univ a) hnot)
  rw [h, ite_eq_left rfl, mul_one]

/-- `∑ i, u i * (if a = i then c else 0) = u a * c`. -/
lemma sum_mul_ite_eq (u : Vec n) (a : Fin n) (c : ZMod 2) :
    ∑ i, u i * (if a = i then c else 0) = u a * c := by
  have h := Finset.sum_eq_single (s := Finset.univ)
    (f := fun i => u i * (if a = i then c else 0)) a
    (fun b _ hne => by rw [ite_eq_right (fun h => hne h.symm), mul_zero])
    (fun hnot => absurd (Finset.mem_univ a) hnot)
  rw [h, ite_eq_left rfl]

/-- `∑ i, (if i = a then u i else 0) = u a`. -/
lemma sum_ite_self (u : Vec n) (a : Fin n) :
    ∑ i, (if i = a then u i else 0) = u a := by
  have h := Finset.sum_eq_single (s := Finset.univ)
    (f := fun i => if i = a then u i else 0) a
    (fun b _ hne => by rw [ite_eq_right (fun h => hne h)])
    (fun hnot => absurd (Finset.mem_univ a) hnot)
  rw [h, ite_eq_left rfl]

/-! ## The kernel -/

/-- The kernel of a list of rows: all vectors orthogonal to every row (zero GF(2) dot
product).

This is the algebraic description of the **error space** of a quantum error-correcting
code, namely the Pauli operators commuting with every parity-check row. It is tied to
LeanQEC's `LinearMap.ker M.toLin'` through `mem_ker_iff_dotProd_rows_eq_zero`. -/
def kerL (L : List (Vec n)) : Submodule (ZMod 2) (Vec n) where
  carrier := {x | ∀ r ∈ L, r ⬝ᵥ x = 0}
  zero_mem' := by intro r _; simp
  add_mem' := by
    intro x y hx hy r hr
    rw [dotProduct_add, hx r hr, hy r hr, add_zero]
  smul_mem' := by
    intro c x hx r hr
    rw [dotProduct_smul, hx r hr, smul_zero]

@[simp] lemma mem_kerL {L : List (Vec n)} {x : Vec n} :
    x ∈ kerL L ↔ ∀ r ∈ L, r ⬝ᵥ x = 0 := Iff.rfl

/-- The kernel depends only on the row space: two lists of rows with the same row space
give the same kernel. -/
lemma kerL_eq_of_spanL_eq {A B : List (Vec n)} (h : spanL A = spanL B) : kerL A = kerL B := by
  have key : ∀ {P Q : List (Vec n)}, spanL P ≤ spanL Q → kerL Q ≤ kerL P := by
    intro P Q hPQ x hx
    rw [mem_kerL] at hx ⊢
    intro p hp
    exact Submodule.span_induction
      (fun y hy => hx y hy) (by simp)
      (fun u v _ _ ihu ihv => by rw [add_dotProduct, ihu, ihv, add_zero])
      (fun c u _ ihu => by rw [smul_dotProduct, ihu, smul_zero])
      (hPQ (subset_spanL hp))
  exact le_antisymm (key h.ge) (key h.le)

/-! ## Pivot columns and free columns -/

/-- The set of pivot columns. -/
def pivCols (D : List (PivRow n)) : Finset (Fin n) := (D.map (·.2)).toFinset

/-- A free column: a column that is not the pivot column of any row. -/
def IsFreeCol (D : List (PivRow n)) (j : Fin n) : Prop := ∀ ri ∈ D, ri.2 ≠ j

lemma mem_pivCols {D : List (PivRow n)} {i : Fin n} :
    i ∈ pivCols D ↔ ∃ ri ∈ D, ri.2 = i := by
  rw [pivCols, List.mem_toFinset, List.mem_map]

/-- The paired form of (R2): the entry of any pivot row at any pivot column is of
Kronecker type. -/
lemma IsReduced.row_apply_piv {D : List (PivRow n)} (hD : IsReduced D)
    {ri rj : PivRow n} (hri : ri ∈ D) (hrj : rj ∈ D) :
    ri.1 rj.2 = if ri = rj then 1 else 0 := by
  by_cases h : ri = rj
  · rw [ite_eq_left h, h]; exact hD.1 rj hrj
  · rw [ite_eq_right h]; exact hD.2 ri hri rj hrj h

/-! ## Kernel vectors -/

/-- The kernel vector attached to the free column `j`: `e_j` plus the pivot corrections
determined by the entries of the rows in column `j`. -/
def kerVec (D : List (PivRow n)) (j : Fin n) : Vec n :=
  fun i => (if i = j then 1 else 0) + ∑ ri ∈ D.toFinset, (if ri.2 = i then ri.1 j else 0)

lemma kerVec_apply (D : List (PivRow n)) (j i : Fin n) :
    kerVec D j i
      = (if i = j then 1 else 0) + ∑ ri ∈ D.toFinset, (if ri.2 = i then ri.1 j else 0) := rfl

/-- On a free column the kernel vector is just `e_j`: every correction term
vanishes. -/
lemma kerVec_apply_free {D : List (PivRow n)} {j i : Fin n} (hi : IsFreeCol D i) :
    kerVec D j i = if i = j then 1 else 0 := by
  rw [kerVec_apply]
  have hsum : ∑ ri ∈ D.toFinset, (if ri.2 = i then ri.1 j else 0) = 0 := by
    refine Finset.sum_eq_zero fun ri hri => ?_
    rw [ite_eq_right (hi ri (List.mem_toFinset.mp hri))]
  rw [hsum, add_zero]

/-- On a pivot column the kernel vector reads off the corresponding entry of that
row. -/
lemma kerVec_apply_piv {D : List (PivRow n)} (hD : IsReduced D) {j : Fin n} {rk : PivRow n}
    (hrk : rk ∈ D) :
    kerVec D j rk.2 = (if rk.2 = j then 1 else 0) + rk.1 j := by
  rw [kerVec_apply]
  congr 1
  have hsingle : ∑ ri ∈ D.toFinset, (if ri.2 = rk.2 then ri.1 j else 0) = rk.1 j := by
    have h := Finset.sum_eq_single (s := D.toFinset)
      (f := fun ri => if ri.2 = rk.2 then ri.1 j else 0) rk
      (fun b hb hne => by
        rw [ite_eq_right]
        intro hcon
        exact hne (hD.pivot_inj b (List.mem_toFinset.mp hb) rk hrk hcon))
      (fun hnot => absurd (List.mem_toFinset.mpr hrk) hnot)
    rwa [ite_eq_left rfl] at h
  exact hsingle

/-- **Soundness direction**: a kernel vector really does lie in the kernel of these rows.

The proof cancels two sums: the dot product of `rk` with the kernel vector is expanded into
a double sum, the order of summation is exchanged, and the Kronecker form of (R1)/(R2)
collapses the inner sum to a single term. -/
lemma kerVec_mem_kerL {D : List (PivRow n)} (hD : IsReduced D) (j : Fin n) :
    kerVec D j ∈ kerL (rowList D) := by
  rw [mem_kerL]
  intro r hr
  obtain ⟨rk, hrk, rfl⟩ := List.mem_map.mp hr
  rw [dotProduct]
  have hexp : ∀ i : Fin n, kerVec D j i
      = (if i = j then 1 else 0) + ∑ ri ∈ D.toFinset, (if ri.2 = i then ri.1 j else 0) :=
    fun i => kerVec_apply D j i
  simp only [hexp]
  simp only [mul_add]
  rw [Finset.sum_add_distrib]
  have h1 : ∑ i, rk.1 i * (if i = j then (1 : ZMod 2) else 0) = rk.1 j :=
    sum_mul_ite_self rk.1 j
  have h2 : ∑ i, rk.1 i * (∑ ri ∈ D.toFinset, (if ri.2 = i then ri.1 j else 0)) = rk.1 j := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hinner : ∀ ri ∈ D.toFinset,
        ∑ i, rk.1 i * (if ri.2 = i then ri.1 j else 0) = rk.1 ri.2 * ri.1 j :=
      fun ri _ => sum_mul_ite_eq rk.1 ri.2 (ri.1 j)
    rw [Finset.sum_congr rfl hinner]
    have hsingle : ∑ b ∈ D.toFinset, rk.1 b.2 * b.1 j = rk.1 rk.2 * rk.1 j :=
      Finset.sum_eq_single (s := D.toFinset) (f := fun b => rk.1 b.2 * b.1 j) rk
        (fun b hb hne => by
          rw [hD.2 rk hrk b (List.mem_toFinset.mp hb) (fun h => hne h.symm), zero_mul])
        (fun hnot => absurd (List.mem_toFinset.mpr hrk) hnot)
    rw [hsingle, hD.1 rk hrk, one_mul]
  rw [h1, h2]
  exact CharTwo.add_self_eq_zero (rk.1 j)

/-! ## The Singleton-type count: how light a kernel vector is -/

/-- **A kernel vector is nonzero**: on a free column it is just `e_j`, so it cannot be the
zero vector. -/
theorem kerVec_ne_zero {D : List (PivRow n)} {j : Fin n} (hj : IsFreeCol D j) :
    kerVec D j ≠ 0 := by
  intro hzero
  have h1 : kerVec D j j = 1 := by rw [kerVec_apply_free hj, ite_eq_left rfl]
  rw [hzero] at h1
  simp only [Pi.zero_apply] at h1
  exact zero_ne_one h1

/-- **The Singleton-type count**: the support of a kernel vector lies in
$\{j\}\cup$ the pivot columns, so its weight is at most $1+\#D$.

This holds for **every** column `j`, free or not: `kerVec D j` can be nonzero only at `j`
and at the pivot columns, and every other column is free and hence vanishes by
`kerVec_apply_free`. There are exactly `#D` pivot columns, and `#D` is the rank. Together
with `kerVec_ne_zero` this makes "a nontrivial kernel $\Rightarrow$ there is a nonzero
kernel vector of weight $\le\rho+1$" a theorem rather than an informal remark. -/
theorem hammingNorm_kerVec_le (D : List (PivRow n)) (j : Fin n) :
    hammingNorm (kerVec D j) ≤ D.length + 1 := by
  rw [← weight_eq_hammingNorm]
  calc (support (kerVec D j)).card
      ≤ (insert j (pivCols D)).card := Finset.card_le_card (fun i hi => ?_)
    _ ≤ (pivCols D).card + 1 := Finset.card_insert_le j (pivCols D)
    _ ≤ D.length + 1 := by
        have h := List.toFinset_card_le (D.map (·.2))
        simp only [pivCols, List.length_map] at h ⊢
        omega
  rw [support, Finset.mem_filter] at hi
  obtain ⟨-, hne⟩ := hi
  rw [Finset.mem_insert, mem_pivCols]
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hij, hnot⟩ := hcon
  have hfree : IsFreeCol D i := fun ri hri hcon2 => hnot ⟨ri, hri, hcon2⟩
  rw [kerVec_apply_free hfree, ite_eq_right hij] at hne
  exact hne rfl

/-! ## Kernel generators -/

/-- The kernel generators: each free column yields one kernel vector. (There are exactly
`n − #D` free columns, so the number of generators is the dimension of the kernel; see the
completeness half of `kerL_rowReduce`.) -/
def kerBasis (D : List (PivRow n)) : List (Vec n) :=
  ((List.finRange n).filter (fun j => decide (j ∉ pivCols D))).map (kerVec D)

lemma mem_kerBasis {D : List (PivRow n)} {x : Vec n} :
    x ∈ kerBasis D ↔ ∃ j, j ∉ pivCols D ∧ kerVec D j = x := by
  simp only [kerBasis, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, of_decide_eq_true hj, rfl⟩
  · rintro ⟨j, hjp, rfl⟩
    exact ⟨j, decide_eq_true hjp, rfl⟩

/-! ## Completeness -/

/-- A vector supported on the pivot columns is recovered from the pivot columns. -/
lemma eq_sum_of_piv_support {D : List (PivRow n)} (hD : IsReduced D) {z : Vec n}
    (hz : ∀ i, (∀ ri ∈ D, ri.2 ≠ i) → z i = 0) :
    ∀ m, z m = ∑ rl ∈ D.toFinset, (if rl.2 = m then z rl.2 else 0) := by
  intro m
  by_cases hm : ∃ rl ∈ D, rl.2 = m
  · obtain ⟨rl, hrl, rfl⟩ := hm
    have hsingle : ∑ b ∈ D.toFinset, (if b.2 = rl.2 then z b.2 else 0) = z rl.2 := by
      have h := Finset.sum_eq_single (s := D.toFinset)
        (f := fun b => if b.2 = rl.2 then z b.2 else 0) rl
        (fun b hb hne => by
          rw [ite_eq_right]
          intro hcon
          exact hne (hD.pivot_inj b (List.mem_toFinset.mp hb) rl hrl hcon))
        (fun hnot => absurd (List.mem_toFinset.mpr hrl) hnot)
      rwa [ite_eq_left rfl] at h
    rw [hsingle]
  · have hz0 : z m = 0 := hz m (fun ri hri hcon => hm ⟨ri, hri, hcon⟩)
    have hsum0 : ∑ b ∈ D.toFinset, (if b.2 = m then z b.2 else 0) = 0 := by
      refine Finset.sum_eq_zero fun b hb => ?_
      rw [ite_eq_right]
      intro hcon
      exact hm ⟨b, List.mem_toFinset.mp hb, hcon⟩
    rw [hz0, hsum0]

/-- **The entries at the pivot columns determine everything**: a vector supported on the
pivot columns that also lies in the kernel must be zero. -/
lemma eq_zero_of_piv_support {D : List (PivRow n)} (hD : IsReduced D) {z : Vec n}
    (hz : ∀ i, (∀ ri ∈ D, ri.2 ≠ i) → z i = 0) (hzker : ∀ ri ∈ D, ri.1 ⬝ᵥ z = 0) :
    z = 0 := by
  have hzsum := eq_sum_of_piv_support hD hz
  funext m
  by_cases hm : ∃ rk ∈ D, rk.2 = m
  · obtain ⟨rk, hrk, rfl⟩ := hm
    have hdot : rk.1 ⬝ᵥ z = z rk.2 := by
      rw [dotProduct]
      have step1 : ∑ i, rk.1 i * z i
          = ∑ i, rk.1 i * (∑ rl ∈ D.toFinset, (if rl.2 = i then z rl.2 else 0)) :=
        Finset.sum_congr rfl fun i _ => by rw [hzsum i]
      rw [step1]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      have hinner : ∀ rl ∈ D.toFinset,
          ∑ x, rk.1 x * (if rl.2 = x then z rl.2 else 0) = rk.1 rl.2 * z rl.2 :=
        fun rl _ => sum_mul_ite_eq rk.1 rl.2 (z rl.2)
      rw [Finset.sum_congr rfl hinner]
      have hsingle : ∑ b ∈ D.toFinset, rk.1 b.2 * z b.2 = rk.1 rk.2 * z rk.2 :=
        Finset.sum_eq_single (s := D.toFinset) (f := fun b => rk.1 b.2 * z b.2) rk
          (fun b hb hne => by
            rw [hD.2 rk hrk b (List.mem_toFinset.mp hb) (fun h => hne h.symm), zero_mul])
          (fun hnot => absurd (List.mem_toFinset.mpr hrk) hnot)
      rw [hsingle, hD.1 rk hrk, one_mul]
    rw [← hdot]
    exact hzker rk hrk
  · exact hz m (fun ri hri hcon => hm ⟨ri, hri, hcon⟩)

/-- **Completeness direction**: every vector in the kernel is a linear combination of the
kernel generators. -/
lemma kerL_le_spanL_kerBasis {D : List (PivRow n)} (hD : IsReduced D) :
    kerL (rowList D) ≤ spanL (kerBasis D) := by
  intro x hx
  rw [mem_kerL] at hx
  set y := ∑ j ∈ Finset.univ.filter (fun j => j ∉ pivCols D), x j • kerVec D j with hy
  have hy_mem : y ∈ spanL (kerBasis D) := by
    rw [hy]
    refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (subset_spanL ?_)
    rw [mem_kerBasis]
    exact ⟨j, (Finset.mem_filter.mp hj).2, rfl⟩
  have hy_ker : y ∈ kerL (rowList D) := by
    rw [hy]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (kerVec_mem_kerL hD j)
  have hxy_ker : ∀ rk ∈ D, rk.1 ⬝ᵥ (x + y) = 0 := by
    intro rk hrk
    have h1 : rk.1 ⬝ᵥ x = 0 := hx rk.1 (List.mem_map_of_mem hrk)
    have h2 : rk.1 ⬝ᵥ y = 0 := by
      rw [mem_kerL] at hy_ker; exact hy_ker rk.1 (List.mem_map_of_mem hrk)
    rw [dotProduct_add, h1, h2, add_zero]
  have hxy_free : ∀ i, (∀ ri ∈ D, ri.2 ≠ i) → (x + y) i = 0 := by
    intro i hi
    have hiF : i ∈ Finset.univ.filter (fun j => j ∉ pivCols D) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i, by
        rw [mem_pivCols]
        rintro ⟨ri, hri, hcon⟩
        exact hi ri hri hcon⟩
    have hyi : y i = x i := by
      rw [hy, Finset.sum_apply]
      have hsingle : ∑ j ∈ Finset.univ.filter (fun j => j ∉ pivCols D),
            (x j • kerVec D j) i = (x i • kerVec D i) i :=
        Finset.sum_eq_single (s := Finset.univ.filter (fun j => j ∉ pivCols D))
          (f := fun j => (x j • kerVec D j) i) i
          (fun b _ hne => by
            rw [Pi.smul_apply, kerVec_apply_free hi, ite_eq_right (fun h => hne h.symm),
              smul_zero])
          (fun hnot => absurd hiF hnot)
      rw [hsingle, Pi.smul_apply, kerVec_apply_free hi, ite_eq_left rfl, smul_eq_mul,
        mul_one]
    rw [Pi.add_apply, hyi]
    exact CharTwo.add_self_eq_zero (x i)
  have hzero : x + y = 0 := eq_zero_of_piv_support hD hxy_free hxy_ker
  have hxy : x = y := by
    have h := add_add_same_left x y
    rw [hzero, add_zero] at h
    exact h
  rw [hxy]
  exact hy_mem

/-! ## Agreement with the original code -/

/-- **Main theorem**: the kernel equals the space spanned by the kernel generators. The
list of rows is first put through the trusted row reduction, and the kernel generators are
read directly off the pivot structure that it outputs; the whole chain closes inside the
kernel. -/
theorem kerL_rowReduce (L : List (Vec n)) :
    kerL L = spanL (kerBasis (rowReduce L)) := by
  rw [← kerL_eq_of_spanL_eq (spanL_rowReduce L)]
  refine le_antisymm (kerL_le_spanL_kerBasis (isReduced_rowReduce L)) ?_
  refine Submodule.span_le.2 fun x hx => ?_
  have hx' : x ∈ kerBasis (rowReduce L) := hx
  rw [mem_kerBasis] at hx'
  obtain ⟨j, -, rfl⟩ := hx'
  exact kerVec_mem_kerL (isReduced_rowReduce L) j

/-- **The row-list form of the frontier-argument step**: as long as `rowReduce L` still
has a free column, that is, as long as the kernel is nontrivial, the kernel of `L` contains
a nonzero element of weight $\le 1+\#(rowReduce L)$.

Now $\#(rowReduce L)$ is the rank of `L`, so this is the full statement that a matrix of
rank $\rho$ has a nonzero kernel vector of weight $\le\rho+1$: existence comes from the
completeness direction of `kerL_rowReduce`, while nonzeroness and the weight bound come
from the two results above. -/
theorem exists_light_mem_kerL (L : List (Vec n)) {j : Fin n}
    (hj : IsFreeCol (rowReduce L) j) :
    ∃ v ∈ kerL L, v ≠ 0 ∧ hammingNorm v ≤ (rowReduce L).length + 1 := by
  refine ⟨kerVec (rowReduce L) j, ?_, kerVec_ne_zero hj, hammingNorm_kerVec_le _ _⟩
  rw [kerL_rowReduce]
  refine subset_spanL (mem_kerBasis.mpr ⟨j, fun hmem => ?_, rfl⟩)
  obtain ⟨ri, hri, hcon⟩ := mem_pivCols.mp hmem
  exact hj ri hri hcon

/-- **The indexed form**: the kernel vector given by the free column `j` lies in the
kernel, has weight at most the rank plus one, and takes the value $1$ at `j`.

The clause "takes the value 1 at `j`" is needed for the frontier argument: the witness
construction for the hypergraph product requires the seed kernel vector to be nonzero at
some index (`s a₀ = 1` in `xwLeft`). -/
theorem exists_light_mem_kerL_apply (L : List (Vec n)) {j : Fin n}
    (hj : IsFreeCol (rowReduce L) j) :
    kerVec (rowReduce L) j ∈ kerL L
      ∧ hammingNorm (kerVec (rowReduce L) j) ≤ (rowReduce L).length + 1
      ∧ kerVec (rowReduce L) j j = 1 := by
  refine ⟨?_, hammingNorm_kerVec_le _ _, ?_⟩
  · rw [kerL_rowReduce]
    refine subset_spanL (mem_kerBasis.mpr ⟨j, fun hmem => ?_, rfl⟩)
    obtain ⟨ri, hri, hcon⟩ := mem_pivCols.mp hmem
    exact hj ri hri hcon
  · rw [kerVec_apply_free hj, ite_eq_left rfl]

/-! ## Agreement with the LeanQEC matrix interface -/

/-- The kernel of a parity-check **matrix** (LeanQEC's `LinearMap.ker M.toLin'`) agrees
with the kernel of its list of rows. This bridge lets the row-space theorems already
available in LeanQEC act directly on `kerL` of this module. -/
theorem LinearMap.ker_eq_kerL_ofFn {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    LinearMap.ker M.toLin' = kerL (List.ofFn fun i => M i) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [mem_kerL]
    rw [mem_ker_iff_dotProd_rows_eq_zero] at hx
    intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact hx i
  · intro x hx
    rw [mem_ker_iff_dotProd_rows_eq_zero]
    intro i
    exact (mem_kerL.mp hx) (M i) (List.mem_ofFn.mpr ⟨i, rfl⟩)

/-- **Main theorem for external use (LeanQEC interface version)**: the kernel of a
parity-check matrix `M` equals the space spanned by the kernel generators. The generators
are read directly off the list of rows of `M` by the trusted row reduction, and the whole
procedure closes inside the kernel. -/
theorem LinearMap.ker_eq_spanL_kerBasis_ofFn {m : ℕ}
    (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    LinearMap.ker M.toLin' = spanL (kerBasis (rowReduce (List.ofFn fun i => M i))) := by
  rw [LinearMap.ker_eq_kerL_ofFn, kerL_rowReduce]

end QECCertificates
