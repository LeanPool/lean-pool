/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.AdianRabin.Gordon.Construction

/-!
# Gordon's printed condition (2.1)

This file separates Gordon's original torsion hypothesis from the
proof-oriented data used by the presentation construction.  Repeated order
values are removed by choosing one representative of each value.  The
remaining partial degree assignment is extended injectively by assigning all
unselected generators values above the sum of the selected orders.
-/

@[expose] public section

namespace Undecidability.Gordon

/-- Gordon's condition (2.1), before passing to a minimal witness.

The selected generators are distinct, but their abelianized orders `q` need
not be distinct. -/
structure Condition21 (P : FP n m) where
  /-- The number of generators selected for the torsion condition. -/
  p : ℕ
  /-- The distinct generator indices selected for the torsion condition. -/
  selected : Fin p ↪ Fin n
  /-- The prescribed orders of the selected generators in the abelianization. -/
  q : Fin p → ℕ
  q_pos : ∀ i, 0 < q i
  gcd_q : Finset.univ.gcd q = 1
  exactOrder : ∀ i,
    orderOf (Abelianization.of
      (PresentedGroup.of (selected i) : P.Group)) = q i

namespace Condition21

variable {n m : ℕ} {P : FP n m}

/-- The finite set of distinct abelianized orders appearing in a witness to
condition (2.1). -/
def orderValues (condition : Condition21 P) : Finset ℕ :=
  Finset.univ.image condition.q

/-- Enumerate the distinct order values by a finite ordinal. -/
noncomputable def valueEquiv (condition : Condition21 P) :
    Fin condition.orderValues.card ≃ condition.orderValues :=
  condition.orderValues.equivFin.symm

/-- Choose one original selected generator for each distinct order value. -/
noncomputable def representative (condition : Condition21 P)
    (q : condition.orderValues) : Fin condition.p :=
  Classical.choose (Finset.mem_image.mp q.property)

theorem q_representative (condition : Condition21 P)
    (q : condition.orderValues) :
    condition.q (condition.representative q) = q.1 :=
  (Classical.choose_spec (Finset.mem_image.mp q.property)).2

/-- Distinct order values have distinct chosen representatives. -/
noncomputable def representativeEmbedding (condition : Condition21 P) :
    condition.orderValues ↪ Fin condition.p where
  toFun := condition.representative
  inj' := by
    intro q r hqr
    apply Subtype.ext
    rw [← condition.q_representative q,
      ← condition.q_representative r, hqr]

/-- The duplicate-free selection of host generators. -/
noncomputable def normalizedSelected (condition : Condition21 P) :
    Fin condition.orderValues.card ↪ Fin n :=
  condition.valueEquiv.toEmbedding |>.trans
    condition.representativeEmbedding |>.trans condition.selected

/-- The duplicate-free list of exact abelianized orders. -/
noncomputable def normalizedQ (condition : Condition21 P) :
    Fin condition.orderValues.card → ℕ :=
  fun i ↦ (condition.valueEquiv i).1

theorem normalizedQ_injective (condition : Condition21 P) :
    Function.Injective condition.normalizedQ := by
  intro i j hij
  apply condition.valueEquiv.injective
  exact Subtype.ext hij

theorem normalizedQ_pos (condition : Condition21 P)
    (i : Fin condition.orderValues.card) :
    0 < condition.normalizedQ i := by
  change 0 < (condition.valueEquiv i).1
  rw [← condition.q_representative (condition.valueEquiv i)]
  exact condition.q_pos _

theorem normalized_exactOrder (condition : Condition21 P)
    (i : Fin condition.orderValues.card) :
    orderOf (Abelianization.of
      (PresentedGroup.of (condition.normalizedSelected i) : P.Group)) =
        condition.normalizedQ i := by
  rw [show condition.normalizedSelected i =
      condition.selected
        (condition.representative (condition.valueEquiv i)) from rfl]
  rw [condition.exactOrder, condition.q_representative]
  rfl

theorem normalized_gcd (condition : Condition21 P) :
    Finset.univ.gcd condition.normalizedQ = 1 := by
  rw [Finset.gcd_eq_gcd_image]
  have himage :
      Finset.univ.image condition.normalizedQ = condition.orderValues := by
    ext q
    constructor
    · intro hq
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
      exact (condition.valueEquiv i).property
    · intro hq
      let q' : condition.orderValues := ⟨q, hq⟩
      obtain ⟨i, hi⟩ := condition.valueEquiv.surjective q'
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ i, ?_⟩
      exact congrArg Subtype.val hi
  rw [himage]
  have hgcd := condition.gcd_q
  rw [Finset.gcd_eq_gcd_image] at hgcd
  exact hgcd

/-- A bound above every duplicate-free selected order. -/
noncomputable def degreeBound (condition : Condition21 P) : ℕ :=
  Finset.univ.sum condition.normalizedQ

theorem normalizedQ_le_degreeBound (condition : Condition21 P)
    (i : Fin condition.orderValues.card) :
    condition.normalizedQ i ≤ condition.degreeBound :=
  Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
    (Finset.mem_univ i)

/-- A generator belongs to the duplicate-free selected family. -/
def IsNormalizedSelected (condition : Condition21 P) (j : Fin n) : Prop :=
  ∃ i, condition.normalizedSelected i = j

/-- Recover the unique selected index of a selected generator. -/
noncomputable def normalizedPreimage (condition : Condition21 P)
    (j : Fin n) (hj : condition.IsNormalizedSelected j) :
    Fin condition.orderValues.card :=
  Classical.choose hj

theorem normalizedSelected_preimage (condition : Condition21 P)
    (j : Fin n) (hj : condition.IsNormalizedSelected j) :
    condition.normalizedSelected (condition.normalizedPreimage j hj) = j :=
  Classical.choose_spec hj

/-- Extend the selected order values to a positive injective degree assignment
on all host generators.  Unselected generators receive values strictly above
the sum of the selected orders. -/
noncomputable def extendedDegree (condition : Condition21 P) (j : Fin n) : ℕ :=
  by
    classical
    exact if hj : condition.IsNormalizedSelected j then
      condition.normalizedQ (condition.normalizedPreimage j hj)
    else
      condition.degreeBound + j.1 + 1

theorem extendedDegree_selected (condition : Condition21 P)
    (i : Fin condition.orderValues.card) :
    condition.extendedDegree (condition.normalizedSelected i) =
      condition.normalizedQ i := by
  have hi : condition.IsNormalizedSelected
      (condition.normalizedSelected i) := ⟨i, rfl⟩
  rw [extendedDegree]
  simp only [dite_eq_left hi]
  congr 1
  apply condition.normalizedSelected.injective
  exact condition.normalizedSelected_preimage _ hi

theorem extendedDegree_pos (condition : Condition21 P) (j : Fin n) :
    0 < condition.extendedDegree j := by
  rw [extendedDegree]
  split_ifs with hj
  · exact condition.normalizedQ_pos _
  · omega

theorem extendedDegree_injective (condition : Condition21 P) :
    Function.Injective condition.extendedDegree := by
  intro i j hij
  by_cases hi : condition.IsNormalizedSelected i
  · by_cases hj : condition.IsNormalizedSelected j
    · rw [extendedDegree, dite_eq_left hi, extendedDegree, dite_eq_left hj] at hij
      have hpre : condition.normalizedPreimage i hi =
          condition.normalizedPreimage j hj :=
        condition.normalizedQ_injective hij
      calc
        i = condition.normalizedSelected
            (condition.normalizedPreimage i hi) :=
          (condition.normalizedSelected_preimage i hi).symm
        _ = condition.normalizedSelected
            (condition.normalizedPreimage j hj) := congrArg _ hpre
        _ = j := condition.normalizedSelected_preimage j hj
    · rw [extendedDegree, dite_eq_left hi, extendedDegree, dite_eq_right hj] at hij
      have hle := condition.normalizedQ_le_degreeBound
        (condition.normalizedPreimage i hi)
      omega
  · by_cases hj : condition.IsNormalizedSelected j
    · rw [extendedDegree, dite_eq_right hi, extendedDegree, dite_eq_left hj] at hij
      have hle := condition.normalizedQ_le_degreeBound
        (condition.normalizedPreimage j hj)
      omega
    · rw [extendedDegree, dite_eq_right hi, extendedDegree, dite_eq_right hj] at hij
      apply Fin.ext
      omega

/-- Normalize Gordon's printed condition (2.1) to the data required by the
one-extra-relator construction. -/
noncomputable def toTorsionData (condition : Condition21 P) : TorsionData P where
  p := condition.orderValues.card
  selected := condition.normalizedSelected
  q := condition.normalizedQ
  gcd_q := condition.normalized_gcd
  exactOrder := condition.normalized_exactOrder
  degree := condition.extendedDegree
  degree_pos := condition.extendedDegree_pos
  degree_injective := condition.extendedDegree_injective
  degree_selected := condition.extendedDegree_selected

end Condition21

end Undecidability.Gordon
