/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.RemainingRank

/-!
# The kernel criterion for a fair unread answer

A query at an unread coordinate can be flipped while preserving all observed
values and equations exactly when its column is in the span of the other
unread columns.  This does not require the remaining matrix to have full row
rank.  Otherwise every two compatible assignments agree at the query.
-/

@[expose] public section

namespace Klr.AffineAnswer

open AffineObservation

variable {ι : Type*} [DecidableEq ι] {r : ℕ}

/-- The column of a linear system indexed by one coordinate. -/
def column (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) (q : ι) : Fin r → ZMod 2 :=
  D (Pi.single q 1)

omit [DecidableEq ι] in
/-- The unread image depends on the observed set, not its decision procedure. -/
theorem unreadMap_range_congr
    (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    {O P : Set ι} [dO : DecidablePred (· ∈ O)] [dP : DecidablePred (· ∈ P)]
    (h : O = P) : LinearMap.range (unreadMap D O) = LinearMap.range (unreadMap D P) := by
  subst P
  cases Subsingleton.elim dO dP
  rfl

/-- A vector vanishing on the observed coordinates splits into its next coordinate
and its remaining unread part. -/
theorem unread_insert_decomposition (O : Set ι) [DecidablePred (· ∈ O)]
    (q : ι) (x : ι → ZMod 2) (hx : observedPart O x = 0) :
    x = extendUnread (insert q O) (unreadPart (insert q O) x) + x q • Pi.single q 1 := by
  funext i
  by_cases hi : i = q
  · subst i
    simp [extendUnread, Pi.smul_apply]
  · by_cases hO : i ∈ O
    · have hx0 : x i = 0 := congrFun hx ⟨i, hO⟩
      simp [extendUnread, unreadPart, Pi.smul_apply, hi, hO, hx0]
    · simp [extendUnread, unreadPart, Pi.smul_apply, hi, hO]

/-- A single unread column belongs to the unread image. -/
theorem column_mem_unreadRange
    (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (O : Set ι) [DecidablePred (· ∈ O)] (q : ι) (hq : q ∉ O) :
    column D q ∈ LinearMap.range (unreadMap D O) := by
  refine ⟨unreadPart O (Pi.single q 1), ?_⟩
  change D (extendUnread O (unreadPart O (Pi.single q 1))) = D (Pi.single q 1)
  congr 1
  apply extendUnread_unreadPart_of_observed_zero
  funext i
  have hi : i.val ≠ q := by intro h; exact hq (h ▸ i.property)
  simp [observedPart, hi]

/-- Adding the queried unread column to the other unread image recovers the current image. -/
theorem unreadRange_eq_withColumn
    (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (O : Set ι) [DecidablePred (· ∈ O)] (q : ι) (hq : q ∉ O) :
    LinearMap.range (unreadMap D O) =
      Affine.withColumn (unreadMap D (insert q O)) (column D q) := by
  apply le_antisymm
  · rintro y ⟨u, rfl⟩
    let x := extendUnread O u
    have hx : observedPart O x = 0 := by
      funext i
      simp [x, observedPart, extendUnread, i.property]
    have he := congrArg D (unread_insert_decomposition O q x hx)
    simp only [map_add, map_smul] at he
    change D x ∈ LinearMap.range (unreadMap D (insert q O)) ⊔
      Submodule.span (ZMod 2) {column D q}
    apply Submodule.mem_sup.mpr
    refine ⟨unreadMap D (insert q O) (unreadPart (insert q O) x),
      LinearMap.mem_range_self _ _, x q • column D q, ?_, he.symm⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply sup_le
    · exact unreadMap_range_antitone D (Set.subset_insert q O)
    · exact Submodule.span_le.mpr (by
        intro c hc
        rcases Set.mem_singleton_iff.mp hc with rfl
        exact column_mem_unreadRange D O q hq)

/-- A column is redundant exactly when a kernel vector flips it and leaves observed
coordinates fixed.  The resulting translation will preserve the conditioned input law. -/
theorem column_mem_iff_kernel_vector
    (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (O : Set ι) [DecidablePred (· ∈ O)] (q : ι) (hq : q ∉ O) :
    column D q ∈ LinearMap.range (unreadMap D (insert q O)) ↔
      ∃ k : ι → ZMod 2, observedPart O k = 0 ∧ D k = 0 ∧ k q = 1 := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨Pi.single q 1 - extendUnread (insert q O) u, ?_, ?_, ?_⟩
    · funext i
      have hi : i.val ≠ q := by intro h; exact hq (h ▸ i.property)
      simp [observedPart, extendUnread, hi, i.property]
    · change D (Pi.single q 1 - extendUnread (insert q O) u) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hu.symm
    · simp [extendUnread]
  · rintro ⟨k, hkO, hkD, hkq⟩
    have he := congrArg D (unread_insert_decomposition O q k hkO)
    simp only [map_add, hkD, hkq, one_smul] at he
    have hneg : unreadMap D (insert q O) (unreadPart (insert q O) k) = -column D q := by
      apply eq_neg_of_add_eq_zero_left
      exact he.symm
    refine ⟨-unreadPart (insert q O) k, ?_⟩
    rw [map_neg, hneg, neg_neg]

/-- Deleting the queried unread column strictly lowers numerical rank exactly when
that column is not in the span of the other unread columns. -/
theorem rank_drop_iff_column_not_mem
    (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (O : Set ι) [DecidablePred (· ∈ O)] (q : ι) (hq : q ∉ O) :
    Module.finrank (ZMod 2) (LinearMap.range (unreadMap D (insert q O))) <
        Module.finrank (ZMod 2) (LinearMap.range (unreadMap D O)) ↔
      column D q ∉ LinearMap.range (unreadMap D (insert q O)) := by
  rw [unreadRange_eq_withColumn D O q hq]
  exact Affine.rank_drop_iff_not_mem_range _ _

/-- If the queried column is not redundant, any two compatible assignments with
the same observed values must have the same next answer. -/
theorem answer_eq_of_column_not_mem
    (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (O : Set ι) [DecidablePred (· ∈ O)] (q : ι) (hq : q ∉ O)
    (hc : column D q ∉ LinearMap.range (unreadMap D (insert q O)))
    {x y : ι → ZMod 2} (hO : observedPart O x = observedPart O y) (hD : D x = D y) :
    x q = y q := by
  by_contra hqxy
  apply hc
  apply (column_mem_iff_kernel_vector D O q hq).mpr
  refine ⟨(x q - y q)⁻¹ • (x - y), ?_, ?_, ?_⟩
  · funext i
    have hi : x i.val = y i.val := congrFun hO i
    simp [observedPart, Pi.smul_apply, hi]
  · simp [map_smul, map_sub, hD]
  · simp [Pi.smul_apply, smul_eq_mul, sub_ne_zero.mpr hqxy]

end Klr.AffineAnswer
