/-
Copyright (c) 2026 Richard Bean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Bean
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import LeanPool.LatinQuarter.LowerBound
public import LeanPool.LatinQuarter.CornerSize

/-!
# The quarter bound for critical sets of Latin squares

The definitions of Latin square, agreement, and unique completion are in
`Basic.lean`. The lower bound is proved for every Latin square. The matching
upper bound is furnished by the two corner triangles of the cyclic square.
-/

@[expose] public section

namespace LatinQuarter

/-- A critical set is a defining set with no proper defining subset. -/
def IsCritical {n : ℕ} (P : Finset (Cell n)) (L : Square n) : Prop :=
  IsDefining P L ∧ ∀ Q : Finset (Cell n), Q ⊂ P → ¬ IsDefining Q L

theorem critical_set_lower_bound {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (h : IsCritical P L) : n * n / 4 ≤ P.card :=
  defining_set_lower_bound P L h.1

theorem cornerSet_card (n : ℕ) (hn : 0 < n) :
    (cornerSet n).card = n * n / 4 := by
  apply le_antisymm (cornerSet_card_le n)
  exact defining_set_lower_bound _ _ (cornerSet_isDefining n hn)

theorem cornerSet_isCritical (n : ℕ) (hn : 0 < n) :
    IsCritical (cornerSet n) (cyclic n) := by
  refine ⟨cornerSet_isDefining n hn, ?_⟩
  intro Q hQ hdef
  have hlt := Finset.card_lt_card hQ
  have hlo := defining_set_lower_bound Q (cyclic n) hdef
  rw [cornerSet_card n hn] at hlt
  omega

/-- The smallest critical-set size among all labelled Latin squares of
order `n`. This definition contains no bound or cyclic-square assumption. -/
noncomputable def scs (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ (L : Square n) (P : Finset (Cell n)),
    IsCritical P L ∧ P.card = m}

/-- The smallest critical-set size in one specified square. -/
noncomputable def scsOf {n : ℕ} (L : Square n) : ℕ :=
  sInf {m : ℕ | ∃ P : Finset (Cell n), IsCritical P L ∧ P.card = m}

/-- Main theorem: the least size over all Latin squares is `floor(n²/4)`. -/
theorem scs_eq_quarter (n : ℕ) (hn : 0 < n) : scs n = n * n / 4 := by
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨cyclic n, cornerSet n, cornerSet_isCritical n hn, cornerSet_card n hn⟩
  · rintro m ⟨L, P, hP, rfl⟩
    exact critical_set_lower_bound P L hP

/-- The cyclic Latin square attains the same least size. -/
theorem cyclic_scs_eq_quarter (n : ℕ) (hn : 0 < n) :
    scsOf (cyclic n) = n * n / 4 := by
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨cornerSet n, cornerSet_isCritical n hn, cornerSet_card n hn⟩
  · rintro m ⟨P, hP, rfl⟩
    exact critical_set_lower_bound P (cyclic n) hP

/-- A single statement giving the unrestricted lower bound and an
explicit critical set attaining it in the cyclic square. -/
theorem quarter_bound (n : ℕ) (hn : 0 < n) :
    (∀ (L : Square n) (P : Finset (Cell n)),
      IsDefining P L → n * n / 4 ≤ P.card) ∧
    IsCritical (cornerSet n) (cyclic n) ∧
    (cornerSet n).card = n * n / 4 :=
  ⟨fun L P h => defining_set_lower_bound P L h,
    cornerSet_isCritical n hn, cornerSet_card n hn⟩

end LatinQuarter
