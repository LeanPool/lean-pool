/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.UniformSupport
public import LeanPool.KLRandomness.RandomMatrix
import Mathlib.Tactic.Positivity

/-!
# The actual finite experiment for sparse affine candidates

A candidate is a uniformly selected support of size `m`, paired independently
with a uniformly selected full-row-rank binary matrix with `m` columns.  A fixed
enumeration of each support identifies unread pool positions with matrix
columns.  Thus the probability bounds below are for an actual finite sample
space, with no assumed intersection moments or rank-failure estimates.
-/

@[expose] public section

namespace Klr.SparseCandidate

open FiniteProbability UniformSupport RandomMatrix
open scoped BigOperators

variable {M m r : ℕ}

/-- The support and full-rank matrix are sampled independently and uniformly. -/
abbrev Candidate (M m r : ℕ) := Support M m × FullRankMatrix (Fin m) r

/-- A fixed enumeration of the positions of a size-`m` support. -/
noncomputable def supportEquiv (S : Support M m) : Fin m ≃ S.val :=
  Fintype.equivOfCardEq (by simp [S.property])

/-- The corresponding injection of column indices into pool positions. -/
noncomputable def position (S : Support M m) : Fin m ↪ Fin M where
  toFun j := (supportEquiv S j).val
  inj' _ _ h := (supportEquiv S).injective (Subtype.ext h)

theorem position_mem (S : Support M m) (j : Fin m) : position S j ∈ S.val :=
  (supportEquiv S j).property

/-- The columns located at unread positions of the pool. -/
noncomputable def unreadColumns (D : Finset (Fin M)) (S : Support M m) : Finset (Fin m) :=
  Finset.univ.filter (fun j => position S j ∈ D)

@[simp] theorem mem_unreadColumns (D : Finset (Fin M)) (S : Support M m) (j : Fin m) :
    j ∈ unreadColumns D S ↔ position S j ∈ D := by
  simp [unreadColumns]

theorem map_unreadColumns (D : Finset (Fin M)) (S : Support M m) :
    (unreadColumns D S).map (position S) = S.val ∩ D := by
  ext a
  constructor
  · intro ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp ha
    exact Finset.mem_inter.mpr ⟨position_mem S j, (mem_unreadColumns D S j).mp hj⟩
  · intro ha
    obtain ⟨hS, hD⟩ := Finset.mem_inter.mp ha
    let j := (supportEquiv S).symm ⟨a, hS⟩
    have hj : position S j = a := by
      exact congrArg Subtype.val ((supportEquiv S).apply_symm_apply ⟨a, hS⟩)
    exact Finset.mem_map.mpr ⟨j, (mem_unreadColumns D S j).mpr (hj ▸ hD), hj⟩

/-- The unread-column count is exactly the support intersection size. -/
@[simp] theorem card_unreadColumns (D : Finset (Fin M)) (S : Support M m) :
    (unreadColumns D S).card = (S.val ∩ D).card := by
  rw [← map_unreadColumns D S, Finset.card_map]

/-- Rank failure of the candidate's matrix on the unread pool positions. -/
def BadRank (D : Finset (Fin M)) (c : Candidate M m r) : Prop :=
  ¬ Function.Surjective (restrictedMap c.2.val (unreadColumns D c.1) (K := ZMod 2))

theorem candidate_nonempty (hmM : m ≤ M) (hrm : r + 1 ≤ m) :
    Nonempty (Candidate M m r) := by
  have : Nonempty (Support M m) := support_nonempty hmM
  have : Nonempty (FullRankMatrix (Fin m) r) :=
    nonempty_fullRankMatrix_of_card (by simpa using hrm)
  infer_instance

/-- Every pool position has exactly the inclusion probability `m/M`. -/
theorem probability_contains (hm1 : 1 ≤ m) (hmM : m ≤ M) (hrm : r + 1 ≤ m)
    (a : Fin M) :
    probability {c : Candidate M m r | a ∈ c.1.val} = (m : ℝ) / M := by
  classical
  have : Nonempty (FullRankMatrix (Fin m) r) :=
    nonempty_fullRankMatrix_of_card (by simpa using hrm)
  rw [probability_prod_fiber]
  calc
    _ = average (inclusion (m := m) a) := by
      apply average_congr
      intro S
      by_cases h : a ∈ S.val <;> simp [h, inclusion]
    _ = _ := average_inclusion hm1 hmM a

/-- On supports with at least `2r` unread positions, the conditional matrix
rank-failure probability is at most `2 * 2^(-r)`. -/
theorem probability_badRank_fiber_le (D : Finset (Fin M)) (S : Support M m)
    (hrm : r + 1 ≤ m) (hS : 2 * r ≤ (S.val ∩ D).card) :
    probability {B : FullRankMatrix (Fin m) r | BadRank D (S, B)} ≤
      2 * (1 / 2 : ℝ) ^ r := by
  exact full_rank_restricted_failure_probability_le_pow_of_card (unreadColumns D S)
    (by simpa using hrm) (by simpa using hS)

/-- The rank-failure probability of the actual sparse candidate experiment.
The two terms account for a support with fewer than `2r` unread positions and
for rank failure of the full-rank-conditioned matrix on the remaining supports. -/
theorem probability_badRank_le (hm2 : 2 ≤ m) (hmM : m ≤ M) (hrm : r + 1 ≤ m)
    (D : Finset (Fin M)) (τ : ℝ) (hτ : 0 < τ)
    (hD : τ * M ≤ (D.card : ℝ)) (hr : 4 * (r : ℝ) ≤ τ * m) :
    probability {c : Candidate M m r | BadRank D c} ≤
      4 / (τ * m) + 2 * (1 / 2 : ℝ) ^ r := by
  classical
  have : Nonempty (Support M m) := support_nonempty hmM
  have : Nonempty (FullRankMatrix (Fin m) r) :=
    nonempty_fullRankMatrix_of_card (by simpa using hrm)
  have hq : 0 ≤ 2 * (1 / 2 : ℝ) ^ r := by positivity
  rw [probability_prod_fiber]
  calc
    _ ≤ average (fun S : Support M m =>
        (if (S.val ∩ D).card < 2 * r then (1 : ℝ) else 0) +
          2 * (1 / 2 : ℝ) ^ r) := by
      apply average_mono
      intro S
      change probability {B : FullRankMatrix (Fin m) r | BadRank D (S, B)} ≤ _
      by_cases hS : (S.val ∩ D).card < 2 * r
      · simpa only [ite_eq_left hS] using
          (probability_le_one {B : FullRankMatrix (Fin m) r | BadRank D (S, B)}).trans
            (le_add_of_nonneg_right hq)
      · simpa only [ite_eq_right hS, zero_add] using
          probability_badRank_fiber_le D S hrm (by omega)
    _ = probability {S : Support M m | (S.val ∩ D).card < 2 * r} +
        2 * (1 / 2 : ℝ) ^ r := by
      rw [average_add, average_const]
      congr 1
      unfold probability
      apply average_congr
      intro S
      by_cases hS : (S.val ∩ D).card < 2 * r <;> simp [hS]
    _ ≤ _ := add_le_add
      (probability_small_intersection_le_density hm2 hmM D r τ hτ hD hr) le_rfl

end Klr.SparseCandidate
