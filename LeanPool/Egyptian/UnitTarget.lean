/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.UnitBest

/-!
# Theorem 1 at a unit-fraction target

The first paragraph of the proof of Theorem 1 takes the prefix (T+1).
The split comes from the identity 1/T − 1/(T+1) = 1/(T(T+1)).
-/

public section

namespace Egyptian

theorem unit_first_prefix (σ : Convention) (T : ℕ) (hT : 1 ≤ T) :
    unit T = recipSum [T + 1] + unit (T * (T + 1)) ∧
      IsBest σ (unit T) 1 [T + 1] ∧
      ∀ m,
        IsBest σ (unit T) (1 + m) ([T + 1] ++ greedyTuple σ (unit (T * (T + 1))) m) := by
  have oneStep : greedyTuple σ (unit T) 1 = [T + 1] := greedyTuple_unit σ hT 1
  have hp := (uniqueUnitTails σ T 1 hT).1
  rw [oneStep] at hp
  have hT' : 1 ≤ T * (T + 1) := Nat.mul_pos (by omega) (by omega)
  have hsplit : unit T = recipSum [T + 1] + unit (T * (T + 1)) := by
    have h := unit_sub_unit_succ hT
    simp only [recipSum, List.map_singleton, List.sum_singleton]
    linarith
  refine ⟨hsplit, hp, ?_⟩
  intro m
  have hext := (uniqueUnitTails σ T (1 + m) hT).1
  have htuple : greedyTuple σ (unit T) (1 + m) =
      [T + 1] ++ greedyTuple σ (unit (T * (T + 1))) m := by
    rw [show 1 + m = m + 1 by omega, greedyTuple_unit σ hT, greedyTuple_unit σ hT']
    rfl
  rwa [htuple] at hext

theorem unitTarget
    (σ : Convention) (T : ℕ) (hT : 1 ≤ T) :
    IsBest σ (unit T) 1 [T + 1] ∧
      ∀ m : ℕ, 1 ≤ m →
        let u := unit T - bestValue σ (unit T) 1
        let g := greedyTuple σ u m
        bestValue σ (unit T) (1 + m) = bestValue σ (unit T) 1 + bestValue σ u m ∧
        IsBest σ u m g ∧
        (∀ ds, IsBest σ u m ds → ds = g) ∧
        IsBest σ (unit T) (1 + m) ([T + 1] ++ g) := by
  obtain ⟨hsplit, hp, hext⟩ := unit_first_prefix σ T hT
  have hT' : 1 ≤ T * (T + 1) := Nat.mul_pos hT (Nat.succ_pos _)
  exact ⟨hp, optimal_unit_extensions uniqueUnitTails hT' hsplit hp (fun m _ => hext m)⟩

end Egyptian
