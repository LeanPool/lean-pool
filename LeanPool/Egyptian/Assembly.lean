/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# Passing from compatible unit tails to Theorem 1

The last paragraph of the proof of Theorem 1 expresses the value of the best
extension as the sum of two attained maxima. Its two inputs here are the
unit-fraction extremal lemma and the existence of a common optimizing prefix
with an optimizing unit tail. No general principle interchanging maxima and
addition is needed.
-/

@[expose] public section

namespace Egyptian

/-- Successive greedy denominators of a unit remainder, written with the
paper's recurrence. This representation recurses on the number of terms. -/
def unitDigits (T : ℕ) : ℕ → List ℕ
  | 0 => []
  | m + 1 => (T + 1) :: unitDigits (T * (T + 1)) m

theorem digits_eq_prefix (T m : ℕ) :
    unitDigits T m = prefixTuple (fun i => unitIter T i + 1) m := by
  induction m generalizing T with
  | zero => rfl
  | succ m ih =>
    simp only [unitDigits, ih, prefixTuple, List.range_succ_eq_map, List.map_cons,
      List.map_map, Function.comp_def, unitIter_step_start, unitIter]

theorem unit_sub_unit_succ {T : ℕ} (hT : 1 ≤ T) :
    unit T - unit (T + 1) = unit (T * (T + 1)) := by
  have hpos : (0 : ℚ) < T := by exact_mod_cast (show 0 < T by omega)
  simp only [unit, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  field_simp
  ring

theorem greedyDen_unit {T : ℕ} (hT : 1 ≤ T) : greedyDen (unit T) = T + 1 := by
  simp [greedyDen, unit, max_eq_right (show 2 ≤ T + 1 by omega)]

private theorem greedyFrom_unit (σ : Convention) (m : ℕ) :
    ∀ {T lo : ℕ}, 1 ≤ T → lo ≤ T + 1 →
      greedyFrom σ (unit T) lo m = unitDigits T m := by
  induction m with
  | zero => intros; rfl
  | succ m ih =>
    intro T lo hT hlo
    simp only [greedyFrom, unitDigits, greedyDen_unit hT, max_eq_right hlo,
      unit_sub_unit_succ hT, List.cons.injEq, true_and]
    have hgrow : T + 1 ≤ T * (T + 1) := Nat.le_mul_of_pos_left _ (by omega)
    apply ih
    · omega
    · cases σ <;> dsimp <;> omega

theorem greedyTuple_unit (σ : Convention) {T : ℕ} (hT : 1 ≤ T) (m : ℕ) :
    greedyTuple σ (unit T) m = unitDigits T m :=
  greedyFrom_unit σ m hT (by omega)

theorem IsBest.eq_bestValue {σ : Convention} {q : ℚ} {n : ℕ} {ds : List ℕ}
    (h : IsBest σ q n ds) : recipSum ds = bestValue σ q n := by
  classical
  have hExists : ∃ es, IsBest σ q n es := ⟨ds, h⟩
  rw [bestValue, dite_eq_left hExists]
  exact le_antisymm (hExists.choose_spec.2 ds h.1) (h.2 _ hExists.choose_spec.1)

@[simp] theorem recipSum_append (ds es : List ℕ) :
    recipSum (ds ++ es) = recipSum ds + recipSum es := by
  simp [recipSum]

/-- The common prefix and its legal maximizing extensions supplied by the
Bellman argument after discarding enough initial tail steps in the strict case. -/
def CompatibleUnitTails : Prop :=
  ∀ (σ : Convention) (q : ℚ), 0 < q →
    ∃ (N T : ℕ) (p : List ℕ), 1 ≤ N ∧ 1 ≤ T ∧
      q = recipSum p + unit T ∧ IsBest σ q N p ∧
      ∀ m, 1 ≤ m → IsBest σ q (N + m) (p ++ greedyTuple σ (unit T) m)

/-- Unit-fraction extremality and uniqueness, in the paper's two conventions. -/
def UniqueUnitTails : Prop :=
  ∀ (σ : Convention) (T m : ℕ), 1 ≤ T → 1 ≤ m →
    IsBest σ (unit T) m (greedyTuple σ (unit T) m) ∧
      ∀ ds, IsBest σ (unit T) m ds → ds = greedyTuple σ (unit T) m

/-- A compatible maximizing prefix and a unique maximizing unit tail give
an attained additive optimum at every extension length. -/
theorem optimal_unit_extensions (hUnique : UniqueUnitTails)
    {σ : Convention} {q : ℚ} {N T : ℕ} {p : List ℕ} (hT : 1 ≤ T)
    (hsplit : q = recipSum p + unit T) (hp : IsBest σ q N p)
    (hext : ∀ m, 1 ≤ m → IsBest σ q (N + m) (p ++ greedyTuple σ (unit T) m)) :
    ∀ m : ℕ, 1 ≤ m →
      let u := q - bestValue σ q N
      let g := greedyTuple σ u m
      bestValue σ q (N + m) = bestValue σ q N + bestValue σ u m ∧
      IsBest σ u m g ∧
      (∀ ds, IsBest σ u m ds → ds = g) ∧
      IsBest σ q (N + m) (p ++ g) := by
  intro m hm
  dsimp only
  have hu : q - bestValue σ q N = unit T := by
    rw [← hp.eq_bestValue, hsplit]
    abel
  rw [hu]
  obtain ⟨hg, honly⟩ := hUnique σ T m hT hm
  have hpg := hext m hm
  refine ⟨?_, hg, honly, hpg⟩
  rw [← hpg.eq_bestValue, ← hp.eq_bestValue, ← hg.eq_bestValue, recipSum_append]

theorem eventuallyGreedy_of_unitTails
    (hCompatible : CompatibleUnitTails) (hUnique : UniqueUnitTails) :
    EventuallyGreedy := by
  intro σ q hq
  obtain ⟨N, T, p, hN, hT, hsplit, hp, hext⟩ := hCompatible σ q hq
  exact ⟨N, p, hN, hp, optimal_unit_extensions hUnique hT hsplit hp hext⟩

/-- The sum of reciprocals over the first n places, coerced into the reals. -/
theorem real_prefix_sum (a : ℕ → ℕ) (n : ℕ) :
    (recipSum (prefixTuple a n) : ℝ) = ∑ i ∈ Finset.range n, 1 / (a i : ℝ) := by
  induction n with
  | zero => simp [recipSum, prefixTuple]
  | succ n ih =>
    simpa [prefixTuple, recipSum, List.range_succ, unit, Finset.sum_range_succ]
      using congrArg (fun x : ℝ => x + 1 / (a n : ℝ)) ih

end Egyptian
