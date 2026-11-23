/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.BellmanProper
public import LeanPool.Egyptian.GlobalAttainment
public import LeanPool.Egyptian.HarmonicEntrance
public import LeanPool.Egyptian.Completion
public import LeanPool.Egyptian.UnitTarget

/-!
# Eventually greedy best underapproximations

Proof of Theorem 1 of Kovač and Tang. A maximizing Bellman terminal and
completion of competing tuples give the common prefix. If the maximizing
terminal is empty, the rational target is a unit fraction and the construction
starts with its first greedy denominator.
-/

public section

namespace Egyptian.Control

/-- At every admissible positive state, a terminal decomposition attains the
Bellman optimum, in either order convention. -/
theorem global_winner (σ : Convention) (s : State) (hv : Valid s) (hi : Interior s) :
    ∃ xs T, Wins σ s xs T := by
  by_cases hsmall : s.p ≤ s.q
  · obtain ⟨xs,T,hwin,_⟩ := proper_winner σ s hv hi hsmall
    exact ⟨xs,T,hwin⟩
  · exact (improper_winners σ s hv (Nat.lt_of_not_ge hsmall)
      (terminal_exists σ s hv hi) (proper_winner σ)).1

end Egyptian.Control

namespace Egyptian

/-- Starting at a unit fraction, take the one-term prefix in Theorem 1. -/
private theorem unit_compatible (σ : Convention) {T : ℕ} (hT : 1 ≤ T) :
    ∃ (N U : ℕ) (p : List ℕ), 1 ≤ N ∧ 1 ≤ U ∧
      unit T = recipSum p + unit U ∧ IsBest σ (unit T) N p ∧
      ∀ m, 1 ≤ m → IsBest σ (unit T) (N+m) (p ++ greedyTuple σ (unit U) m) := by
  obtain ⟨hsplit, hbest, hext⟩ := unit_first_prefix σ T hT
  exact ⟨1, T * (T + 1), [T + 1], le_rfl, Nat.mul_pos hT (Nat.succ_pos _), hsplit, hbest,
    fun m _ => hext m⟩

/-- The common maximizing prefix, with unit remainder, needed in both
Theorem 1 and the infinite benchmark of Theorem 4. -/
theorem compatibleUnitTails : CompatibleUnitTails := by
  intro σ q hq
  obtain ⟨s,hv,hz,hval⟩ := Control.exists_initial_state hq
  have hin : Control.Interior s := by
    simpa only [Control.Interior, hz, Nat.zero_mul] using hv.2
  obtain ⟨xs,T,hwin⟩ := Control.global_winner σ s hv hin
  obtain ⟨had,hstop,hsplit⟩ := Control.terminal_to_tuple hv hwin.1
  rw [hval] at had hsplit
  have hT := hwin.1.2.1
  by_cases hnil : xs = []
  · have he : q = unit T := by simpa [hnil, recipSum] using hsplit
    rw [he]
    exact unit_compatible σ (by omega)
  · have hlen : 1 ≤ xs.length := by
      exact List.length_pos_iff_ne_nil.mpr hnil
    have hc := Control.completion_bound_of_value_le hv hz hval (Control.wins_value hwin).le
    exact compatible_of_terminal_completion hlen hT had hstop hsplit hc

/-- The complete unconditional statement of Theorem 1. -/
theorem eventuallyGreedy_proof : EventuallyGreedy :=
  eventuallyGreedy_of_unitTails compatibleUnitTails uniqueUnitTails

end Egyptian
