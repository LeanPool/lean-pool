/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Bellman
public import LeanPool.Egyptian.Payoff
import Mathlib.Tactic.Positivity.Finset

/-! The greedy Bellman drift and the strict lower bound above the stopping
obstacle at nonunit states, as in §3.2 of Kovač and Tang. -/

@[expose] public section

namespace Egyptian.Control

/-- The reciprocal of the remainder represented by a Bellman state. -/
noncomputable def inverseRemainder (s : State) : ℝ := s.q / (s.p : ℝ)

theorem one_le_inverse {s : State} (hv : Valid s) (hsmall : s.p ≤ s.q) :
    1 ≤ inverseRemainder s := by
  have hp : (0 : ℝ) < s.p := by exact_mod_cast hv.1
  apply (one_le_div hp).2
  exact_mod_cast hsmall

/-- The reciprocal recurrence gains exactly (p/p')t² over the old reciprocal. -/
theorem step_inverse {σ s x} (hv : Valid s) (hx : Legal σ s x) :
    inverseRemainder (step s x) = inverseRemainder s +
      ((s.p : ℝ) / (step s x).p) * (inverseRemainder s)^2 := by
  have hs : s.q ≤ s.p * x := hx.1.le
  have hpos : (0 : ℝ) < s.p := by exact_mod_cast hv.1
  have hd : (0 : ℝ) < (step s x).p := by exact_mod_cast (step_valid hv hx).1
  have hnum : ((step s x).p : ℝ) + s.q = s.p * x := by
    exact_mod_cast Nat.sub_add_cancel hs
  have hden : ((step s x).q : ℝ) = s.q * x := by simp [step]
  unfold inverseRemainder
  rw [hden]
  field_simp [hpos.ne', hd.ne']
  nlinarith [congrArg (fun v : ℝ => v * s.q) hnum]

theorem first_step_drift {σ s x} (hv : Valid s) (hsmall : s.p ≤ s.q)
    (hx : Legal σ s x) (hdrop : (step s x).p < s.p) :
    2 * Payoff.value (inverseRemainder s) < Payoff.value (inverseRemainder (step s x)) := by
  have ht := one_le_inverse hv hsmall
  have hp' : (0 : ℝ) < (step s x).p := by exact_mod_cast (step_valid hv hx).1
  have hratio : (1 : ℝ) < (s.p : ℝ) / (step s x).p :=
    (one_lt_div hp').2 (by exact_mod_cast hdrop)
  have hr : Payoff.phi (inverseRemainder s) < inverseRemainder (step s x) := by
    rw [step_inverse hv hx]
    unfold Payoff.phi
    nlinarith [mul_lt_mul_of_pos_right hratio
      (sq_pos_of_pos (show 0 < inverseRemainder s by linarith))]
  rw [← Payoff.value_phi ht]
  exact Payoff.value_strictMonoOn (Payoff.one_le_phi ht) ((Payoff.one_le_phi ht).trans hr.le) hr

private theorem inverse_of_stop {s : State} {T : ℕ} (hv : Valid s)
    (h : s.q = s.p * T) : inverseRemainder s = T := by
  have hp : (s.p : ℝ) ≠ 0 := by exact_mod_cast hv.1.ne'
  simp [inverseRemainder, h, Nat.cast_mul, hp]

/-- A unit state admits a terminal continuation of exactly its initial payoff.
When T=1 the legal string [2,3] is used in place of an illegal immediate stop. -/
theorem unit_reward (σ : Convention) {s : State} (hv : Valid s) (hi : Interior s)
    (hd : s.p ∣ s.q) :
    ∃ xs T, Terminal σ s xs T ∧
      (1/2 : ℝ)^xs.length * Payoff.value T = Payoff.value (inverseRemainder s) := by
  obtain ⟨T,hT⟩ := hd
  have hi' : s.last < T := by
    unfold Interior at hi
    rw [hT, Nat.mul_comm s.p] at hi
    exact Nat.lt_of_mul_lt_mul_right hi
  rw [inverse_of_stop hv hT]
  by_cases htwo : 2 ≤ T
  · exact ⟨[], T, ⟨trivial, htwo, hi', hT⟩, by simp⟩
  · have hone : T = 1 := by omega
    subst T
    have hz : s.last = 0 := by omega
    have he : s.q = s.p := by simpa using hT
    have ha : σ.rel 0 2 := by cases σ <;> norm_num [Convention.rel]
    have hb : σ.rel 2 3 := by cases σ <;> norm_num [Convention.rel]
    refine ⟨[2,3],6, ?_, ?_⟩
    · simp only [Terminal, Controls, Legal, finish, step, CanStop, he, hz]
      have hp := hv.1
      exact ⟨⟨⟨by omega, by decide, ha⟩, ⟨by omega, by decide, hb⟩, trivial⟩,
        by decide, by decide, by omega⟩
    · have h1 := Payoff.value_phi (t := 1) (by norm_num)
      have h2 := Payoff.value_phi (t := 2) (by norm_num)
      norm_num [Payoff.phi] at h1 h2 ⊢
      linarith

/-- The finite greedy continuation reaches a legal terminal state with at
least the initial payoff. A nonunit initial remainder gives strict growth. -/
theorem greedy_reward (σ : Convention) (s : State) (hv : Valid s)
    (hi : Interior s) (hsmall : s.p ≤ s.q) :
    ∃ xs T, Terminal σ s xs T ∧
      Payoff.value (inverseRemainder s) ≤ (1/2 : ℝ)^xs.length * Payoff.value T ∧
      (¬s.p ∣ s.q → Payoff.value (inverseRemainder s) <
        (1/2 : ℝ)^xs.length * Payoff.value T) := by
  by_cases hd : s.p ∣ s.q
  · obtain ⟨xs,T,ht,he⟩ := unit_reward σ hv hi hd
    exact ⟨xs,T,ht,he.ge,fun hn => (hn hd).elim⟩
  · let x := s.q / s.p + 1
    obtain ⟨hl, hdrop, hi', hs'⟩ := greedy_step hv hi hsmall hd σ
    obtain ⟨xs,T,ht,hb,_⟩ :=
      greedy_reward σ (step s x) (step_valid hv hl) hi' hs'
    have hgain := first_step_drift hv hsmall hl hdrop
    have hstrict : Payoff.value (inverseRemainder s) <
        (1/2 : ℝ)^(x :: xs).length * Payoff.value T := by
      simp only [List.length_cons, pow_succ]
      linarith
    exact ⟨x::xs,T,⟨⟨hl,ht.1⟩,ht.2⟩,hstrict.le,fun _ => hstrict⟩
termination_by s.p

theorem strict_obstacle (σ : Convention) (s : State) (hv : Valid s)
    (hi : Interior s) (hsmall : s.p ≤ s.q) (hd : ¬s.p ∣ s.q) :
    (Payoff.value (inverseRemainder s) : EReal) <
      value σ (fun T => Payoff.value T) s := by
  obtain ⟨xs,T,ht,_,hstrict⟩ := greedy_reward σ s hv hi hsmall
  exact (EReal.coe_lt_coe_iff.2 (hstrict hd)).trans_le
    (reward_le_value (H := fun T => Payoff.value T) ht)

end Egyptian.Control
