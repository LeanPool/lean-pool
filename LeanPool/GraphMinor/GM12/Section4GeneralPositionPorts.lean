/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4CirclePortIntervals
public import LeanPool.GraphMinor.GM12.Section4ChordFamily

/-!
# Ordered ports with chords in general position

For XII (4.5), page 253, prescribe the order of all edge ends
around the circle and an open neighborhood for each vertex block.
Choose disjoint ordered port intervals in these neighborhoods,
then choose the chords inside their intervals. The port order is
retained, the supporting lines are distinct, and no three of them
meet.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Choose all ports of a finite chord family in their assigned
order and neighborhoods, with no triple intersections of supporting
lines. This combines the order and perturbation choices for the
source crossing drawing in XII (4.5), page 253. -/
theorem exists_ordered_general_position_ports {n : ℕ}
    (ρ : (Fin n × Bool) ≃ Fin (2 * n))
    (c : Fin (2 * n) → ℝ) (hc : Monotone c) (hc01 : ∀ i, c i ∈ Ioo 0 1)
    (O : Fin (2 * n) → Set ℂ) (hO : ∀ i, IsOpen (O i))
    (hcO : ∀ i, (ee (c i) : ℂ) ∈ O i) :
    ∃ p : Fin n × Bool → ℝ,
      (∀ x, p x ∈ Ioo 0 1 ∧ (ee (p x) : ℂ) ∈ O (ρ x)) ∧
      (∀ x y, ρ x < ρ y → p x < p y) ∧
      Function.Injective (fun x => (ee (p x) : ℂ)) ∧
      (∀ i j, i ≠ j →
        line[ℝ, (ee (p (i, false)) : ℂ), (ee (p (i, true)) : ℂ)] ≠
        line[ℝ, (ee (p (j, false)) : ℂ), (ee (p (j, true)) : ℂ)]) ∧
      ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ∀ x : ℂ,
        ¬ (x ∈ line[ℝ, (ee (p (i, false)) : ℂ), (ee (p (i, true)) : ℂ)] ∧
          x ∈ line[ℝ, (ee (p (j, false)) : ℂ), (ee (p (j, true)) : ℂ)] ∧
          x ∈ line[ℝ, (ee (p (k, false)) : ℂ), (ee (p (k, true)) : ℂ)]) := by
  obtain ⟨u, v, huv, horder⟩ := exists_ordered_circle_port_intervals c hc hc01 O hO hcO
  obtain ⟨s, t, hst, hne, hthree⟩ := exists_chord_family_in_arcs n
    (fun i => u (ρ (i, false))) (fun i => v (ρ (i, false)))
    (fun i => u (ρ (i, true))) (fun i => v (ρ (i, true)))
    (fun i => (huv _).2.1) (fun i => by linarith [(huv (ρ (i, false))).1, (huv (ρ
      (i, false))).2.2.1])
    (fun i => (huv _).2.1) (fun i => by linarith [(huv (ρ (i, true))).1, (huv (ρ (i, true))).2.2.1])
  let p : Fin n × Bool → ℝ := fun x => if x.2 then t x.1 else s x.1
  have hpinterval : ∀ x, p x ∈ Ioo (u (ρ x)) (v (ρ x)) := by
    rintro ⟨i, b⟩
    cases b
    · exact (hst i).1
    · exact (hst i).2.1
  have hp01 : ∀ x, p x ∈ Ioo (0 : ℝ) 1 := fun x =>
    ⟨lt_of_le_of_lt (huv _).1 (hpinterval x).1,
      lt_of_lt_of_le (hpinterval x).2 (huv _).2.2.1⟩
  have hporder : ∀ x y, ρ x < ρ y → p x < p y := fun x y hxy =>
    (hpinterval x).2.trans ((horder _ _ hxy).trans (hpinterval y).1)
  refine ⟨p, ?_, hporder, ?_, ?_, ?_⟩
  · intro x
    have hi := hpinterval x
    exact ⟨hp01 x, (huv _).2.2.2 _ hi⟩
  · intro x y hxy
    have hparam : p x = p y := ee_injOn_short_interval (by norm_num : (1 : ℝ) ≤ 0 + 1)
      (hp01 x) (hp01 y) (Subtype.ext hxy)
    apply ρ.injective
    rcases lt_trichotomy (ρ x) (ρ y) with h | h | h
    · exact False.elim ((hporder x y h).ne hparam)
    · exact h
    · exact False.elim ((hporder y x h).ne hparam.symm)
  · simpa only [p, Bool.false_eq_true, ↓reduceIte] using hne
  · simpa only [p, Bool.false_eq_true, ↓reduceIte] using hthree

end GraphMinor.GM12
