/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Multiplicity normal form for D7.2 counterexample searches

This file formalizes the discrete pruning step behind the D7.2 exact-emptiness
program. It contains no geometric emptiness theorem and proves no improvement of
the ESGK bound. The point is narrower:

If a finite family of distance multiplicities has total mass `T`, pointwise cap
`B`, and energy comparable to `B*T`, then a positive fraction of the mass must
live in classes whose multiplicity is a positive fraction of `B`.

For general-position distance energy, `B` is supplied by the existing geometric
ceiling (`OrderedMultiplicity p r <= 3*n`) and `T` is the ordered off-diagonal
pair count. D7.2 is the later geometric step: exclude realizability of the
resulting heavy bounded-degree distance designs under no-three-collinear /
no-four-cocircular.
-/

@[expose] public section

namespace Esgk

open scoped BigOperators

variable {α : Type*}

/-- Total multiplicity mass over a finite index set. For distance classes this
is the total number of ordered off-diagonal pairs represented by the selected
distance values. -/
def MultiplicityMass (s : Finset α) (m : α → ℕ) : ℕ :=
  ∑ a ∈ s, m a

/-- Multiplicity energy `sum m_a^2` over a finite index set. -/
def MultiplicityEnergy (s : Finset α) (m : α → ℕ) : ℕ :=
  ∑ a ∈ s, (m a) ^ 2

/-- Classes whose multiplicity is at least the threshold `K`. -/
def HeavyMultiplicityClasses (s : Finset α) (m : α → ℕ) (K : ℕ) : Finset α :=
  s.filter (fun a ↦ K ≤ m a)

/-- Total multiplicity mass carried by the threshold-heavy classes. -/
def HeavyMultiplicityMass (s : Finset α) (m : α → ℕ) (K : ℕ) : ℕ :=
  ∑ a ∈ HeavyMultiplicityClasses s m K, m a

/-- Heavy classes carry at least `K` times their count. -/
theorem threshold_mul_heavyMultiplicityCard_le_heavyMultiplicityMass
    (s : Finset α) (m : α → ℕ) (K : ℕ) :
    K * (HeavyMultiplicityClasses s m K).card ≤ HeavyMultiplicityMass s m K := by
  classical
  unfold HeavyMultiplicityMass HeavyMultiplicityClasses
  calc K * (s.filter (fun a ↦ K ≤ m a)).card
      = ∑ _a ∈ s.filter (fun a ↦ K ≤ m a), K := by
          simp [Finset.sum_const, mul_comm]
    _ ≤ ∑ a ∈ s.filter (fun a ↦ K ≤ m a), m a := by
          refine Finset.sum_le_sum ?_
          intro a ha
          exact (Finset.mem_filter.mp ha).2

/-- A pointwise cap `m_a <= B` bounds the heavy mass by `B` times the heavy
class count. This is the bookkeeping bridge from heavy mass to `Theta(n)` many
heavy distance classes when `T/B = Theta(n)`. -/
theorem heavyMultiplicityMass_le_cap_mul_heavyMultiplicityCard
    (s : Finset α) (m : α → ℕ) (K B : ℕ)
    (hcap : ∀ a ∈ s, m a ≤ B) :
    HeavyMultiplicityMass s m K ≤ B * (HeavyMultiplicityClasses s m K).card := by
  classical
  unfold HeavyMultiplicityMass HeavyMultiplicityClasses
  calc ∑ a ∈ s.filter (fun a ↦ K ≤ m a), m a
      ≤ ∑ _a ∈ s.filter (fun a ↦ K ≤ m a), B := by
          refine Finset.sum_le_sum ?_
          intro a ha
          exact hcap a (Finset.mem_of_mem_filter a ha)
    _ = B * (s.filter (fun a ↦ K ≤ m a)).card := by
          simp [Finset.sum_const, mul_comm]

/-- The basic pruning inequality. Light classes contribute at most `K*T`;
heavy classes contribute at most `B` times their heavy mass. Hence any energy
above the light term must come from the heavy band. -/
theorem multiplicityEnergy_le_threshold_mul_mass_add_cap_mul_heavyMass
    (s : Finset α) (m : α → ℕ) (K B : ℕ)
    (hcap : ∀ a ∈ s, m a ≤ B) :
    MultiplicityEnergy s m ≤
      K * MultiplicityMass s m + B * HeavyMultiplicityMass s m K := by
  classical
  unfold MultiplicityEnergy MultiplicityMass HeavyMultiplicityMass HeavyMultiplicityClasses
  calc
    ∑ a ∈ s, (m a) ^ 2
        ≤ ∑ a ∈ s, (K * m a + B * (if K ≤ m a then m a else 0)) := by
          refine Finset.sum_le_sum ?_
          intro a ha
          by_cases hheavy : K ≤ m a
          · have hsquare : (m a) ^ 2 ≤ B * m a := by
              calc (m a) ^ 2 = m a * m a := by ring
                _ ≤ B * m a := Nat.mul_le_mul_right (m a) (hcap a ha)
            calc (m a) ^ 2 ≤ B * m a := hsquare
              _ ≤ K * m a + B * m a := Nat.le_add_left _ _
              _ = K * m a + B * (if K ≤ m a then m a else 0) := by simp [hheavy]
          · have hleK : m a ≤ K := Nat.le_of_lt (Nat.lt_of_not_ge hheavy)
            have hsquare : (m a) ^ 2 ≤ K * m a := by
              calc (m a) ^ 2 = m a * m a := by ring
                _ ≤ K * m a := Nat.mul_le_mul_right (m a) hleK
            calc (m a) ^ 2 ≤ K * m a := hsquare
              _ ≤ K * m a + B * (if K ≤ m a then m a else 0) := Nat.le_add_right _ _
    _ = K * ∑ a ∈ s, m a + B * ∑ a ∈ s, (if K ≤ m a then m a else 0) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ = K * ∑ a ∈ s, m a +
        B * ∑ a ∈ s.filter (fun a ↦ K ≤ m a), m a := by
          congr 2
          rw [Finset.sum_filter]

/-- Nontrivial energy above the light contribution forces a nonempty heavy band. -/
theorem heavyMultiplicityMass_pos_of_threshold_mul_mass_lt_energy
    (s : Finset α) (m : α → ℕ) (K B : ℕ)
    (hcap : ∀ a ∈ s, m a ≤ B)
    (henergy : K * MultiplicityMass s m < MultiplicityEnergy s m) :
    0 < HeavyMultiplicityMass s m K := by
  by_contra hnot
  have hzero : HeavyMultiplicityMass s m K = 0 := Nat.eq_zero_of_not_pos hnot
  have hmain := multiplicityEnergy_le_threshold_mul_mass_add_cap_mul_heavyMass s m K B hcap
  rw [hzero, mul_zero, add_zero] at hmain
  exact (not_le_of_gt henergy) hmain

/-- Real-valued normal form. If `E >= eta * B * T` and the heavy threshold
`K` is at most `(eta/2) * B`, then the `K`-heavy classes carry at least
`(eta/2) * T` total mass.

This is the formal version of the Branch-A pruning slogan: cubic energy under a
linear multiplicity cap forces a positive fraction of all pairs into
linear-multiplicity distance classes. -/
theorem heavyMultiplicityMass_lower_bound_real
    (s : Finset α) (m : α → ℕ) (K B : ℕ) {eta : ℝ}
    (hcap : ∀ a ∈ s, m a ≤ B)
    (hBpos : 0 < (B : ℝ))
    (henergy : eta * (B : ℝ) * (MultiplicityMass s m : ℝ) ≤
      (MultiplicityEnergy s m : ℝ))
    (hK : (K : ℝ) ≤ eta / 2 * (B : ℝ)) :
    eta / 2 * (MultiplicityMass s m : ℝ) ≤
      (HeavyMultiplicityMass s m K : ℝ) := by
  have hmain_nat :=
    multiplicityEnergy_le_threshold_mul_mass_add_cap_mul_heavyMass s m K B hcap
  have hmain : (MultiplicityEnergy s m : ℝ) ≤
      (K : ℝ) * (MultiplicityMass s m : ℝ) +
        (B : ℝ) * (HeavyMultiplicityMass s m K : ℝ) := by
    exact_mod_cast hmain_nat
  have hKT : (K : ℝ) * (MultiplicityMass s m : ℝ) ≤
      (eta / 2 * (B : ℝ)) * (MultiplicityMass s m : ℝ) := by
    exact mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg _)
  nlinarith

end Esgk
