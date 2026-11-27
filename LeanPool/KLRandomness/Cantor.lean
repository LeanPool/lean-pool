/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.NormNum

/-!
# Cantor space and fair-coin measure

Finite binary strings use `List Bool`; infinite binary sequences use `ℕ → Bool`.
The measure below is the actual infinite product of fair two-point measures.
-/

@[expose] public section

namespace Klr

open MeasureTheory
open scoped ENNReal NNReal

/-- Cantor space, with the product topology and product measurable space. -/
abbrev Cantor := ℕ → Bool

/-- The cylinder consisting of the infinite extensions of a finite binary string. -/
def cylinder (s : List Bool) : Set Cantor :=
  {X | ∀ i < s.length, X i = s.getD i false}

@[simp] theorem mem_cylinder {s : List Bool} {X : Cantor} :
    X ∈ cylinder s ↔ ∀ i < s.length, X i = s.getD i false := Iff.rfl

@[simp] theorem cylinder_nil : cylinder [] = Set.univ := by
  ext X
  simp [cylinder]

theorem cylinder_eq_pi (s : List Bool) :
    cylinder s = Set.pi (Finset.range s.length) (fun i => {s.getD i false}) := by
  ext X
  simp [cylinder, Set.pi]

theorem isOpen_cylinder (s : List Bool) : IsOpen (cylinder s) := by
  rw [cylinder_eq_pi]
  exact isOpen_set_pi (Finset.finite_toSet _) (fun _ _ => isOpen_discrete _)

theorem isClosed_cylinder (s : List Bool) : IsClosed (cylinder s) := by
  rw [cylinder_eq_pi]
  exact isClosed_set_pi (fun _ _ => isClosed_singleton)

theorem measurableSet_cylinder (s : List Bool) : MeasurableSet (cylinder s) := by
  rw [cylinder_eq_pi]
  exact MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => measurableSet_singleton _)

/-- The fair probability measure on one bit. -/
noncomputable def fairBit : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false ⟨1 / 2, by norm_num, by norm_num⟩

instance : IsProbabilityMeasure fairBit := by
  unfold fairBit
  infer_instance

@[simp] theorem fairBit_singleton (b : Bool) : fairBit {b} = (1 / 2 : ℝ≥0∞) := by
  cases b <;>
    norm_num [fairBit, ProbabilityTheory.bernoulliMeasure_apply,
      unitInterval.toNNReal, unitInterval.symm]
  all_goals
    change ((1 / 2 : ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹
    norm_num

/-- Independent fair coin tosses on all natural-number positions. -/
noncomputable def fairCoin : Measure Cantor :=
  Measure.infinitePi (fun _ : ℕ => fairBit)

instance : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance

/-- A finite specification of `|s|` bits has fair-coin measure `2⁻|s|`. -/
@[simp] theorem fairCoin_cylinder (s : List Bool) :
    fairCoin (cylinder s) = (1 / 2 : ℝ≥0∞) ^ s.length := by
  rw [cylinder_eq_pi, fairCoin, Measure.infinitePi_pi]
  · simp
  · intro i hi
    exact measurableSet_singleton _

end Klr
