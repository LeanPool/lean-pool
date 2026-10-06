/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section57.MinimalScaleTail
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# High-contrast homogenization: Provider.Quenched.MinimalScaleMeasurability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Measurability of the abstract quenched minimal scale

The abstract Chapter 5 stopping construction supplies the first generation after
which no bad event occurs, but its public API does not record measurability.  This
file proves measurability directly from measurability of the individual bad
events.  No additional stopping-scale definition is introduced.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

open Book.Ch05.Section57

/-- The event that every bad event from a fixed generation onward is absent is
measurable when every individual bad event is measurable. -/
theorem measurableSet_goodTailFrom {Bad : ℕ → Set Ω}
    (hBad : ∀ n, MeasurableSet (Bad n)) (m : ℕ) :
    MeasurableSet {ω | goodTailFrom Bad m ω} := by
  rw [show {ω | goodTailFrom Bad m ω} =
      ⋂ n : ℕ, if m ≤ n then (Bad n)ᶜ else Set.univ by
    ext ω
    simp [goodTailFrom]]
  exact MeasurableSet.iInter fun n => by
    split_ifs
    · exact (hBad n).compl
    · exact MeasurableSet.univ

/-- The event that some generation starts an all-good tail is measurable when
every individual bad event is measurable. -/
theorem measurableSet_hasGoodTailFrom {Bad : ℕ → Set Ω}
    (hBad : ∀ n, MeasurableSet (Bad n)) (n₀ : ℕ) :
    MeasurableSet {ω | hasGoodTailFrom n₀ Bad ω} := by
  rw [show {ω | hasGoodTailFrom n₀ Bad ω} =
      ⋃ m : ℕ, if n₀ ≤ m then {ω | goodTailFrom Bad m ω} else ∅ by
    ext ω
    simp [hasGoodTailFrom]]
  exact MeasurableSet.iUnion fun m => by
    split_ifs
    · exact measurableSet_goodTailFrom hBad m
    · exact MeasurableSet.empty

/-- The abstract quenched minimal-scale index is measurable when its bad events
are measurable. -/
theorem measurable_quenchedMinimalScaleIndex {Bad : ℕ → Set Ω}
    (hBad : ∀ n, MeasurableSet (Bad n)) (n₀ : ℕ) :
    Measurable (quenchedMinimalScaleIndex n₀ Bad) := by
  classical
  let p : Ω → ℕ → Prop := fun ω m =>
    (n₀ ≤ m ∧ goodTailFrom Bad m ω) ∨
      (m = n₀ ∧ ¬ hasGoodTailFrom n₀ Bad ω)
  have hp : ∀ ω, ∃ m, p ω m := by
    intro ω
    by_cases hgood : hasGoodTailFrom n₀ Bad ω
    · obtain ⟨m, hn₀m, hm⟩ := hgood
      exact ⟨m, Or.inl ⟨hn₀m, hm⟩⟩
    · exact ⟨n₀, Or.inr ⟨rfl, hgood⟩⟩
  have hp_measurable : ∀ m, MeasurableSet {ω | p ω m} := by
    intro m
    rw [show {ω | p ω m} =
        (if n₀ ≤ m then {ω | goodTailFrom Bad m ω} else ∅) ∪
          (if m = n₀ then {ω | ¬ hasGoodTailFrom n₀ Bad ω} else ∅) by
      ext ω
      simp [p]]
    apply MeasurableSet.union
    · split_ifs
      · exact measurableSet_goodTailFrom hBad m
      · exact MeasurableSet.empty
    · split_ifs
      · exact (measurableSet_hasGoodTailFrom hBad n₀).compl
      · exact MeasurableSet.empty
  have hfind : Measurable fun ω => Nat.find (hp ω) :=
    measurable_find hp hp_measurable
  have hindex :
      (fun ω => quenchedMinimalScaleIndex n₀ Bad ω) =
        fun ω => Nat.find (hp ω) := by
    funext ω
    by_cases hgood : hasGoodTailFrom n₀ Bad ω
    · have hleft : Nat.find hgood ≤ Nat.find (hp ω) := by
        apply Nat.find_min' hgood
        have hspec := Nat.find_spec (hp ω)
        rcases hspec with hspec | hspec
        · exact hspec
        · exact False.elim (hspec.2 hgood)
      have hright : Nat.find (hp ω) ≤ Nat.find hgood := by
        apply Nat.find_min' (hp ω)
        exact Or.inl (Nat.find_spec hgood)
      simpa [quenchedMinimalScaleIndex, hgood] using le_antisymm hleft hright
    · have hspec := Nat.find_spec (hp ω)
      have hfind_eq : Nat.find (hp ω) = n₀ := by
        rcases hspec with hspec | hspec
        · exact False.elim (hgood ⟨Nat.find (hp ω), hspec⟩)
        · exact hspec.1
      simp [quenchedMinimalScaleIndex, hgood, hfind_eq]
  change Measurable (fun ω => quenchedMinimalScaleIndex n₀ Bad ω)
  rw [hindex]
  exact hfind

/-- The abstract triadic quenched minimal scale is measurable when its bad
events are measurable. -/
theorem measurable_quenchedMinimalScale {Bad : ℕ → Set Ω}
    (hBad : ∀ n, MeasurableSet (Bad n)) (n₀ : ℕ) :
    Measurable (quenchedMinimalScale n₀ Bad) := by
  rw [show quenchedMinimalScale n₀ Bad =
      fun ω => (3 : ℝ) ^ quenchedMinimalScaleIndex n₀ Bad ω by
    rfl]
  exact Measurable.const_pow (measurable_quenchedMinimalScaleIndex hBad n₀) 3

end

end Quenched
end HighContrast
end HCPolySupport
