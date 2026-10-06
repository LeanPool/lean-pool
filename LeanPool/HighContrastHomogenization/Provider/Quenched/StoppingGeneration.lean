/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.MinimalScaleMeasurability

/-!
# High-contrast homogenization: Provider.Quenched.StoppingGeneration

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The generation map of a family of quenched stopping radii

The annealed-to-quenched endgame replaces a family of stopping radii by the
number of generations one has to step back from an outer generation before a
stopping radius already fits inside the cube of that generation, with a fallback
index when no replay succeeds.  This file fixes that generation map together
with its fallback value and proves the two facts the
quantitative estimate needs: below the generation map every admissible offset
overshoots, and the event that the generation map is large is either contained
in a single overshoot event or empty.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

attribute [local instance] Classical.propDecidable

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A candidate offset for the generation map: the offset does not step below
the base generation, and the stopping radius at the stepped-back generation
already fits inside the cube of the outer generation. -/
@[expose]
def IsStoppingCandidate (nstar : ℕ) (R : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) (q : ℕ) :
    Prop :=
  q ≤ m - nstar ∧ R (m - q) ω ≤ (3 : ℝ) ^ m

/-- The generation map `N(m)`: the least candidate offset when one exists, and
the fallback offset `m - n_* + q_fb` otherwise. -/
@[expose]
def stoppingGeneration (nstar qfb : ℕ) (R : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) : ℕ :=
  if h : ∃ q, IsStoppingCandidate nstar R m ω q then Nat.find h else m - nstar + qfb

omit [MeasurableSpace Ω] in
/-- The generation map never exceeds its fallback value. -/
theorem stoppingGeneration_le (nstar qfb : ℕ) (R : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) :
    stoppingGeneration nstar qfb R m ω ≤ m - nstar + qfb := by
  unfold stoppingGeneration
  split
  · next h => exact le_trans (Nat.find_spec h).1 (Nat.le_add_right _ _)
  · exact le_rfl

omit [MeasurableSpace Ω] in
/-- Every admissible offset strictly below the generation map overshoots the
cube of the outer generation. -/
theorem lt_of_lt_stoppingGeneration {nstar qfb : ℕ} {R : ℕ → Ω → ℝ} {m : ℕ}
    {ω : Ω} {q : ℕ} (hq : q ≤ m - nstar)
    (hlt : q < stoppingGeneration nstar qfb R m ω) :
    (3 : ℝ) ^ m < R (m - q) ω := by
  by_contra hcon
  push Not at hcon
  have hex : ∃ q, IsStoppingCandidate nstar R m ω q := ⟨q, hq, hcon⟩
  have hle : Nat.find hex ≤ q := Nat.find_le ⟨hq, hcon⟩
  rw [stoppingGeneration, dite_eq_left hex] at hlt
  omega

/-- The shifted upper-tail event of the generation map inherits the overshoot
bound of a single stopping radius; beyond the fallback range it is empty. -/
theorem measureReal_stoppingGeneration_gt_le
    {P : Measure Ω} [IsProbabilityMeasure P] {nstar qfb b : ℕ} {R : ℕ → Ω → ℝ}
    {bnd : ℕ → ℝ} (hbnd : ∀ q, 0 ≤ bnd q)
    (hR : ∀ n q : ℕ, nstar ≤ n →
      P.real {ω | (3 : ℝ) ^ (n + q + b) < R n ω} ≤ bnd q)
    (m q : ℕ) :
    P.real {ω | q + (qfb + b) < stoppingGeneration nstar qfb R m ω} ≤ bnd q := by
  by_cases hcase : q + b + nstar ≤ m
  · have hqb : q + b ≤ m - nstar := by omega
    have hsub : {ω | q + (qfb + b) < stoppingGeneration nstar qfb R m ω} ⊆
        {ω | (3 : ℝ) ^ (m - (q + b) + q + b) < R (m - (q + b)) ω} := by
      intro ω hω
      have hlt : q + b < stoppingGeneration nstar qfb R m ω := by
        simp only [Set.mem_ofPred_eq] at hω
        omega
      have hover := lt_of_lt_stoppingGeneration (qfb := qfb) hqb hlt
      have hmm : m - (q + b) + q + b = m := by omega
      simpa only [Set.mem_ofPred_eq, hmm] using hover
    exact le_trans (measureReal_mono hsub) (hR (m - (q + b)) q (by omega))
  · have hempty :
        {ω | q + (qfb + b) < stoppingGeneration nstar qfb R m ω} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have hle := stoppingGeneration_le nstar qfb R m ω
      omega
    rw [hempty]
    simpa only [measureReal_empty] using hbnd q

end

end Quenched
end HighContrast
end HCPolySupport
