/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianKilledOUPathMeasure.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianSublevelPathExhaustion
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianOUActionWeight
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianInitialDensityCancellation

/-!
# Ginibre Hamiltonian killed OU path measure

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreHamiltonianKilledOUAction_initial_cancellation`,
`ginibreHamiltonianKilledOUActionMeasure_reverse`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths over the horizon `[0, T]`. -/
local instance ginibreKilledOUPathMeasurable (n : ℕ) (T : ℝ) :
    MeasurableSpace C(Icc (0 : ℝ) T, Configuration n) := borel _
local instance ginibreKilledOUPathBorel (n : ℕ) (T : ℝ) :
    BorelSpace C(Icc (0 : ℝ) T, Configuration n) := ⟨rfl⟩

/-- The paths on `[0, T]` that stay in the sublevel domain
`ginibreHamiltonianOUSublevelDomain n R` at all times. -/
def ginibreHamiltonianCompactSurvival (n : ℕ) (T R : ℝ) :
    Set C(Icc (0 : ℝ) T, Configuration n) :=
  {x | ∀ t, x t ∈ ginibreHamiltonianOUSublevelDomain n R}

theorem ginibreHamiltonianCompactSurvival_isOpen (n : ℕ) (T R : ℝ) :
    IsOpen (ginibreHamiltonianCompactSurvival n T R) := by
  have hW : Continuous (ginibreWeight n) :=
    (Real.continuous_exp.comp ((contDiff_configurationNormSq (n := n)).continuous.const_mul (-(n :
        ℝ)))).mul
      (contDiff_vandermondeWeight n).continuous
  have hG : IsOpen (ginibreHamiltonianOUSublevelDomain n R) := isOpen_lt continuous_const hW
  simpa only [ginibreHamiltonianCompactSurvival, Set.mapsTo_univ_iff, Set.range_subset_iff] using
    (ContinuousMap.isOpen_setOfPred_mapsTo (X := Icc (0 : ℝ) T) isCompact_univ hG)

theorem ginibreHamiltonianCompactSurvival_measurableSet (n : ℕ) (T R : ℝ) :
    MeasurableSet (ginibreHamiltonianCompactSurvival n T R) :=
  (ginibreHamiltonianCompactSurvival_isOpen n T R).measurableSet

/-- Literal Hamiltonian action on the event that the whole reference path
survives the prescribed Hamiltonian sublevel. -/
def ginibreHamiltonianKilledOUActionWeight (n : ℕ) (α T R : ℝ) (hT : 0 ≤ T) :
    C(Icc (0 : ℝ) T, Configuration n) → ℝ :=
  (ginibreHamiltonianCompactSurvival n T R).indicator
    (ginibreHamiltonianOUActionWeight n α T hT)

theorem ginibreHamiltonianKilledOUActionWeight_measurable (n : ℕ) (α T R : ℝ) (hT : 0 ≤ T) :
    Measurable (ginibreHamiltonianKilledOUActionWeight n α T R hT) :=
  (ginibreHamiltonianOUActionWeight_measurable n α T hT).indicator
    (ginibreHamiltonianCompactSurvival_measurableSet n T R)

theorem ginibreHamiltonianKilledOUActionWeight_reverse (n : ℕ) (α T R : ℝ) (hT : 0 ≤ T)
    (x : C(Icc (0 : ℝ) T, Configuration n)) :
    ginibreHamiltonianKilledOUActionWeight n α T R hT
      (x.comp (ginibreHamiltonianCompactReverseTime T hT)) =
      ginibreHamiltonianKilledOUActionWeight n α T R hT x := by
  classical
  have hh := ginibreHamiltonian_compact_sublevel_survival_reverse T hT R x
  change (if (∀ t, (x.comp (ginibreHamiltonianCompactReverseTime T hT)) t ∈
    ginibreHamiltonianOUSublevelDomain n R) then _ else 0) =
    (if (∀ t, x t ∈ ginibreHamiltonianOUSublevelDomain n R) then _ else 0)
  rw [hh, ginibreHamiltonianOUActionWeight_reverse]

/-- Initial Ginibre/Gaussian interaction weighting cancels the genuine
likelihood initial factor, also off survival where both killed densities vanish. -/
theorem ginibreHamiltonianKilledOUAction_initial_cancellation (n : ℕ) (α T R : ℝ) (hT : 0 ≤ T)
    (x : C(Icc (0 : ℝ) T, Configuration n)) :
    vandermondeWeight (x ⟨0, ⟨le_rfl, hT⟩⟩) *
      (ginibreHamiltonianCompactSurvival n T R).indicator
        (fun y => Real.exp (ginibreInteractionPotential n (y ⟨0, ⟨le_rfl, hT⟩⟩)) *
          ginibreHamiltonianOUActionWeight n α T hT y) x =
      ginibreHamiltonianKilledOUActionWeight n α T R hT x := by
  classical
  by_cases hx : x ∈ ginibreHamiltonianCompactSurvival n T R
  · have h0 := hx (⟨0, ⟨le_rfl, hT⟩⟩ : Icc (0 : ℝ) T)
    have hK : x ⟨0, ⟨le_rfl, hT⟩⟩ ∈ ginibreHamiltonianSublevel n R := by
      rw [ginibreHamiltonianSublevel_eq_weight_superlevel]
      exact (show Real.exp (-R) < ginibreWeight n (x ⟨0, ⟨le_rfl, hT⟩⟩) from h0).le
    simp only [Set.indicator_of_mem hx, ginibreHamiltonianKilledOUActionWeight]
    exact ginibreInteraction_initial_action_cancellation _ hK.1 _
  · simp only [Set.indicator_of_notMem hx, ginibreHamiltonianKilledOUActionWeight, mul_zero]

/-- Reversal of the actual stationary original-Brownian OU reference with the
literal killed action. Identification with the killed singular SDE is separate. -/
theorem ginibreHamiltonianKilledOUActionMeasure_reverse {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : IsBrownianReal B P) (Z : Ω → ℝ) (hZ : HasLaw Z (gaussianReal 0 (1 / 2)) P)
    (hind : IndepFun Z (fun ω t => B t ω) P) (α R : ℝ) (T : ℝ≥0) :
    ((ginibreConfigurationOUReferenceLaw n B P Z (2*α/(n : ℝ)).toNNReal T).withDensity
      (fun x => ENNReal.ofReal (ginibreHamiltonianKilledOUActionWeight n α (T : ℝ) R T.property
          x))).map
      (fun x => x.comp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) =
    (ginibreConfigurationOUReferenceLaw n B P Z (2*α/(n : ℝ)).toNNReal T).withDensity
      (fun x => ENNReal.ofReal (ginibreHamiltonianKilledOUActionWeight n α (T : ℝ) R T.property x))
          := by
  exact invariant_measure_withDensity_of_invariant_weight _ _
    (ContinuousMap.continuous_precomp (ginibreHamiltonianCompactReverseTime (T : ℝ)
        T.property)).measurable
    (ginibreConfigurationOUReferenceLaw_reverse n B P hB Z hZ hind _ T) _
    (ENNReal.measurable_ofReal.comp (ginibreHamiltonianKilledOUActionWeight_measurable n α (T : ℝ) R
        T.property))
    (fun x => congrArg ENNReal.ofReal (ginibreHamiltonianKilledOUActionWeight_reverse n α (T : ℝ) R
        T.property x))

end
end GinibrePoincare
