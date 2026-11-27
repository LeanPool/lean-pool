/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageHorizonChoice

/-!
# The early and tail estimates for the chosen syndrome

An exact minimizer of the computable truncated-wager objective satisfies the
actual rank-drop early-wager estimate. The first-drop tail is preserved by
every syndrome, so the same selected syndrome satisfies both estimates.
These are one-stage statements for the actual conditional input laws.
-/

@[expose] public section

noncomputable section

namespace Klr.StageHorizonChoice

open MeasureTheory ProbabilityTheory AffineBlock StageSyndrome
open scoped BigOperators ENNReal

/-- The actual early rank-drop wager of a single block, expressed through
the existing family-based API. The unused family coordinates do not enter it. -/
def earlyWager (B : AffineBlock) (π : ScanRule) (h : List Bool → ℚ)
    (V : ℕ) : Cantor → ℝ :=
  EarlyLateWagers.earlyWager (fun _ => B) π (fun v => (h v : ℝ)) (fun _ => V) 0

/-- Reinsert the one-block quantity at any position of a stage sequence. -/
theorem earlyWager_eq_family (B : ℕ → AffineBlock) (π : ScanRule)
    (h : List Bool → ℚ) (V : ℕ → ℕ) (j : ℕ) :
    earlyWager (B j) π h (V j) =
      EarlyLateWagers.earlyWager B π (fun v => (h v : ℝ)) V j := rfl

theorem earlyWager_nonneg (B : AffineBlock) (π : ScanRule)
    (h : List Bool → ℚ) (V : ℕ) (X : Cantor) : 0 ≤ earlyWager B π h V X :=
  EarlyLateWagers.earlyWager_nonneg (fun _ => B) π _ (fun _ => V) 0 X

theorem integrable_earlyWager (μ : Measure Cantor) [IsFiniteMeasure μ]
    (B : AffineBlock) (π : ScanRule) (h : List Bool → ℚ) (V : ℕ)
    (hh : ∀ v, |(h v : ℝ)| ≤ (1 / 2 : ℝ)) :
    Integrable (earlyWager B π h V) μ := by
  apply Integrable.of_bound
    (EarlyLateWagers.measurable_earlyWager (fun _ => B) π _ (fun _ => V) 0).aestronglyMeasurable
    ((V : ℝ) / 2)
  apply Filter.Eventually.of_forall
  intro X
  rw [Real.norm_eq_abs]
  change |earlyWager B π h V X| ≤ _
  rw [abs_of_nonneg (earlyWager_nonneg B π h V X)]
  exact EarlyLateWagers.earlyWager_le_half_horizon (fun _ => B) π _ (fun _ => V) hh 0 X

variable {ι : Type*} [Fintype ι]

/-- The computable truncated objective dominates the sum of actual early
rank-drop wagers plus the partial-rank probabilities. -/
theorem sum_early_partial_le_objective (μ : Measure Cantor) [IsFiniteMeasure μ]
    (B : AffineBlock) (π : ι → ScanRule) (h : ι → List Bool → ℚ) (V : ℕ)
    (hh : ∀ i v, |(h i v : ℝ)| ≤ (1 / 2 : ℝ)) :
    (∑ i, ((∫ X, earlyWager B (π i) (h i) V X ∂μ) +
      μ.real (LateDropBound.partialEvent B (π i) V))) ≤
      ∫ X, objective B π h V X ∂μ := by
  rw [integral_objective μ B π h V hh, StageRankLimit.partialMass,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply add_le_add _ le_rfl
  exact integral_mono (integrable_earlyWager μ B (π i) (h i) V (hh i))
    (integrable_truncated μ (π i) (h i) B.support V (hh i))
    (fun X => StageFiniteWager.earlyWager_le_truncated (fun _ => B) (π i) (h i)
      (fun _ => V) 0 X)

/-- Every exact minimizing syndrome satisfies the simultaneous real-valued
version of estimate (6). Its objective may count additional support queries. -/
theorem minimizing_syndrome_early_sum_lt {κ : Type*} [Finite κ]
    (old : κ → AffineBlock) (B : AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (hnew : ∀ k, Disjoint (old k).support B.support)
    (π : ι → ScanRule) (h : ι → List Bool → ℚ) (V : ℕ)
    (hh : ∀ i v, |(h i v : ℝ)| ≤ (1 / 2 : ℝ)) (error : ℝ)
    (hwager : (∑ i, ∫ X, StageWeights.supportWager (π i)
      (fun v => (h i v : ℝ)) B.support X ∂finiteStageLaw old) < error)
    (hpartial : StageRankLimit.partialMass (finiteStageLaw old) B π V < 3 * error)
    (y : Fin B.rank → ZMod 2)
    (hmin : ∀ z, (∫ X, objective B π h V X ∂law old B y) ≤
      ∫ X, objective B π h V X ∂law old B z) :
    (∑ i, ((∫ X, earlyWager (withSyndrome B y) (π i) (h i) V X ∂law old B y) +
      (law old B y).real (LateDropBound.partialEvent (withSyndrome B y) (π i) V))) <
      4 * error :=
  (sum_early_partial_le_objective (law old B y) (withSyndrome B y) π h V hh).trans_lt
    (minimizing_objective_lt old B hold hnew π h V hh error hwager hpartial y hmin)

/-- Existence of an admissible syndrome follows from actual uniform
syndrome averaging. This theorem does not assume a minimizing oracle. -/
theorem exists_syndrome_early_sum_lt {κ : Type*} [Finite κ]
    (old : κ → AffineBlock) (B : AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (hnew : ∀ k, Disjoint (old k).support B.support)
    (π : ι → ScanRule) (h : ι → List Bool → ℚ) (V : ℕ)
    (hh : ∀ i v, |(h i v : ℝ)| ≤ (1 / 2 : ℝ)) (error : ℝ)
    (hwager : (∑ i, ∫ X, StageWeights.supportWager (π i)
      (fun v => (h i v : ℝ)) B.support X ∂finiteStageLaw old) < error)
    (hpartial : StageRankLimit.partialMass (finiteStageLaw old) B π V < 3 * error) :
    ∃ y : Fin B.rank → ZMod 2,
      (∑ i, ((∫ X, earlyWager (withSyndrome B y) (π i) (h i) V X ∂law old B y) +
        (law old B y).real (LateDropBound.partialEvent (withSyndrome B y) (π i) V))) <
        4 * error := by
  let : IsProbabilityMeasure (finiteStageLaw old) :=
    finiteStageLaw_isProbabilityMeasure_of_disjoint old hold
  obtain ⟨y, hy⟩ := exists_integral_cond_syndrome_le old B hold hnew
    (integrable_objective (finiteStageLaw old) B π h V hh)
  refine ⟨y, ?_⟩
  exact ((sum_early_partial_le_objective (law old B y)
    (withSyndrome B y) π h V hh).trans hy).trans_lt
    (integral_objective_lt (finiteStageLaw old) B π h V hh error hwager hpartial)

/-- Conditioning on any syndrome preserves the probability of a first drop
after the horizon, by the full-rank pre-drop cylinder identity. -/
theorem law_rankDropTailEvent {κ : Type*} [Finite κ] (old : κ → AffineBlock)
    (B : AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (hnew : ∀ k, Disjoint (old k).support B.support)
    (y : Fin B.rank → ZMod 2) (π : ScanRule) (V : ℕ) :
    law old B y (StoppingTranscript.rankDropTailEvent (withSyndrome B y) π V) =
      finiteStageLaw old (StoppingTranscript.rankDropTailEvent B π V) := by
  rw [law, finiteStageLaw,
    cond_cond_eq_cond_inter (measurableSet_familyEvent old) (withSyndrome B y).measurableSet_event]
  simpa only [rankDropTailEvent_withSyndrome, finiteStageLaw] using
    StoppingTranscript.nextStage_rankDropTail old (withSyndrome B y) hold hnew π V

theorem law_real_rankDropTailEvent {κ : Type*} [Finite κ] (old : κ → AffineBlock)
    (B : AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (hnew : ∀ k, Disjoint (old k).support B.support)
    (y : Fin B.rank → ZMod 2) (π : ScanRule) (V : ℕ) :
    (law old B y).real (StoppingTranscript.rankDropTailEvent (withSyndrome B y) π V) =
      (finiteStageLaw old).real (StoppingTranscript.rankDropTailEvent B π V) :=
  congrArg ENNReal.toReal (law_rankDropTailEvent old B hold hnew y π V)

/-- The summed tail bound produced by the horizon search survives every
syndrome choice, in particular the computable objective minimizer. -/
theorem syndrome_sum_tail_lt {κ : Type*} [Finite κ] (old : κ → AffineBlock)
    (B : AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (hnew : ∀ k, Disjoint (old k).support B.support)
    (π : ι → ScanRule) (V : ℕ) (error : ℝ)
    (htail : (∑ i, (finiteStageLaw old).real
      (StoppingTranscript.rankDropTailEvent B (π i) V)) < 2 * error)
    (y : Fin B.rank → ZMod 2) :
    (∑ i, (law old B y).real
      (StoppingTranscript.rankDropTailEvent (withSyndrome B y) (π i) V)) < 2 * error := by
  simpa only [law_real_rankDropTailEvent old B hold hnew] using htail

/-- Convert the real-valued early estimate to the nonnegative lower-integral
form used by `StageEstimates`. -/
theorem early_lintegral_add_measure_le (μ : Measure Cantor) [IsFiniteMeasure μ]
    (B : AffineBlock) (π : ScanRule) (h : List Bool → ℚ) (V : ℕ)
    (hh : ∀ v, |(h v : ℝ)| ≤ (1 / 2 : ℝ)) {c : ℝ}
    (hbound : (∫ X, earlyWager B π h V X ∂μ) +
      μ.real (LateDropBound.partialEvent B π V) ≤ c) :
    (∫⁻ X, ENNReal.ofReal (earlyWager B π h V X) ∂μ) +
      μ (LateDropBound.partialEvent B π V) ≤ ENNReal.ofReal c := by
  have hn : 0 ≤ ∫ X, earlyWager B π h V X ∂μ :=
    integral_nonneg (earlyWager_nonneg B π h V)
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_earlyWager μ B π h V hh)
    (Filter.Eventually.of_forall (earlyWager_nonneg B π h V))]
  calc
    _ = ENNReal.ofReal ((∫ X, earlyWager B π h V X ∂μ) +
        μ.real (LateDropBound.partialEvent B π V)) := by
      rw [ENNReal.ofReal_add hn measureReal_nonneg,
        Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ _)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

/-- One chosen minimizing syndrome simultaneously satisfies (6) and (7)
for every protected strategy, in the measure types used by the stage API. -/
theorem minimizing_syndrome_stage_bounds {κ : Type*} [Finite κ]
    (old : κ → AffineBlock) (B : AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (hnew : ∀ k, Disjoint (old k).support B.support)
    (π : ι → ScanRule) (h : ι → List Bool → ℚ) (V : ℕ)
    (hh : ∀ i v, |(h i v : ℝ)| ≤ (1 / 2 : ℝ)) (error : ℝ)
    (hwager : (∑ i, ∫ X, StageWeights.supportWager (π i)
      (fun v => (h i v : ℝ)) B.support X ∂finiteStageLaw old) < error)
    (hpartial : StageRankLimit.partialMass (finiteStageLaw old) B π V < 3 * error)
    (htail : (∑ i, (finiteStageLaw old).real
      (StoppingTranscript.rankDropTailEvent B (π i) V)) < 2 * error)
    (y : Fin B.rank → ZMod 2)
    (hmin : ∀ z, (∫ X, objective B π h V X ∂law old B y) ≤
      ∫ X, objective B π h V X ∂law old B z) :
    ∀ i,
      ((∫⁻ X, ENNReal.ofReal (earlyWager (withSyndrome B y) (π i) (h i) V X)
        ∂law old B y) +
        law old B y (LateDropBound.partialEvent (withSyndrome B y) (π i) V) ≤
          ENNReal.ofReal (4 * error)) ∧
      law old B y (StoppingTranscript.rankDropTailEvent (withSyndrome B y) (π i) V) ≤
        ENNReal.ofReal (2 * error) := by
  have hearly := minimizing_syndrome_early_sum_lt old B hold hnew π h V hh error
    hwager hpartial y hmin
  have htail' := syndrome_sum_tail_lt old B hold hnew π V error htail y
  intro i
  constructor
  · apply early_lintegral_add_measure_le (law old B y) (withSyndrome B y) (π i) (h i) V (hh i)
    apply le_trans _ hearly.le
    refine Finset.single_le_sum (f := fun j : ι =>
      (∫ X, earlyWager (withSyndrome B y) (π j) (h j) V X ∂law old B y) +
        (law old B y).real (LateDropBound.partialEvent (withSyndrome B y) (π j) V))
      (s := Finset.univ) (a := i) ?_ (Finset.mem_univ i)
    intro j _
    exact add_nonneg
      (integral_nonneg (earlyWager_nonneg (withSyndrome B y) (π j) (h j) V))
      measureReal_nonneg
  · have hi : (law old B y).real
        (StoppingTranscript.rankDropTailEvent (withSyndrome B y) (π i) V) ≤ 2 * error := by
      apply le_trans _ htail'.le
      exact Finset.single_le_sum (f := fun j : ι => (law old B y).real
        (StoppingTranscript.rankDropTailEvent (withSyndrome B y) (π j) V))
        (s := Finset.univ) (fun _ _ => measureReal_nonneg) (Finset.mem_univ i)
    have hle := ENNReal.ofReal_le_ofReal hi
    simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top (law old B y) _)] using hle

end Klr.StageHorizonChoice
