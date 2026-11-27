/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageFiniteWager
public import LeanPool.KLRandomness.StageSyndrome
public import LeanPool.KLRandomness.StageRankLimitMeasure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Choosing a syndrome at the reconstructed horizon

The objective averages the actual truncated support wagers and partial-rank
indicators of all protected strategies. It depends only on the finite
horizon transcripts, so its conditional expectations can be computed by the
finite stage interpreter. Uniform syndrome averaging shows that every exact
minimizer meets the simultaneous early-wager bound.
-/

@[expose] public section

noncomputable section

namespace Klr.StageHorizonChoice

open MeasureTheory ProbabilityTheory AffineBlock StageSyndrome
open scoped BigOperators ENNReal

/-- The actual next-stage law for a chosen syndrome. -/
def law {κ : Type*} (old : κ → AffineBlock) (B : AffineBlock)
    (y : Fin B.rank → ZMod 2) : Measure Cantor :=
  cond (finiteStageLaw old) (withSyndrome B y).event

instance {κ : Type*} (old : κ → AffineBlock) (B : AffineBlock)
    (y : Fin B.rank → ZMod 2) : IsFiniteMeasure (law old B y) := by
  unfold law
  infer_instance

@[simp]
theorem remainingRank_withSyndrome (B : AffineBlock) (y : Fin B.rank → ZMod 2)
    (π : ScanRule) (v : List Bool) :
    (withSyndrome B y).remainingRank π v = B.remainingRank π v := rfl

@[simp]
theorem partialEvent_withSyndrome (B : AffineBlock) (y : Fin B.rank → ZMod 2)
    (π : ScanRule) (V : ℕ) :
    LateDropBound.partialEvent (withSyndrome B y) π V = LateDropBound.partialEvent B π V := rfl

@[simp]
theorem rankDropTailEvent_withSyndrome (B : AffineBlock) (y : Fin B.rank → ZMod 2)
    (π : ScanRule) (V : ℕ) :
    StoppingTranscript.rankDropTailEvent (withSyndrome B y) π V =
      StoppingTranscript.rankDropTailEvent B π V := rfl

@[simp]
theorem noDropEvent_withSyndrome (B : AffineBlock) (y : Fin B.rank → ZMod 2)
    (π : ScanRule) :
    NoDrop.noDropEvent (withSyndrome B y) π = NoDrop.noDropEvent B π := rfl

@[simp]
theorem hasDrop_withSyndrome (B : AffineBlock) (y : Fin B.rank → ZMod 2)
    (π : ScanRule) :
    LateDropBound.hasDrop (withSyndrome B y) π = LateDropBound.hasDrop B π := rfl

/-- Bounded wager fractions make the all-time finite-support cost integrable
under every finite measure. Freshness leaves at most one wager per position. -/
theorem integrable_supportWager_of_half_bound (μ : Measure Cantor) [IsFiniteMeasure μ]
    (π : ScanRule) (h : List Bool → ℚ) (S : Finset ℕ)
    (hh : ∀ v, |(h v : ℝ)| ≤ (1 / 2 : ℝ)) :
    Integrable (StageWeights.supportWager π (fun v => (h v : ℝ)) S) μ := by
  classical
  apply Integrable.of_bound (StageWeights.measurable_supportWager π _ S).aestronglyMeasurable
    ((S.card : ℝ) / 2)
  apply Filter.Eventually.of_forall
  intro X
  rw [Real.norm_eq_abs, abs_of_nonneg (StageWeights.supportWager_nonneg π _ S X)]
  calc
    StageWeights.supportWager π (fun v => (h v : ℝ)) S X ≤
        ∑ _a ∈ S, (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : ∃ t, π.query (π.transcript X t) = a
      · obtain ⟨t, rfl⟩ := ha
        rw [StageWeights.wagerAt_eq_of_query]
        exact hh _
      · rw [StageWeights.wagerAt_eq_zero_of_not_queried π _ a X (by simpa using ha)]
        norm_num
    _ = _ := by simp [div_eq_mul_inv]

/-- The rational finite-horizon wager statistic is integrable under every
finite input law. -/
theorem integrable_truncated (μ : Measure Cantor) [IsFiniteMeasure μ]
    (π : ScanRule) (h : List Bool → ℚ) (S : Finset ℕ) (V : ℕ)
    (hh : ∀ v, |(h v : ℝ)| ≤ (1 / 2 : ℝ)) :
    Integrable (fun X => (StageFiniteWager.truncated π h S (π.transcript X V) : ℝ)) μ := by
  apply Integrable.of_bound (StageFiniteWager.measurable_truncated π h S V).aestronglyMeasurable
    ((V : ℝ) / 2)
  apply Filter.Eventually.of_forall
  intro X
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact StageFiniteWager.truncated_transcript_le_half_horizon π h S X V hh
  · exact_mod_cast StageFiniteWager.truncated_nonneg π h S (π.transcript X V)

variable {ι : Type*} [Fintype ι]

/-- One finite-transcript objective for all protected strategies. It uses
truncated support wagers so that exact rational evaluation is possible. -/
def objective (B : AffineBlock) (π : ι → ScanRule) (h : ι → List Bool → ℚ)
    (V : ℕ) (X : Cantor) : ℝ :=
  ∑ i, ((StageFiniteWager.truncated (π i) (h i) B.support ((π i).transcript X V) : ℝ) +
    (LateDropBound.partialEvent B (π i) V).indicator (fun _ => (1 : ℝ)) X)

@[simp]
theorem objective_withSyndrome (B : AffineBlock) (y : Fin B.rank → ZMod 2)
    (π : ι → ScanRule) (h : ι → List Bool → ℚ) (V : ℕ) :
    objective (withSyndrome B y) π h V = objective B π h V := rfl

theorem integrable_objective (μ : Measure Cantor) [IsFiniteMeasure μ]
    (B : AffineBlock) (π : ι → ScanRule) (h : ι → List Bool → ℚ) (V : ℕ)
    (hh : ∀ i v, |(h i v : ℝ)| ≤ (1 / 2 : ℝ)) :
    Integrable (objective B π h V) μ := by
  unfold objective
  apply integrable_finsetSum
  intro i _
  exact (integrable_truncated μ (π i) (h i) B.support V (hh i)).add
    ((integrable_const (1 : ℝ)).indicator (LateDropBound.measurableSet_partialEvent B (π i) V))

/-- Separating the two parts of the finite objective recovers the actual
partial-rank probability sum. -/
theorem integral_objective (μ : Measure Cantor) [IsFiniteMeasure μ]
    (B : AffineBlock) (π : ι → ScanRule) (h : ι → List Bool → ℚ) (V : ℕ)
    (hh : ∀ i v, |(h i v : ℝ)| ≤ (1 / 2 : ℝ)) :
    (∫ X, objective B π h V X ∂μ) =
      (∑ i, ∫ X, (StageFiniteWager.truncated (π i) (h i) B.support
        ((π i).transcript X V) : ℝ) ∂μ) + StageRankLimit.partialMass μ B π V := by
  unfold objective
  rw [integral_finsetSum (f := fun i X =>
    (StageFiniteWager.truncated (π i) (h i) B.support ((π i).transcript X V) : ℝ) +
      (LateDropBound.partialEvent B (π i) V).indicator (fun _ => (1 : ℝ)) X)
    Finset.univ (fun i _ =>
    (integrable_truncated μ (π i) (h i) B.support V (hh i)).add
      ((integrable_const (1 : ℝ)).indicator
        (LateDropBound.measurableSet_partialEvent B (π i) V)))]
  simp_rw [integral_add (integrable_truncated μ (π _) (h _) B.support V (hh _))
    ((integrable_const (1 : ℝ)).indicator (LateDropBound.measurableSet_partialEvent B (π _) V)),
    integral_indicator_const _ (LateDropBound.measurableSet_partialEvent B (π _) V),
    smul_eq_mul, mul_one]
  exact Finset.sum_add_distrib

/-- The old-stage objective is strictly below `4 * error` once the selected
support has total expected wager below `error` and the horizon's partial-rank
mass is below `3 * error`. -/
theorem integral_objective_lt (μ : Measure Cantor) [IsFiniteMeasure μ]
    (B : AffineBlock) (π : ι → ScanRule) (h : ι → List Bool → ℚ) (V : ℕ)
    (hh : ∀ i v, |(h i v : ℝ)| ≤ (1 / 2 : ℝ)) (error : ℝ)
    (hwager : (∑ i, ∫ X, StageWeights.supportWager (π i)
      (fun v => (h i v : ℝ)) B.support X ∂μ) < error)
    (hpartial : StageRankLimit.partialMass μ B π V < 3 * error) :
    (∫ X, objective B π h V X ∂μ) < 4 * error := by
  have hle : (∑ i, ∫ X, (StageFiniteWager.truncated (π i) (h i) B.support
      ((π i).transcript X V) : ℝ) ∂μ) ≤
      ∑ i, ∫ X, StageWeights.supportWager (π i) (fun v => (h i v : ℝ)) B.support X ∂μ := by
    apply Finset.sum_le_sum
    intro i _
    exact integral_mono (integrable_truncated μ (π i) (h i) B.support V (hh i))
      (integrable_supportWager_of_half_bound μ (π i) (h i) B.support (hh i))
      (fun X => StageFiniteWager.truncated_transcript_le_supportWager (π i) (h i) B.support X V)
  rw [integral_objective μ B π h V hh]
  linarith

/-- Every exact minimizer of the finite conditional objective has a cost
below the required budget. The selection of the minimizer can therefore be
performed by the finite rational search without extra advice. -/
theorem minimizing_objective_lt {κ : Type*} [Finite κ] (old : κ → AffineBlock)
    (B : AffineBlock)
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
    (∫ X, objective B π h V X ∂law old B y) < 4 * error := by
  let : IsProbabilityMeasure (finiteStageLaw old) :=
    finiteStageLaw_isProbabilityMeasure_of_disjoint old hold
  obtain ⟨z, hz⟩ := exists_integral_cond_syndrome_le old B hold hnew
    (integrable_objective (finiteStageLaw old) B π h V hh)
  exact ((hmin z).trans hz).trans_lt
    (integral_objective_lt (finiteStageLaw old) B π h V hh error hwager hpartial)

end Klr.StageHorizonChoice
