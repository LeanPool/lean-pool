/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageRankLimit
public import LeanPool.KLRandomness.StageHorizonComputable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith

/-!
# Limits of the actual finite-horizon rank probabilities

For any finite input measure, bounded convergence turns pointwise rank
stabilization into convergence of the partial-rank probabilities. Continuity
from below gives convergence of the probabilities of a drop by time `n`.
Finite sums supply exactly the two limits used by the bounded-advice horizon
search. The first-drop tail is the difference between the limiting drop mass
and the mass already seen.
-/

@[expose] public section

noncomputable section

namespace Klr.StageRankLimit

open MeasureTheory Filter PoolQuery
open scoped Topology BigOperators

/-- Bounded convergence for the actual finite partial-rank events. -/
theorem tendsto_partial_probability (μ : Measure Cantor) [IsFiniteMeasure μ]
    (B : AffineBlock) (π : ScanRule) :
    Tendsto (fun n => μ.real (LateDropBound.partialEvent B π n)) atTop
      (𝓝 (μ.real (eventualPartialEvent B π))) := by
  classical
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n => (LateDropBound.partialEvent B π n).indicator (fun _ => (1 : ℝ)))
    (f := (eventualPartialEvent B π).indicator (fun _ => (1 : ℝ)))
    (fun _ => (1 : ℝ))
    (fun n => (measurable_const.indicator
      (LateDropBound.measurableSet_partialEvent B π n)).aestronglyMeasurable)
    (integrable_const 1) (fun n => Eventually.of_forall fun X => by
      by_cases hX : X ∈ LateDropBound.partialEvent B π n <;>
        simp [hX])
    (Eventually.of_forall fun X => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_partialEvent_iff B π X] with n hn
      simp only [Set.indicator_apply, hn])
  have hfinite (n : ℕ) :
      (∫ X, (LateDropBound.partialEvent B π n).indicator (fun _ => (1 : ℝ)) X ∂μ) =
        μ.real (LateDropBound.partialEvent B π n) :=
    integral_indicator_one (LateDropBound.measurableSet_partialEvent B π n)
  have hlimit :
      (∫ X, (eventualPartialEvent B π).indicator (fun _ => (1 : ℝ)) X ∂μ) =
        μ.real (eventualPartialEvent B π) :=
    integral_indicator_one (measurableSet_eventualPartialEvent B π)
  simpa only [hfinite, hlimit] using h

/-- The drop-by-time probabilities increase to the probability of any drop. -/
theorem tendsto_drop_probability (μ : Measure Cantor) [IsFiniteMeasure μ]
    (B : AffineBlock) (π : ScanRule) :
    Tendsto (fun n => μ.real (droppedBy B π n)) atTop
      (𝓝 (μ.real (LateDropBound.hasDrop B π))) := by
  have h := tendsto_measure_iUnion_atTop (μ := μ) (droppedBy_mono B π)
  rw [iUnion_droppedBy] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp h

/-- The exact finite-stage first-drop tail identity. -/
theorem tail_probability_eq_sub (μ : Measure Cantor) [IsFiniteMeasure μ]
    (B : AffineBlock) (π : ScanRule) (N : ℕ) :
    μ.real (StoppingTranscript.rankDropTailEvent B π N) =
      μ.real (LateDropBound.hasDrop B π) - μ.real (droppedBy B π N) := by
  rw [rankDropTailEvent_eq_sdiff,
    measureReal_sdiff (droppedBy_subset_hasDrop B π N) (measurableSet_droppedBy B π N)]

/-- The limiting partial-rank probability is controlled by the two actual
input-space events used to select the candidate. -/
theorem partial_limit_probability_le (μ : Measure Cantor) [IsFiniteMeasure μ]
    (B : AffineBlock) (π : ScanRule) (G : Finset ℕ) (hBG : B.support ⊆ G)
    (H : Set Cantor) :
    μ.real (eventualPartialEvent B π) ≤
      μ.real (π.observationMap ⁻¹' H ∩
        {X | 0 < missedCount π G (π.observationMap X)}) +
      μ.real (π.observationMap ⁻¹' Hᶜ ∩ LateDropBound.hasDrop B π) :=
  (measureReal_mono
    (eventualPartialEvent_subset_highMiss_union_lowDrop B π G hBG H)).trans
      (measureReal_union_le _ _)

variable {ι : Type*} [Fintype ι]

/-- Sum of finite partial-rank probabilities for the protected scan family. -/
def partialMass (μ : Measure Cantor) (B : AffineBlock) (π : ι → ScanRule) (n : ℕ) : ℝ :=
  ∑ i, μ.real (LateDropBound.partialEvent B (π i) n)

/-- Sum of limiting partial-rank probabilities. -/
def partialLimitMass (μ : Measure Cantor) (B : AffineBlock) (π : ι → ScanRule) : ℝ :=
  ∑ i, μ.real (eventualPartialEvent B (π i))

/-- Sum of probabilities of a first drop by the horizon. -/
def dropMass (μ : Measure Cantor) (B : AffineBlock) (π : ι → ScanRule) (n : ℕ) : ℝ :=
  ∑ i, μ.real (droppedBy B (π i) n)

/-- Sum of probabilities that a first drop ever occurs. -/
def dropLimitMass (μ : Measure Cantor) (B : AffineBlock) (π : ι → ScanRule) : ℝ :=
  ∑ i, μ.real (LateDropBound.hasDrop B (π i))

theorem tendsto_partialMass (μ : Measure Cantor) [IsFiniteMeasure μ]
    (B : AffineBlock) (π : ι → ScanRule) :
    Tendsto (partialMass μ B π) atTop (𝓝 (partialLimitMass μ B π)) :=
  tendsto_finsetSum _ fun i _ => tendsto_partial_probability μ B (π i)

theorem tendsto_dropMass (μ : Measure Cantor) [IsFiniteMeasure μ]
    (B : AffineBlock) (π : ι → ScanRule) :
    Tendsto (dropMass μ B π) atTop (𝓝 (dropLimitMass μ B π)) :=
  tendsto_finsetSum _ fun i _ => tendsto_drop_probability μ B (π i)

theorem dropMass_mono (μ : Measure Cantor) [IsFiniteMeasure μ]
    (B : AffineBlock) (π : ι → ScanRule) : Monotone (dropMass μ B π) := by
  intro m n hmn
  exact Finset.sum_le_sum fun i _ => measureReal_mono (droppedBy_mono B (π i) hmn)

theorem dropLimitMass_nonneg (μ : Measure Cantor) (B : AffineBlock)
    (π : ι → ScanRule) : 0 ≤ dropLimitMass μ B π :=
  Finset.sum_nonneg fun _ _ => measureReal_nonneg

/-- The total first-drop mass is at most the number of protected strategies. -/
theorem dropLimitMass_le_card (μ : Measure Cantor) [IsProbabilityMeasure μ]
    (B : AffineBlock) (π : ι → ScanRule) :
    dropLimitMass μ B π ≤ Fintype.card ι := by
  calc
    _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun _ _ => measureReal_le_one
    _ = _ := by simp

/-- Summing the individual finite-stage tail identities gives the exact
quantity certified by the bounded-advice horizon test. -/
theorem sum_tail_probability_eq_sub (μ : Measure Cantor) [IsFiniteMeasure μ]
    (B : AffineBlock) (π : ι → ScanRule) (N : ℕ) :
    (∑ i, μ.real (StoppingTranscript.rankDropTailEvent B (π i) N)) =
      dropLimitMass μ B π - dropMass μ B π N := by
  simp only [tail_probability_eq_sub, Finset.sum_sub_distrib, dropLimitMass, dropMass]

/-- The same pool and the same selected block serve every protected scan. -/
theorem partialLimitMass_le (μ : Measure Cantor) [IsFiniteMeasure μ]
    (B : AffineBlock) (π : ι → ScanRule) (G : Finset ℕ) (hBG : B.support ⊆ G)
    (H : ι → Set Cantor) :
    partialLimitMass μ B π ≤
      (∑ i, μ.real ((π i).observationMap ⁻¹' H i ∩
        {X | 0 < missedCount (π i) G ((π i).observationMap X)})) +
      ∑ i, μ.real ((π i).observationMap ⁻¹' (H i)ᶜ ∩
        LateDropBound.hasDrop B (π i)) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => partial_limit_probability_le μ B (π i) G hBG (H i)

/-- The strict simultaneous score bounds yield the partial-rank limit bound
used by the finite horizon search. -/
theorem partialLimitMass_lt_two_mul (μ : Measure Cantor) [IsFiniteMeasure μ]
    (B : AffineBlock) (π : ι → ScanRule) (G : Finset ℕ) (hBG : B.support ⊆ G)
    (H : ι → Set Cantor) (error : ℝ)
    (hhigh : (∑ i, μ.real ((π i).observationMap ⁻¹' H i ∩
      {X | 0 < missedCount (π i) G ((π i).observationMap X)})) < error)
    (hlow : (∑ i, μ.real ((π i).observationMap ⁻¹' (H i)ᶜ ∩
      LateDropBound.hasDrop B (π i))) < error) :
    partialLimitMass μ B π < 2 * error := by
  have h := partialLimitMass_le μ B π G hBG H
  linarith

/-- Connect exact rational finite-horizon probabilities to the actual
partial-recursive horizon search. Its output bounds the summed first-drop
tails of these scans under this input measure. -/
theorem exists_bounded_advice_search_of_rank_probabilities
    {α : Type*} {error : ℚ} (herror : 0 < error)
    {u v : α → ℕ → ℚ} (input : α)
    (μ : Measure Cantor) [IsProbabilityMeasure μ]
    (B : AffineBlock) (π : ι → ScanRule) (G : Finset ℕ) (hBG : B.support ⊆ G)
    (H : ι → Set Cantor)
    (hu : ∀ n, (u input n : ℝ) = partialMass μ B π n)
    (hv : ∀ n, (v input n : ℝ) = dropMass μ B π n)
    (hhigh : (∑ i, μ.real ((π i).observationMap ⁻¹' H i ∩
      {X | 0 < missedCount (π i) G ((π i).observationMap X)})) < (error : ℝ))
    (hlow : (∑ i, μ.real ((π i).observationMap ⁻¹' (H i)ᶜ ∩
      LateDropBound.hasDrop B (π i))) < (error : ℝ)) :
    ∃ advice, advice ≤ StageHorizon.adviceBound error (Fintype.card ι) ∧
      (StageHorizon.search error u v (input, advice)).Dom ∧
      ∀ horizon, horizon ∈ StageHorizon.search error u v (input, advice) →
        StageHorizon.Accepted error (u input) (v input) advice horizon ∧
        (∑ i, μ.real (StoppingTranscript.rankDropTailEvent B (π i) horizon)) <
          2 * (error : ℝ) := by
  have huconv : Tendsto (fun n => (u input n : ℝ)) atTop (𝓝 (partialLimitMass μ B π)) := by
    simpa only [hu] using tendsto_partialMass μ B π
  have hvconv : Tendsto (fun n => (v input n : ℝ)) atTop (𝓝 (dropLimitMass μ B π)) := by
    simpa only [hv] using tendsto_dropMass μ B π
  obtain ⟨advice, hadvice, hdom, hspec⟩ := StageHorizon.exists_bounded_advice_search herror input
    huconv hvconv (partialLimitMass_lt_two_mul μ B π G hBG H error hhigh hlow).le
    (dropLimitMass_nonneg μ B π) (dropLimitMass_le_card μ B π)
  refine ⟨advice, hadvice, hdom, fun horizon hhorizon => ?_⟩
  obtain ⟨haccepted, htail⟩ := hspec horizon hhorizon
  refine ⟨haccepted, ?_⟩
  rwa [sum_tail_probability_eq_sub, ← hv horizon]

end Klr.StageRankLimit
