/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Entropy.ComplexHierarchySeparationRates

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication.Foundation.StageHierarchyResources

open Filter HierarchySeparationRates LabelHierarchyCounts
open scoped BigOperators Topology

universe u v

local instance (priority := low) {B : Type*} : DecidableEq B := Classical.decEq B

variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

def stageRefinementCount (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (n t : ℕ) : ℕ :=
  refinementCount (sourcePrefixCounts (fun a => t * counts a) labels) n

def stageNodeCounts (counts : A → ℕ) (labels : ∀ n, A → Label n) (n : ℕ)
    (r : LabelRecord Label n) (s : Label n) : ℕ :=
  sourcePrefixCounts counts labels (n + 1) (r, s)

theorem stageRefinementCount_eq_nodeProduct (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (n t : ℕ) :
    stageRefinementCount counts labels n t =
      pairingProduct (stageNodeCounts counts labels n) t := by
  unfold stageRefinementCount refinementCount pairingProduct
  apply Finset.prod_congr rfl
  intro r hr
  change Nat.multinomial Finset.univ
      (fun s : Label n => sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s)) =
    Nat.multinomial Finset.univ
      (fun s : Label n => t * sourcePrefixCounts counts labels (n + 1) (r, s))
  apply Nat.multinomial_congr
  intro s hs
  exact sourcePrefixCounts_mul counts labels t (n + 1) (r, s)

theorem stageRefinementCount_eq_sourcePoolProduct (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ) (n : Fin depth) (t : ℕ) :
    stageRefinementCount counts labels n.val t =
      ∏ r : LabelRecord Label n.val,
        poolTypeCount (sourcePoolCounts counts labels depth) ⟨n, r⟩ t :=
  stageRefinementCount_eq_nodeProduct counts labels n.val t

theorem stageRefinementCount_pos (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (n t : ℕ) : 0 < stageRefinementCount counts labels n t := by
  unfold stageRefinementCount refinementCount
  exact Finset.prod_pos (fun r _ => Nat.multinomial_pos _ _)

theorem stageConditionalWords_card {Position : Type*} [Fintype Position]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ)
    (w : Position → LabelRecord Label n)
    (hword : ∀ r, wordPopulation w r = sourcePrefixCounts (fun a => t * counts a) labels n r) :
    Fintype.card (ConditionalWords w
      (fun r s => sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s))) =
      stageRefinementCount counts labels n t := by
  exact conditionalWords_card w
    (fun r s => sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s))
    (fun r => (hword r).trans
      (sourcePrefixCounts_compatible (fun a => t * counts a) labels n r))

theorem stageConditionalPool_card {Position : Type*} [Fintype Position]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ)
    (w : Position → LabelRecord Label n)
    (hword : ∀ r, wordPopulation w r = sourcePrefixCounts (fun a => t * counts a) labels n r) :
    (Finset.univ.filter (fun fine : Position → Label n =>
      ∀ r s, Fintype.card {i // w i = r ∧ fine i = s} =
        sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s))).card =
      stageRefinementCount counts labels n t := by
  simpa only [ConditionalWords, Fintype.card_subtype] using
    stageConditionalWords_card counts labels n t w hword

omit [∀ n, Fintype (Label n)] in
theorem stageConditionalWords_nonempty [∀ n, Finite (Label n)] {Position : Type*} [Fintype Position]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ)
    (w : Position → LabelRecord Label n)
    (hword : ∀ r, wordPopulation w r = sourcePrefixCounts (fun a => t * counts a) labels n r) :
    Nonempty (ConditionalWords w
      (fun r s => sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s))) := by
  classical
  let : ∀ n, Fintype (Label n) := fun n => Fintype.ofFinite (Label n)
  apply Fintype.card_pos_iff.mp
  rw [stageConditionalWords_card counts labels n t w hword]
  exact stageRefinementCount_pos counts labels n t

def stageEntropyRate (counts : A → ℕ) (labels : ∀ n, A → Label n) (n : ℕ) : ℝ :=
  poolEntropyTotal (stageNodeCounts counts labels n)

theorem stageEntropyRate_nonneg (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (n : ℕ) : 0 ≤ stageEntropyRate counts labels n := by
  exact Finset.sum_nonneg (fun r _ => populationEntropyRate_nonneg
    (stageNodeCounts counts labels n r))

theorem tendsto_log_stageRefinementCount_div (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (n : ℕ) :
    Tendsto (fun t : ℕ => Real.log (stageRefinementCount counts labels n t : ℝ) / (t : ℝ))
      atTop (𝓝 (stageEntropyRate counts labels n)) := by
  simpa only [stageRefinementCount_eq_nodeProduct, stageEntropyRate] using
    tendsto_log_pairingProduct_div (stageNodeCounts counts labels n)

def stageCost (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ) : ℕ :=
  LabelHierarchySeparation.poolAuxiliaryCost (stageRefinementCount counts labels n t)

theorem tendsto_log_stageCost_div (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (n : ℕ) :
    Tendsto (fun t : ℕ => Real.log (stageCost counts labels n t : ℝ) / (t : ℝ))
      atTop (𝓝 (stageEntropyRate counts labels n)) :=
  LabelHierarchySeparation.tendsto_log_poolAuxiliaryCost_div_nat
    (stageRefinementCount_pos counts labels n) (stageEntropyRate_nonneg counts labels n)
    (tendsto_log_stageRefinementCount_div counts labels n)

def stagePairingProduct (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) : ℕ :=
  ∏ n : Fin depth, stageRefinementCount counts labels n.val t

def stageAuxiliaryBudget (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) : ℕ :=
  ∏ n : Fin depth, stageCost counts labels n.val t

theorem stagePairingProduct_succ (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (n t : ℕ) :
    stagePairingProduct counts labels (n + 1) t =
      stagePairingProduct counts labels n t * stageRefinementCount counts labels n t := by
  exact Fin.prod_univ_castSucc
    (fun i : Fin (n + 1) => stageRefinementCount counts labels i.val t)

theorem stageAuxiliaryBudget_succ (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (n t : ℕ) :
    stageAuxiliaryBudget counts labels (n + 1) t =
      stageAuxiliaryBudget counts labels n t * stageCost counts labels n t := by
  exact Fin.prod_univ_castSucc
    (fun i : Fin (n + 1) => stageCost counts labels i.val t)

theorem stagePairingProduct_eq_exactWords_card (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) (t : ℕ) :
    stagePairingProduct counts labels depth t =
      Fintype.card (ExactWords (fun a => t * counts a)) := by
  unfold stagePairingProduct stageRefinementCount
  rw [Fin.prod_univ_eq_prod_range]
  exact source_refinementCount_product_eq_exactWords_card
    (fun a => t * counts a) labels depth hinjective

theorem stagePairingProduct_le_budget (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth t : ℕ) :
    stagePairingProduct counts labels depth t ≤ stageAuxiliaryBudget counts labels depth t := by
  exact Finset.prod_le_prod (fun n _ =>
    LabelHierarchySeparation.population_le_poolAuxiliaryCost
      (stageRefinementCount counts labels n.val t))

theorem stageAuxiliaryBudget_pos (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth t : ℕ) :
    0 < stageAuxiliaryBudget counts labels depth t := by
  exact Finset.prod_pos (fun n _ => LabelHierarchySeparation.poolAuxiliaryCost_pos
    (stageRefinementCount counts labels n.val t))

abbrev StageAuxiliaryCoordinates (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) :=
  ∀ n : Fin depth,
    LabelHierarchySeparation.PoolAuxiliaryGroup (stageRefinementCount counts labels n.val t)

def stageAuxiliaryTensor (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) :
    Tensor ℂ (StageAuxiliaryCoordinates counts labels depth t)
      (StageAuxiliaryCoordinates counts labels depth t)
      (StageAuxiliaryCoordinates counts labels depth t) :=
  LabelHierarchySeparation.bankTensor (fun n : Fin depth =>
    LabelHierarchySeparation.poolAuxiliaryTensor (stageRefinementCount counts labels n.val t))

theorem stageAuxiliaryTensor_rankAtMost (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth t : ℕ) :
    Tensor.RankAtMost (stageAuxiliaryTensor counts labels depth t)
      (stageAuxiliaryBudget counts labels depth t) := by
  exact LabelHierarchySeparation.bankTensor_rankAtMost
    (fun n : Fin depth => LabelHierarchySeparation.poolAuxiliaryTensor
      (stageRefinementCount counts labels n.val t))
    (fun n => stageCost counts labels n.val t)
    (fun n => LabelHierarchySeparation.poolAuxiliaryTensor_rankAtMost
      (stageRefinementCount counts labels n.val t))

theorem stageAuxiliaryTensor_borderRankAtMost (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth t : ℕ) :
    Tensor.BorderRankAtMost (stageAuxiliaryTensor counts labels depth t)
      (stageAuxiliaryBudget counts labels depth t) :=
  (stageAuxiliaryTensor_rankAtMost counts labels depth t).borderRankAtMost

abbrev StagePairingCoordinates (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) := ∀ n : Fin depth, Fin (stageRefinementCount counts labels n.val t)

theorem card_stagePairingCoordinates (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth t : ℕ) :
    Fintype.card (StagePairingCoordinates counts labels depth t) =
      stagePairingProduct counts labels depth t := by
  simp only [StagePairingCoordinates, Fintype.card_pi, Fintype.card_fin, stagePairingProduct]

theorem sum_stageEntropyRate_eq_nodeEntropyTotal (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ) :
    (∑ n : Fin depth, stageEntropyRate counts labels n.val) =
      poolEntropyTotal (sourcePoolCounts counts labels depth) := by
  simp only [stageEntropyRate, poolEntropyTotal, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro r hr
  rfl

theorem sum_stageEntropyRate_eq_source (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    (∑ n : Fin depth, stageEntropyRate counts labels n.val) = populationEntropyRate counts := by
  rw [sum_stageEntropyRate_eq_nodeEntropyTotal]
  exact source_poolEntropyTotal_eq counts labels depth hinjective

theorem tendsto_log_stageAuxiliaryBudget_div (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    Tendsto (fun t : ℕ => Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) / (t : ℝ))
      atTop (𝓝 (populationEntropyRate counts)) := by
  have h := Separation.tendsto_log_nat_prod_div_nat (I := Fin depth) Finset.univ
    (fun n _ t => LabelHierarchySeparation.poolAuxiliaryCost_pos
      (stageRefinementCount counts labels n.val t))
    (fun n _ => tendsto_log_stageCost_div counts labels n.val)
  simpa only [stageAuxiliaryBudget, stageCost,
    sum_stageEntropyRate_eq_source counts labels depth hinjective] using h

theorem tendsto_log_stagePairingProduct (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    Tendsto
      (fun t : ℕ => Real.log (stagePairingProduct counts labels depth t : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  simpa only [stagePairingProduct_eq_exactWords_card counts labels depth hinjective] using
    tendsto_log_exactWords_card_mul counts hD

theorem tendsto_log_stageAuxiliaryBudget (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    Tendsto
      (fun t : ℕ => Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  have hmain : populationEntropyRate counts / (∑ a, counts a : ℕ) =
      finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) := by
    unfold populationEntropyRate
    exact mul_div_cancel_left₀ _ hD'
  simpa only [div_div, hmain] using
    (tendsto_log_stageAuxiliaryBudget_div counts labels depth hinjective).div_const
      ((∑ a, counts a : ℕ) : ℝ)

theorem source_stage_resource_rates (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    (∀ t, Tensor.RankAtMost (stageAuxiliaryTensor counts labels depth t)
      (stageAuxiliaryBudget counts labels depth t)) ∧
      (∀ t, stagePairingProduct counts labels depth t =
        Fintype.card (ExactWords (fun a => t * counts a))) ∧
      (∀ t, stagePairingProduct counts labels depth t ≤
        stageAuxiliaryBudget counts labels depth t) ∧
      Tendsto
        (fun t : ℕ => Real.log (stagePairingProduct counts labels depth t : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) ∧
      Tendsto
        (fun t : ℕ => Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) :=
  ⟨stageAuxiliaryTensor_rankAtMost counts labels depth,
    stagePairingProduct_eq_exactWords_card counts labels depth hinjective,
    stagePairingProduct_le_budget counts labels depth,
    tendsto_log_stagePairingProduct counts hD labels depth hinjective,
    tendsto_log_stageAuxiliaryBudget counts hD labels depth hinjective⟩

end MatrixMultiplication.Foundation.StageHierarchyResources

end

end MatrixMultiplicationAllFields
