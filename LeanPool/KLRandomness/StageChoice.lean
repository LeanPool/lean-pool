/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageWeights
public import LeanPool.KLRandomness.PrefixStage
public import LeanPool.KLRandomness.StageRankAverage
public import LeanPool.KLRandomness.PoolConstruction
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Selecting one sparse candidate for both stage estimates

The wager and rank-loss scores must be averaged over the same complete list.
Choosing an entry separately for the two scores would not prove the stage
construction. This file makes the joint finite averaging step explicit.
-/

@[expose] public section

namespace Klr.StageChoice

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- One candidate simultaneously controls the sum of the two nonnegative
stage costs. Both average hypotheses refer to the same candidate family. -/
theorem exists_combined_score_le {Q ι : Type*} [Fintype Q] [Nonempty Q] [Fintype ι]
    (a b : Q → ι → ℝ) {d W R : ℝ} (hd : 0 ≤ d)
    (ha : (∑ q, ∑ i, a q i) / Fintype.card Q ≤ W)
    (hb : (∑ q, ∑ i, b q i) / Fintype.card Q ≤ R) :
    ∃ q, (∑ i, (a q i + d * b q i)) ≤ W + d * R := by
  classical
  have hcard : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
  have havg : (∑ q, ∑ i, (a q i + d * b q i)) / Fintype.card Q ≤ W + d * R := by
    calc
      _ = (∑ q, ∑ i, a q i) / Fintype.card Q +
          d * ((∑ q, ∑ i, b q i) / Fintype.card Q) := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
      _ ≤ _ := add_le_add ha (mul_le_mul_of_nonneg_left hb hd)
  have hs : (∑ q, ∑ i, (a q i + d * b q i)) ≤ ∑ _q : Q, (W + d * R) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using
      (div_le_iff₀ hcard).mp havg
  obtain ⟨q, _, hq⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hs
  exact ⟨q, hq⟩

/-- A small joint score controls the sum of all wager costs and each rank
cost, because every summand is nonnegative. -/
theorem components_le_of_combined_score_le {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) {d C : ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hd : 0 ≤ d) (h : (∑ i, (a i + d * b i)) ≤ C) :
    (∑ i, a i) ≤ C ∧ ∀ i, d * b i ≤ C := by
  classical
  constructor
  · apply le_trans _ h
    exact Finset.sum_le_sum fun i _ => le_add_of_nonneg_right (mul_nonneg hd (hb i))
  · intro i
    apply le_trans _ h
    apply le_trans (le_add_of_nonneg_left (ha i))
    exact Finset.single_le_sum (fun j _ => add_nonneg (ha j) (mul_nonneg hd (hb j)))
      (Finset.mem_univ i)

/-- A fresh adaptive scan preserves fair coin on complete answer sequences. -/
theorem fairCoin_map_observationMap (π : ScanRule) :
    fairCoin.map π.observationMap = fairCoin := by
  apply measure_eq_of_cylinders
  intro v
  rw [Measure.map_apply π.measurable_observationMap (measurableSet_cylinder v),
    π.observationMap_preimage_cylinder]
  exact (π.fairCoin_transcript v).trans (fairCoin_cylinder v).symm

/-- Conditioning costs at most the reciprocal mass of the condition, also
for events specified in the complete adaptive answer sequence. -/
theorem conditional_observationReal_le (A : Set Cantor) (hA : MeasurableSet A)
    (π : ScanRule) (E : Set Cantor) (hE : MeasurableSet E) :
    (cond fairCoin A).real (π.observationMap ⁻¹' E) ≤
      (fairCoin.real A)⁻¹ * fairCoin.real E := by
  rw [measureReal_def, cond_apply hA, ENNReal.toReal_mul, ENNReal.toReal_inv]
  change (fairCoin.real A)⁻¹ * fairCoin.real (A ∩ π.observationMap ⁻¹' E) ≤ _
  have hpre : fairCoin.real (π.observationMap ⁻¹' E) = fairCoin.real E := by
    rw [← map_measureReal_apply π.measurable_observationMap hE,
      fairCoin_map_observationMap]
  rw [← hpre]
  exact mul_le_mul_of_nonneg_left (measureReal_mono Set.inter_subset_right)
    (inv_nonneg.mpr measureReal_nonneg)

/-- The reciprocal mass of the previous equations is exactly two to their
total row rank. -/
theorem prefixEvent_inverse_real (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) (n : ℕ) :
    (fairCoin.real (PrefixStage.prefixEvent B n))⁻¹ =
      (2 : ℝ) ^ (∑ k : Fin n, (B k).rank) := by
  change (fairCoin (AffineBlock.familyEvent (PrefixStage.prefixFamily B n))).toReal⁻¹ = _
  rw [AffineBlock.fairCoin_familyEvent _ (PrefixStage.prefixFamily_pairwise B hdis n)]
  simp only [ENNReal.toReal_prod, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_ofNat, PrefixStage.prefixFamily]
  rw [Finset.prod_pow_eq_pow_sum, ← inv_pow]
  norm_num

/-- Every earlier finite-stage law obeys the same answer-event density
bound, with the total rank of the current prefix. -/
theorem prefixLaw_observationReal_le (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (n a : ℕ) (ha : a ≤ n) (π : ScanRule) (E : Set Cantor) (hE : MeasurableSet E) :
    (PrefixStage.law B a).real (π.observationMap ⁻¹' E) ≤
      (2 : ℝ) ^ (∑ k : Fin n, (B k).rank) * fairCoin.real E := by
  have hmass : fairCoin.real (PrefixStage.prefixEvent B n) ≤
      fairCoin.real (PrefixStage.prefixEvent B a) :=
    measureReal_mono (PrefixStage.prefixEvent_antitone B ha)
  have hpos : 0 < fairCoin.real (PrefixStage.prefixEvent B n) :=
    ENNReal.toReal_pos (PrefixStage.fairCoin_prefixEvent_ne_zero B hdis n)
      (measure_ne_top _ _)
  have hinv : (fairCoin.real (PrefixStage.prefixEvent B a))⁻¹ ≤
      (fairCoin.real (PrefixStage.prefixEvent B n))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hpos hmass
  calc
    _ ≤ (fairCoin.real (PrefixStage.prefixEvent B a))⁻¹ * fairCoin.real E :=
      conditional_observationReal_le _ (PrefixStage.measurableSet_prefixEvent B a) π E hE
    _ ≤ (fairCoin.real (PrefixStage.prefixEvent B n))⁻¹ * fairCoin.real E :=
      mul_le_mul_of_nonneg_right hinv measureReal_nonneg
    _ = _ := by rw [prefixEvent_inverse_real B hdis n]

/-- The pool positions in the original order returned by the pool program. -/
def poolLabel (G : List ℕ) {M : ℕ} (hG : G.length = M) : Fin M → ℕ :=
  fun i => G.get (Fin.cast hG.symm i)

theorem poolLabel_injective (G : List ℕ) {M : ℕ} (hG : G.length = M) (hn : G.Nodup) :
    Function.Injective (poolLabel G hG) := by
  intro i j hij
  have h := hn.injective_get hij
  exact Fin.ext (congrArg (fun k : Fin G.length => k.val) h)

theorem poolLabel_image_univ (G : List ℕ) {M : ℕ} (hG : G.length = M) :
    Finset.univ.image (poolLabel G hG) = G.toFinset := by
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset]
  constructor
  · rintro ⟨i, rfl⟩
    exact List.get_mem G _
  · intro ha
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
    exact ⟨Fin.cast hG i, by simpa [poolLabel] using hi⟩

/-- Expected total absolute normalized wager on a candidate's actual support. -/
noncomputable def wagerCost (μ : Measure Cantor) (s : BettingStrategy)
    (B : AffineBlock) : ℝ :=
  ∫ X, StageWeights.supportWager s.normalize.scan s.normalize.capital.wager B.support X ∂μ

/-- Fair-coin probability of a rank drop on the low part of the answer space. -/
noncomputable def lowDropCost (Low : Set Cantor) (s : BettingStrategy)
    (B : AffineBlock) : ℝ :=
  fairCoin.real (Low ∩ (NoDrop.noDropTranscripts B s.normalize.scan)ᶜ)

theorem wagerCost_nonneg (μ : Measure Cantor) (s : BettingStrategy) (B : AffineBlock) :
    0 ≤ wagerCost μ s B :=
  integral_nonneg fun X => StageWeights.supportWager_nonneg _ _ _ X

theorem lowDropCost_nonneg (Low : Set Cantor) (s : BettingStrategy) (B : AffineBlock) :
    0 ≤ lowDropCost Low s B := measureReal_nonneg

/-- The candidate-selection wager cost is independent of its syndrome. -/
theorem wagerCost_listBlock_syndrome_irrel
    {M m r J : ℕ} {τ θ : ℚ} {L : SparseListSearch.CodeList}
    (hL : SparseListSearch.Good M m r J τ θ L)
    (e : Fin M → ℕ) (he : Function.Injective e)
    (y y' : Fin L.length → Fin r → ZMod 2) (j : Fin L.length)
    (μ : Measure Cantor) (s : BettingStrategy) :
    wagerCost μ s (StageRank.listBlock hL e he y j) =
      wagerCost μ s (StageRank.listBlock hL e he y' j) := rfl

/-- Full unread rank depends on the linear map, so the low-drop cost is
independent of the syndrome chosen later in the stage construction. -/
theorem lowDropCost_listBlock_syndrome_irrel
    {M m r J : ℕ} {τ θ : ℚ} {L : SparseListSearch.CodeList}
    (hL : SparseListSearch.Good M m r J τ θ L)
    (e : Fin M → ℕ) (he : Function.Injective e)
    (y y' : Fin L.length → Fin r → ZMod 2) (j : Fin L.length)
    (Low : Set Cantor) (s : BettingStrategy) :
    lowDropCost Low s (StageRank.listBlock hL e he y j) =
      lowDropCost Low s (StageRank.listBlock hL e he y' j) := rfl

/-- The concrete sparse list contains one candidate controlling the wager
and low-part rank-drop costs for the entire protected family at once. -/
theorem exists_candidate_joint_bound {ι : Type*} [Fintype ι]
    (μ : Measure Cantor) [IsProbabilityMeasure μ]
    {M m r J : ℕ} {τ θ : ℚ} {L : SparseListSearch.CodeList}
    (hL : SparseListSearch.Good M m r J τ θ L) (hJ : 0 < J) (hθ : 0 ≤ θ)
    (e : Fin M → ℕ) (he : Function.Injective e)
    (y : Fin L.length → Fin r → ZMod 2)
    (s : ι → BettingStrategy) (Low : ι → Set Cantor)
    (hLow : ∀ i, MeasurableSet (Low i)) (η : ℝ)
    (hpool : ∀ i, fairCoin.real {Z | Z ∈ Low i ∧
      (PoolQuery.missedCount (s i).normalize.scan (Finset.univ.image e) Z : ℝ) <
        (τ : ℝ) * M} ≤ η) {d : ℝ} (hd : 0 ≤ d) :
    ∃ j : Fin L.length,
      (∑ i, (wagerCost μ (s i) (StageRank.listBlock hL e he y j) +
        d * lowDropCost (Low i) (s i) (StageRank.listBlock hL e he y j))) ≤
      (Fintype.card ι : ℝ) *
        ((2 * ((m : ℝ) / M)) * Real.sqrt ((M : ℝ) / 2) + d * (η + (θ : ℝ))) := by
  classical
  let a (j : Fin L.length) (i : ι) := wagerCost μ (s i) (StageRank.listBlock hL e he y j)
  let b (j : Fin L.length) (i : ι) := lowDropCost (Low i) (s i) (StageRank.listBlock hL e he y j)
  have hlen : 0 < L.length := by simpa only [hL.1] using hJ
  let : Nonempty (Fin L.length) := ⟨⟨0, hlen⟩⟩
  have ha : (∑ j, ∑ i, a j i) / Fintype.card (Fin L.length) ≤
      (Fintype.card ι : ℝ) * ((2 * ((m : ℝ) / M)) * Real.sqrt ((M : ℝ) / 2)) := by
    simpa only [a, wagerCost, StageRank.listBlock, StageCandidate.block_support,
      Fintype.card_fin, hL.1] using
      StageWeights.average_integral_normalized_supportWager_le μ hL hJ s e he
  have hb : (∑ j, ∑ i, b j i) / Fintype.card (Fin L.length) ≤
      (Fintype.card ι : ℝ) * (η + (θ : ℝ)) := by
    have hcard : Fintype.card (Fin L.length) = J := by simpa only [Fintype.card_fin] using hL.1
    rw [hcard, Finset.sum_comm, Finset.sum_div]
    calc
      _ ≤ ∑ _i : ι, (η + (θ : ℝ)) := Finset.sum_le_sum fun i _ =>
        StageRank.average_measureReal_low_hasDrop_le hL hJ hθ e he y
          (s i).normalize.scan (Low i) (hLow i) η (hpool i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  obtain ⟨j, hj⟩ := exists_combined_score_le a b hd ha hb
  refine ⟨j, hj.trans_eq ?_⟩
  ring

/-- Actual accepted pool data discharge the low-part hypothesis of the
joint candidate choice. The list order supplies the injective pool labels. -/
theorem exists_candidate_joint_bound_of_goodPool
    (μ : Measure Cantor) [IsProbabilityMeasure μ]
    {M m r J ℓ z : ℕ} {τ θ : ℚ} {L : SparseListSearch.CodeList} {G : List ℕ}
    (hL : SparseListSearch.Good M m r J τ θ L) (hJ : 0 < J) (hθ : 0 ≤ θ)
    (s : ℕ → BettingStrategy) (H : ℕ → Set Cantor)
    (hH : ∀ i < ℓ, MeasurableSet (H i)) (η : ℝ)
    (hG : PoolConstruction.GoodPool (fun i => (s i).normalize.scan) H ℓ η z τ M G)
    (y : Fin L.length → Fin r → ZMod 2) {d : ℝ} (hd : 0 ≤ d) :
    ∃ j : Fin L.length,
      (∑ i : Fin ℓ,
        (wagerCost μ (s i) (StageRank.listBlock hL (poolLabel G hG.1)
          (poolLabel_injective G hG.1 hG.2.1) y j) +
        d * lowDropCost (H i)ᶜ (s i) (StageRank.listBlock hL (poolLabel G hG.1)
          (poolLabel_injective G hG.1 hG.2.1) y j))) ≤
      (ℓ : ℝ) *
        ((2 * ((m : ℝ) / M)) * Real.sqrt ((M : ℝ) / 2) + d * (η + (θ : ℝ))) := by
  have hpool (i : Fin ℓ) : fairCoin.real {Z | Z ∈ (H i)ᶜ ∧
      (PoolQuery.missedCount (s i).normalize.scan (Finset.univ.image (poolLabel G hG.1)) Z : ℝ) <
        (τ : ℝ) * M} ≤ η := by
    rw [poolLabel_image_univ]
    exact (hG.2.2.2 i i.isLt).2.le
  simpa only [Fintype.card_fin] using exists_candidate_joint_bound μ hL hJ hθ
    (poolLabel G hG.1) (poolLabel_injective G hG.1 hG.2.1) y
    (fun i : Fin ℓ => s i) (fun i : Fin ℓ => (H i)ᶜ)
    (fun i => (hH i i.isLt).compl) η hpool hd

/-- The selected joint score bounds all the low-drop probabilities under
every earlier stage law, as well as the total expected wager cost. -/
theorem prior_stage_costs_le_of_joint_bound {ι : Type*} [Fintype ι]
    (μ : Measure Cantor) (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (n : ℕ) (s : ι → BettingStrategy) (Low : ι → Set Cantor)
    (hLow : ∀ i, MeasurableSet (Low i)) (C : AffineBlock) {ε : ℝ}
    (hscore : (∑ i, (wagerCost μ (s i) C +
      (2 : ℝ) ^ (∑ k : Fin n, (B k).rank) * lowDropCost (Low i) (s i) C)) ≤ ε) :
    (∑ i, wagerCost μ (s i) C) ≤ ε ∧
      ∀ i a, a ≤ n → (PrefixStage.law B a).real
        ((s i).normalize.scan.observationMap ⁻¹'
          (Low i ∩ (NoDrop.noDropTranscripts C (s i).normalize.scan)ᶜ)) ≤ ε := by
  have hcomp := components_le_of_combined_score_le
    (fun i => wagerCost μ (s i) C) (fun i => lowDropCost (Low i) (s i) C)
    (fun i => wagerCost_nonneg μ (s i) C) (fun i => lowDropCost_nonneg (Low i) (s i) C)
    (by positivity) hscore
  refine ⟨hcomp.1, ?_⟩
  intro i a ha
  exact (prefixLaw_observationReal_le B hdis n a ha (s i).normalize.scan _
    ((hLow i).inter (NoDrop.measurableSet_noDropTranscripts _ _).compl)).trans (hcomp.2 i)

/-- Every positive-rank candidate inside a good pool has small high-part
no-drop mass; this estimate requires no further candidate selection. -/
theorem high_noDrop_measureReal_lt_of_goodPool
    {M ℓ z : ℕ} {τ : ℚ} {G : List ℕ} {η : ℝ}
    {π : ℕ → ScanRule} {H : ℕ → Set Cantor}
    (hG : PoolConstruction.GoodPool π H ℓ η z τ M G)
    (C : AffineBlock) (hCG : C.support ⊆ G.toFinset) (hr : 0 < C.rank)
    (i : ℕ) (hi : i < ℓ) :
    fairCoin.real (H i ∩ NoDrop.noDropTranscripts C (π i)) < η := by
  have hsub : H i ∩ NoDrop.noDropTranscripts C (π i) ⊆
      {Z | Z ∈ H i ∧ ∃ b ∈ G, ¬ PoolQuery.Reads (π i) b Z} := by
    intro Z hZ
    have hmiss := StageRank.noDropTranscripts_subset_missed C (π i) G.toFinset hCG hr hZ.2
    obtain ⟨b, hb, hnb⟩ := (PoolQuery.missedCount_pos_iff (π i) G.toFinset Z).mp hmiss
    exact ⟨hZ.1, b, List.mem_toFinset.mp hb, hnb⟩
  exact (measureReal_mono hsub).trans_lt (hG.2.2.2 i hi).1

end Klr.StageChoice
