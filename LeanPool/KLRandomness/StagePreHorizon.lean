/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageChoice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A genuine stage candidate before choosing a horizon

The Borel high sets are fixed once for the full scan family. At one stage,
a positive rational error, a rational density, and a pool-producing program
are fixed before the trial rank varies. For all sufficiently large ranks,
the actual pool program and the actual sparse-list construction both halt.
One list entry then has small wager and low-rank-drop costs simultaneously.
The bounds hold for every subsequent syndrome and every earlier stage law.
-/

@[expose] public section

namespace Klr.StagePreHorizon

open Filter MeasureTheory StageChoice
open scoped BigOperators Topology

/-- The high-part event that at least one position of the actual pool is
never queried on the complete prescribed answer sequence. -/
def highPoolMiss (π : ScanRule) (H : Set Cantor) (G : List ℕ) : Set Cantor :=
  {Z | Z ∈ H ∧ ∃ b ∈ G, ¬ PoolQuery.Reads π b Z}

theorem measurableSet_highPoolMiss (π : ScanRule) (H : Set Cantor)
    (hH : MeasurableSet H) (G : List ℕ) : MeasurableSet (highPoolMiss π H G) := by
  have he : highPoolMiss π H G =
      H ∩ {Z | (0 : ℝ) < (PoolQuery.missedCount π G.toFinset Z : ℝ)} := by
    ext Z
    simp [highPoolMiss, PoolQuery.missedCount_pos_iff]
  rw [he]
  exact hH.inter (measurableSet_lt measurable_const (StageRank.measurable_missedCount_real π _))

/-- A low-part rank drop pulled back from answers to the actual input. -/
noncomputable def lowDropInput (s : BettingStrategy) (H : Set Cantor)
    (C : AffineBlock) : Set Cantor :=
  s.normalize.scan.observationMap ⁻¹'
    (Hᶜ ∩ (NoDrop.noDropTranscripts C s.normalize.scan)ᶜ)

/-- A high-part missed pool pulled back to the actual input. -/
noncomputable def highMissInput (s : BettingStrategy) (H : Set Cantor) (G : List ℕ) : Set Cantor :=
  s.normalize.scan.observationMap ⁻¹' highPoolMiss s.normalize.scan H G

/-- Embed the selected executable entry in the concrete output pool. -/
noncomputable def candidate {τ θ : ℚ} {r : ℕ} {G : List ℕ}
    {L : SparseListSearch.CodeList} (hGM : G.length = SparseParameters.blockSize r)
    (hG : G.Nodup) (hL : L ∈ SparseListConstruction.construct τ θ r)
    (q : Fin L.length) (y : Fin r → ZMod 2) : AffineBlock :=
  StageRank.listBlock (SparseListConstruction.construct_spec hL)
    (poolLabel G hGM) (poolLabel_injective G hGM hG) (fun _ => y) q

@[simp] theorem candidate_rank {τ θ : ℚ} {r : ℕ} {G : List ℕ}
    {L : SparseListSearch.CodeList} (hGM : G.length = SparseParameters.blockSize r)
    (hG : G.Nodup) (hL : L ∈ SparseListConstruction.construct τ θ r)
    (q : Fin L.length) (y : Fin r → ZMod 2) :
    (candidate hGM hG hL q y).rank = r := rfl

theorem candidate_support_subset {τ θ : ℚ} {r : ℕ} {G : List ℕ}
    {L : SparseListSearch.CodeList} (hGM : G.length = SparseParameters.blockSize r)
    (hG : G.Nodup) (hL : L ∈ SparseListConstruction.construct τ θ r)
    (q : Fin L.length) (y : Fin r → ZMod 2) :
    (candidate hGM hG hL q y).support ⊆ G.toFinset := by
  rw [← poolLabel_image_univ G hGM]
  change (SparseListWeights.support (SparseParameters.blockSize r) (L.get q)).image
    (poolLabel G hGM) ⊆ _
  exact Finset.image_subset_image (Finset.subset_univ _)

/-- A strict joint score controls the entire protected sum under each old
law; no extra factor for the number of scans is lost in this step. -/
theorem sums_lt_of_joint_score (s : ℕ → BettingStrategy) (H : ℕ → Set Cantor)
    (hH : ∀ i, MeasurableSet (H i)) (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (n : ℕ) (C : AffineBlock) {ε : ℝ}
    (hscore : (∑ i : Fin (n + 1),
      (wagerCost (PrefixStage.law B n) (s i) C +
        (2 : ℝ) ^ (∑ k : Fin n, (B k).rank) * lowDropCost (H i)ᶜ (s i) C)) < ε) :
    (∑ i : Fin (n + 1), wagerCost (PrefixStage.law B n) (s i) C) < ε ∧
      ∀ a ≤ n, (∑ i : Fin (n + 1),
        (PrefixStage.law B a).real (lowDropInput (s i) (H i) C)) < ε := by
  constructor
  · apply lt_of_le_of_lt _ hscore
    exact Finset.sum_le_sum fun i _ =>
      le_add_of_nonneg_right (mul_nonneg (by positivity) (lowDropCost_nonneg _ _ _))
  · intro a ha
    apply lt_of_le_of_lt _ hscore
    apply Finset.sum_le_sum
    intro i _
    exact (prefixLaw_observationReal_le B hdis n a ha (s i).normalize.scan _
      ((hH i).compl.inter (NoDrop.measurableSet_noDropTranscripts _ _).compl)).trans
        (le_add_of_nonneg_left (wagerCost_nonneg _ _ _))

/-- Good pools control the protected high-part missed-pool sum under every
earlier conditional law, with the same prefix-rank density factor. -/
theorem highMiss_sum_lt_of_goodPool (s : ℕ → BettingStrategy) (H : ℕ → Set Cantor)
    (hH : ∀ i, MeasurableSet (H i)) (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (n : ℕ) {z M : ℕ} {τ : ℚ} {η : ℝ} {G : List ℕ}
    (hG : PoolConstruction.GoodPool (fun i => (s i).normalize.scan) H (n + 1) η z τ M G)
    (a : ℕ) (ha : a ≤ n) :
    (∑ i : Fin (n + 1), (PrefixStage.law B a).real (highMissInput (s i) (H i) G)) <
      ((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (∑ k : Fin n, (B k).rank) * η := by
  have hsum : (∑ i : Fin (n + 1), fairCoin.real (highPoolMiss (s i).normalize.scan (H i) G)) <
      ((n + 1 : ℕ) : ℝ) * η := by
    simpa only [highPoolMiss, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using
      Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin (n + 1))))
        Finset.univ_nonempty (fun i _ => (hG.2.2.2 i i.isLt).1)
  calc
    _ ≤ ∑ i : Fin (n + 1),
        (2 : ℝ) ^ (∑ k : Fin n, (B k).rank) *
          fairCoin.real (highPoolMiss (s i).normalize.scan (H i) G) :=
      Finset.sum_le_sum fun i _ =>
        prefixLaw_observationReal_le B hdis n a ha (s i).normalize.scan _
          (measurableSet_highPoolMiss _ _ (hH i) G)
    _ = (2 : ℝ) ^ (∑ k : Fin n, (B k).rank) *
        ∑ i : Fin (n + 1), fairCoin.real (highPoolMiss (s i).normalize.scan (H i) G) :=
      (Finset.mul_sum _ _ _).symm
    _ < (2 : ℝ) ^ (∑ k : Fin n, (B k).rank) * (((n + 1 : ℕ) : ℝ) * η) :=
      mul_lt_mul_of_pos_left hsum (by positivity)
    _ = _ := by ring

/-- Pool sizes tend to infinity along the paper's rank parameter. -/
theorem tendsto_blockSize_nat : Tendsto SparseParameters.blockSize atTop atTop := by
  exact tendsto_pow_atTop (α := ℕ) (by decide : 8 ≠ 0)

/-- Fixed partitions, fixed rational thresholds and one fixed pool program
produce actual stage candidates at every sufficiently large trial rank.

The index is shorter than `r^24`, and all estimates hold for every syndrome
chosen later. The protected family is exactly the first `n + 1` strategies. -/
theorem exists_fixed_partitions_eventual_candidates (s : ℕ → BettingStrategy) :
    ∃ H : ℕ → Set Cantor, (∀ i, MeasurableSet (H i)) ∧
      ∀ (B : ℕ → AffineBlock),
        Pairwise (fun i j => Disjoint (B i).support (B j).support) →
        ∀ (n z : ℕ) (ε : ℝ), 0 < ε →
          ∃ η : ℚ, 0 < η ∧
            ((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (∑ k : Fin n, (B k).rank) *
              ((η : ℝ) + η) < ε / 2 ∧
          ∃ τ : ℚ, 0 < τ ∧ τ < 1 / 4 ∧
          ∃ e : Nat.Partrec.Code, ∀ᶠ r : ℕ in atTop,
            ∃ (G : List ℕ) (L : SparseListSearch.CodeList)
              (hG : PoolConstruction.GoodPool (fun i => (s i).normalize.scan)
                H (n + 1) (η : ℝ) z τ (SparseParameters.blockSize r) G)
              (hL : L ∈ SparseListConstruction.construct τ η r),
              PoolAdvice.encodePool G ∈ e.eval (SparseParameters.blockSize r) ∧
              ∃ q : Fin L.length, 0 < r ∧ q.val < r ^ 24 ∧
                (∀ a ≤ n, (∑ i : Fin (n + 1),
                  (PrefixStage.law B a).real (highMissInput (s i) (H i) G)) < ε) ∧
                ∀ y : Fin r → ZMod 2,
                  (∑ i : Fin (n + 1), wagerCost (PrefixStage.law B n) (s i)
                    (candidate hG.1 hG.2.1 hL q y)) < ε ∧
                  ∀ a ≤ n, (∑ i : Fin (n + 1), (PrefixStage.law B a).real
                    (lowDropInput (s i) (H i) (candidate hG.1 hG.2.1 hL q y))) < ε := by
  obtain ⟨H, hH, hpool⟩ := PoolConstruction.exists_fixed_partitions_computable_pools
    (fun i => (s i).normalize.scan)
  refine ⟨H, hH, ?_⟩
  intro B hdis n z ε hε
  let d : ℝ := (2 : ℝ) ^ (∑ k : Fin n, (B k).rank)
  let c : ℝ := ((n + 1 : ℕ) : ℝ) * d
  have hd : 0 < d := by dsimp [d]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨η, hη0, hηsmall⟩ := exists_rat_btwn (show (0 : ℝ) < ε / (4 * c) by positivity)
  have hη : (0 : ℚ) < η := by exact_mod_cast hη0
  have hsmall : c * (η : ℝ) < ε / 4 := by
    have ht := (lt_div_iff₀ (show (0 : ℝ) < 4 * c by positivity)).mp hηsmall
    nlinarith
  have hbudget : c * ((η : ℝ) + η) < ε / 2 := by nlinarith
  have hhigh : c * (η : ℝ) < ε := hsmall.trans (by linarith)
  obtain ⟨τ, hτ, hτquarter, e, he⟩ := hpool (n + 1) (η : ℝ) hη0 z
  refine ⟨η, hη, hbudget, τ, hτ, hτquarter, e, ?_⟩
  have hpools := tendsto_blockSize_nat.eventually he
  have hlists := SparseListConstruction.eventually_construct_good τ η hτ hη
  have hwager := StageWeights.eventually_family_supportWager_bound_lt (n + 1)
    (show 0 < ε / 2 by positivity)
  filter_upwards [hpools, hlists, hwager, eventually_ge_atTop 1] with r hpr hlr hwr hr
  obtain ⟨G, hGeval, hG⟩ := hpr
  obtain ⟨L, hL, hgood⟩ := hlr
  have hrpos : 0 < r := hr
  have hJ : 0 < SparseParameters.listSize r := by
    unfold SparseParameters.listSize SparseParameters.blockSize
    positivity
  let := PrefixStage.law_isProbabilityMeasure B hdis n
  obtain ⟨q, hq⟩ := exists_candidate_joint_bound_of_goodPool (PrefixStage.law B n)
    hgood hJ hη.le s H (fun i _ => hH i) (η : ℝ) hG (fun _ _ => 0) hd.le
  have hscore : (∑ i : Fin (n + 1),
      (wagerCost (PrefixStage.law B n) (s i) (candidate hG.1 hG.2.1 hL q 0) +
        d * lowDropCost (H i)ᶜ (s i) (candidate hG.1 hG.2.1 hL q 0))) < ε := by
    apply lt_of_le_of_lt hq
    rw [StageWeights.polynomial_supportWager_bound_eq]
    dsimp [c] at hbudget
    nlinarith
  refine ⟨G, L, hG, hL, hGeval, q, hrpos, ?_, ?_, ?_⟩
  · have hlen : L.length = r ^ 24 := by
      rw [hgood.1]
      simp only [SparseParameters.listSize, SparseParameters.blockSize, ← pow_mul]
    exact q.isLt.trans_eq hlen
  · intro a ha
    exact (highMiss_sum_lt_of_goodPool s H hH B hdis n hG a ha).trans hhigh
  · intro y
    apply sums_lt_of_joint_score s H hH B hdis n
    exact hscore

end Klr.StagePreHorizon
