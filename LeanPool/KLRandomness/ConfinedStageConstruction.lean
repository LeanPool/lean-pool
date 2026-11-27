/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageConstruction
public import LeanPool.KLRandomness.ConfinedStageRecursion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Stage construction with prescribed coordinate sets

The finite-stage proof accepts a supplied family of good pools, retaining
an arbitrary coordinate predicate for each stage. Every analytic estimate
is the same as in the unrestricted construction. Support confinement is
retained before choosing the next history.
-/

@[expose] public section

noncomputable section

namespace Klr.ConfinedStageConstruction

open Filter MeasureTheory StageChoice StagePreHorizon StagePrepared
open scoped BigOperators Topology

/-- The only added input to the stage construction: good pools whose members
satisfy a prescribed coordinate predicate at each stage. -/
def PoolSupply (s : ℕ → BettingStrategy) (H : ℕ → Set Cantor)
    (A : ℕ → ℕ → Prop) : Prop :=
  ∀ (n : ℕ) (η : ℝ), 0 < η → ∀ z : ℕ,
    ∃ τ : ℚ, 0 < τ ∧ τ < 1 / 4 ∧
      ∃ e : Nat.Partrec.Code, ∀ᶠ M : ℕ in atTop,
        ∃ G : List ℕ, PoolAdvice.encodePool G ∈ e.eval M ∧
          PoolConstruction.GoodPool (fun i => (s i).normalize.scan)
            H (n + 1) η z τ M G ∧ ∀ b ∈ G, A n b

/-- Supplied confined pools give the same uniform candidate bounds. -/
theorem eventual_candidates (s : ℕ → BettingStrategy)
    (H : ℕ → Set Cantor) (hH : ∀ i, MeasurableSet (H i))
    (A : ℕ → ℕ → Prop) (hpool : PoolSupply s H A) :
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
              (∀ b ∈ G, A n b) ∧
              ∃ q : Fin L.length, 0 < r ∧ q.val < r ^ 24 ∧
                (∀ a ≤ n, (∑ i : Fin (n + 1),
                  (PrefixStage.law B a).real (highMissInput (s i) (H i) G)) < ε) ∧
                ∀ y : Fin r → ZMod 2,
                  (∑ i : Fin (n + 1), wagerCost (PrefixStage.law B n) (s i)
                    (candidate hG.1 hG.2.1 hL q y)) < ε ∧
                  ∀ a ≤ n, (∑ i : Fin (n + 1), (PrefixStage.law B a).real
                    (lowDropInput (s i) (H i) (candidate hG.1 hG.2.1 hL q y))) < ε := by
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
  obtain ⟨τ, hτ, hτquarter, e, he⟩ := hpool n (η : ℝ) hη0 z
  refine ⟨η, hη, hbudget, τ, hτ, hτquarter, e, ?_⟩
  have hpools := tendsto_blockSize_nat.eventually he
  have hlists := SparseListConstruction.eventually_construct_good τ η hτ hη
  have hwager := StageWeights.eventually_family_supportWager_bound_lt (n + 1)
    (show 0 < ε / 2 by positivity)
  filter_upwards [hpools, hlists, hwager, eventually_ge_atTop 1] with r hpr hlr hwr hr
  obtain ⟨G, hGeval, hG, hGA⟩ := hpr
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
  refine ⟨G, L, hG, hL, hGeval, hGA, q, hrpos, ?_, ?_, ?_⟩
  · have hlen : L.length = r ^ 24 := by
      rw [hgood.1]
      simp only [SparseParameters.listSize, SparseParameters.blockSize, ← pow_mul]
    exact q.isLt.trans_eq hlen
  · intro a ha
    exact (highMiss_sum_lt_of_goodPool s H hH B hdis n hG a ha).trans hhigh
  · intro y
    apply sums_lt_of_joint_score s H hH B hdis n
    exact hscore


/-- Rank selection retains the supplied coordinate restriction. -/
theorem exists_prepared (s : ℕ → BettingStrategy)
    (H : ℕ → Set Cantor) (hH : ∀ i, MeasurableSet (H i))
    (A : ℕ → ℕ → Prop) (hpool : PoolSupply s H A) :
      ∀ (old : ℕ → AffineBlock),
        Pairwise (fun i j => Disjoint (old i).support (old j).support) →
        ∀ (n z : ℕ) (error : ℚ), 0 < error →
          ∃ P : Prepared s H old n z error, ∀ b ∈ P.pool, A n b := by
  have hstage := eventual_candidates s H hH A hpool
  intro old hold n z error he
  have heR : (0 : ℝ) < error := by exact_mod_cast he
  obtain ⟨η, hη, _, τ, hτ, hτlt, poolProgram, heventually⟩ :=
    hstage old hold n z (error : ℝ) heR
  obtain ⟨program, hprogram⟩ := StageReconstruction.exists_fixed_program
    (protectedRules s n) (StagePrefixCode.prefixHeader old n) poolProgram error τ η
  have hlength := StageProgramLength.eventually_programFor_stage_budget
    program (StageHorizon.adviceBound error (n + 1)) n
  obtain ⟨r, hr, hbudget⟩ := (heventually.and hlength).exists
  obtain ⟨G, L, hG, hL, hGeval, hGA, q, hrpos, hq, hhigh, hscores⟩ := hr
  exact ⟨{
    listError := η
    density := τ
    listError_pos := hη
    density_pos := hτ
    density_lt := hτlt
    poolProgram := poolProgram
    program := program
    rank := r
    pool := G
    candidates := L
    goodPool := hG
    list_eval := hL
    pool_eval := hGeval
    index := q
    rank_pos := hrpos
    index_lt := hq
    program_correct := hprogram
    program_budget := fun b hb => hbudget q.val b hq hb
    high_miss := hhigh
    scores := hscores }, hGA⟩


/-- Every finite history has a successful extension confined to the supplied
coordinate set. The syndrome and all finite advice are still computed by the
original reconstruction program. -/
theorem exists_step (s : ℕ → BettingStrategy)
    (H : ℕ → Set Cantor) (hH : ∀ i, MeasurableSet (H i))
    (A : ℕ → ℕ → Prop) (hpool : PoolSupply s H A)
    (old : ℕ → AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (n z : ℕ) :
    ∃ C V, StageRecursion.Step s H old n z (StageErrorBudget.rational n) C V ∧
      ∀ p ∈ C.support, A n p := by
  let z' := max z ((PrefixStage.prefixSupport old n).sup id + 1)
  have hz : ∀ k < n, ∀ p ∈ (old k).support, p < z' := by
    intro k hk p hp
    have hmem : p ∈ PrefixStage.prefixSupport old n :=
      (PrefixStage.mem_prefixSupport old n p).mpr ⟨k, hk, hp⟩
    have hle : p ≤ (PrefixStage.prefixSupport old n).sup id :=
      Finset.le_sup (f := id) hmem
    exact lt_of_lt_of_le (Nat.lt_succ_of_le hle) (le_max_right _ _)
  obtain ⟨P, hPA⟩ := exists_prepared s H hH A hpool old hold n z'
    (StageErrorBudget.rational n) (StageErrorBudget.rational_pos n)
  obtain ⟨R⟩ := StageOneStep.result_of_prepared s H old hold n z'
    (StageErrorBudget.rational_pos n) P hz
  have hstep := R.to_step P.goodPool.2.2.1
  refine ⟨R.block, R.horizon, { hstep with above := ?_ }, ?_⟩
  · intro p hp
    exact (le_max_left z _).trans (hstep.above p hp)
  · intro p hp
    exact hPA p (List.mem_toFinset.mp (R.support_subset hp))

/-- The complete construction retains confinement along with all original
stage estimates and exact short affine descriptions. -/
theorem exists_sequence (s : ℕ → BettingStrategy)
    (H : ℕ → Set Cantor) (hH : ∀ i, MeasurableSet (H i))
    (A : ℕ → ℕ → Prop) (hpool : PoolSupply s H A) :
    ∃ (B : ℕ → AffineBlock) (V : ℕ → ℕ),
      Pairwise (fun i j => Disjoint (B i).support (B j).support) ∧
      (∀ n, ∀ p ∈ (B n).support, A n p) ∧
      (∀ i, StageEstimates B (s i).normalize.scan
        (s i).normalize.capital.wager V (H i) i) ∧
      ∀ n : ℕ, ∃ (p : List Bool) (c : AffineCode.Data),
        c ∈ AffineDescription.run p ∧ AffineCode.valid c = true ∧
          2 * p.length + n + 1 ≤ AffineCode.rank c ∧ AffineCode.event c = (B n).event :=
  ConfinedStageRecursion.exists_sequence s H A (exists_step s H hH A hpool) hH

end Klr.ConfinedStageConstruction
