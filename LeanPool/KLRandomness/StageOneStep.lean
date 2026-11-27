/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageOneStepHorizon
public import LeanPool.KLRandomness.StagePreparedIndex
public import LeanPool.KLRandomness.StageCandidateBridge
public import LeanPool.KLRandomness.StageStep

/-!
# A complete stage extension from the prepared finite data

The preparation has already selected one sufficiently large rank and one
good candidate while keeping the reconstruction program fixed. Here bounded
integer advice makes its actual horizon search halt. The same program then
computes the syndrome and a certified affine code. All four stage estimates
and the short-description budget are attached to that actual output.
-/

@[expose] public section

noncomputable section

namespace Klr.StageOneStep

open MeasureTheory ProbabilityTheory SparseListSearch StageCandidate StagePrepared
open scoped BigOperators ENNReal

/-- Prepared finite data produce a fully coded stage result. The only
cutoff hypothesis separates the old supports from the prepared pool. -/
theorem result_of_prepared
    (s : ℕ → BettingStrategy) (H : ℕ → Set Cantor) (old : ℕ → AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (n z : ℕ) {error : ℚ} (herror : 0 < error)
    (P : Prepared s H old n z error)
    (hz : ∀ k < n, ∀ p ∈ (old k).support, p < z) :
    Nonempty (Result old n (protectedRules s n) (fun i => H i)
      error P.rank n P.pool) := by
  let rules := protectedRules s n
  let cs := StagePrefixCode.prefixHeader old n
  let a := P.candidates.get P.index
  have ha : GoodEntry P.pool.length (SparseParameters.supportSize P.rank) P.rank a :=
    StageCandidateBridge.candidate_goodEntry P.goodPool.1 P.list_eval P.index
  let C₀ := block P.pool.get P.goodPool.2.1.injective_get a ha 0
  have heq : StagePreHorizon.candidate P.goodPool.1 P.goodPool.2.1
      P.list_eval P.index 0 = C₀ :=
    StageCandidateBridge.candidate_eq_block P.goodPool.1 P.goodPool.2.1
      P.list_eval P.index ha 0
  have hnew : ∀ k < n, Disjoint (old k).support C₀.support := by
    intro k hk
    apply Finset.disjoint_left.mpr
    intro p hpold hpnew
    have hpG := block_support_subset P.pool P.goodPool.2.1 a ha 0 hpnew
    exact (not_lt_of_ge (P.goodPool.2.2.1 p (List.mem_toFinset.mp hpG))) (hz k hk p hpold)
  have hwager : (∑ i : Fin rules.length, StageChoice.wagerCost (PrefixStage.law old n)
      (rules.get i) C₀) < (error : ℝ) := by
    have h := (P.scores 0).1
    rw [heq] at h
    have h' := (sum_protectedRules s n (fun i =>
      StageChoice.wagerCost (PrefixStage.law old n) (s i) C₀)).trans_lt h
    simpa only [rules, get_protectedRules] using h'
  have hhigh : (∑ i : Fin rules.length, (PrefixStage.law old n).real
      (StagePreHorizon.highMissInput (rules.get i) (H i) P.pool)) < (error : ℝ) := by
    have h' := (sum_protectedRules s n (fun i =>
      (PrefixStage.law old n).real (StagePreHorizon.highMissInput (s i) (H i) P.pool))).trans_lt
      (P.high_miss n le_rfl)
    simpa only [rules, get_protectedRules] using h'
  have hlow : ∀ k ≤ n, (∑ i : Fin rules.length, (PrefixStage.law old k).real
      (StagePreHorizon.lowDropInput (rules.get i) (H i) C₀)) < (error : ℝ) := by
    intro k hk
    have h := (P.scores 0).2 k hk
    rw [heq] at h
    have h' := (sum_protectedRules s n (fun i =>
      (PrefixStage.law old k).real (StagePreHorizon.lowDropInput (s i) (H i) C₀))).trans_lt h
    simpa only [rules, get_protectedRules] using h'
  obtain ⟨b, hb, V, hV, hpartial, htail⟩ := exists_computed_horizon old hold n rules
    (fun i => H i) cs (StagePrefixCode.law_prefixHeader old n) P.pool P.goodPool.2.1
    a ha herror hhigh (hlow n le_rfl)
  have hbounds := bounds_of_computed_horizon old hold n rules (fun i => H i) cs
    (StagePrefixCode.law_prefixHeader old n) P.pool P.goodPool.2.1 P.rank_pos a ha
    hnew hwager hhigh hlow V hpartial htail
  obtain ⟨c, hc, hvalid, hrank, hevent⟩ := StageSyndromeObjective.finish_halts
    rules cs P.pool P.goodPool.2.1 a ha V
  have hget : P.candidates.getD P.index.val default = a :=
    List.getD_eq_get P.candidates default P.index
  have hrun := StageReconstruction.mem_run_of_witnesses rules cs P.poolProgram
    error P.density P.listError
    (r := P.rank) (q := P.index.val) (b := b) (G := P.pool) (L := P.candidates)
    (V := V) (c := c)
    (by simpa only [SparseParameters.blockSize] using P.pool_eval) P.list_eval
    (by simpa only [hget] using hV) (by simpa only [hget] using hc)
  have hruns : c ∈ AffineDescription.run
      (AffineDescription.programFor P.program (Nat.pair P.rank (Nat.pair P.index.val b))) := by
    rw [P.program_correct]
    exact hrun
  refine ⟨{
    block := chosenBlock rules cs P.pool P.goodPool.2.1 a ha V
    horizon := V
    code := c
    program := AffineDescription.programFor P.program (Nat.pair P.rank (Nat.pair P.index.val b))
    valid := hvalid
    runs := hruns
    code_rank := hrank
    block_rank := rfl
    event_eq := hevent
    budget := P.program_budget b ?_
    support_subset := block_support_subset P.pool P.goodPool.2.1 a ha _
    bounds := hbounds }⟩
  simpa only [rules, length_protectedRules] using hb

/-- The finite-list result supplies the natural-number indexed recurrence
relation used by the global stage construction. -/
theorem Result.to_step {s : ℕ → BettingStrategy} {H : ℕ → Set Cantor}
    {old : ℕ → AffineBlock} {n z : ℕ} {error : ℚ} {r : ℕ} {G : List ℕ}
    (R : Result old n (protectedRules s n) (fun i => H i) error r n G)
    (hG : ∀ p ∈ G, z ≤ p) :
    StageRecursion.Step s H old n z error R.block R.horizon := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact hG p (List.mem_toFinset.mp (R.support_subset hp))
  · intro i hi
    let j : Fin (protectedRules s n).length := ⟨i, by rw [length_protectedRules]; omega⟩
    simpa only [get_protectedRules, j] using R.bounds.early j
  · intro i hi
    let j : Fin (protectedRules s n).length := ⟨i, by rw [length_protectedRules]; omega⟩
    simpa only [get_protectedRules, j] using R.bounds.tail j
  · intro i hi
    let j : Fin (protectedRules s n).length := ⟨i, by rw [length_protectedRules]; omega⟩
    simpa only [get_protectedRules, j] using R.bounds.high j
  · intro a ha i hi
    let j : Fin (protectedRules s n).length := ⟨i, by rw [length_protectedRules]; omega⟩
    simpa only [get_protectedRules, lowDropInput_eq, j] using R.bounds.low a ha j
  · refine ⟨R.program, R.code, R.runs, R.valid, ?_, ?_, R.event_eq⟩
    · exact R.code_rank.trans R.block_rank.symm
    · simpa only [R.code_rank] using R.budget

end Klr.StageOneStep

namespace Klr.StagePrepared.Prepared

/-- One prepared stage really extends the construction. This theorem has
no supplied syndrome, horizon, execution witness, or shortness assumption:
all of them are obtained from the prepared data and the analytic estimates. -/
theorem to_step {s : ℕ → BettingStrategy} {H : ℕ → Set Cantor}
    {old : ℕ → AffineBlock}
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    {n z : ℕ} {error : ℚ} (herror : 0 < error)
    (P : StagePrepared.Prepared s H old n z error)
    (hz : ∀ k < n, ∀ p ∈ (old k).support, p < z) :
    ∃ C V, StageRecursion.Step s H old n z error C V := by
  obtain ⟨R⟩ := StageOneStep.result_of_prepared s H old hold n z herror P hz
  exact ⟨R.block, R.horizon, R.to_step P.goodPool.2.2.1⟩

end Klr.StagePrepared.Prepared
