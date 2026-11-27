/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StagePreHorizon
public import LeanPool.KLRandomness.StageReconstruction
public import LeanPool.KLRandomness.StageProgramLength
public import LeanPool.KLRandomness.StagePrefixCode

/-!
# Fixing the program before selecting the final stage rank

The pool lemma and sparse-list estimates give good candidates at every
sufficiently large rank. The reconstruction compiler gives one fixed code
before the rank is selected, and the explicit pairing estimate gives another
eventual bound. Intersecting these two eventual sets chooses an actual
candidate meeting the short-description budget for every allowed horizon
advice. The Borel partitions are fixed before any stage data.
-/

@[expose] public section

noncomputable section

namespace Klr.StagePrepared

open Filter MeasureTheory SparseListSearch
open scoped BigOperators

/-- The finite protected strategy list in the fixed program header. -/
def protectedRules (s : ℕ → BettingStrategy) (n : ℕ) : List BettingStrategy :=
  List.ofFn (fun i : Fin (n + 1) => s i)

@[simp] theorem length_protectedRules (s : ℕ → BettingStrategy) (n : ℕ) :
    (protectedRules s n).length = n + 1 := List.length_ofFn

/-- Concrete outputs and estimates selected at a rank large enough for the
already fixed reconstruction program. The syndrome remains to be computed. -/
structure Prepared (s : ℕ → BettingStrategy) (H : ℕ → Set Cantor)
    (old : ℕ → AffineBlock) (n z : ℕ) (error : ℚ) where
  /-- The rational tolerance used for the sparse-candidate bounds. -/
  listError : ℚ
  /-- The density threshold for testing candidate restrictions. -/
  density : ℚ
  listError_pos : 0 < listError
  density_pos : 0 < density
  density_lt : density < 1 / 4
  /-- The fixed program that computes a pool from its finite input parameters. -/
  poolProgram : Nat.Partrec.Code
  /-- The fixed reconstruction program used to describe a selected affine constraint. -/
  program : Nat.Partrec.Code
  /-- The rank selected for the new affine constraint. -/
  rank : ℕ
  /-- The finite list of fresh positions selected for this stage. -/
  pool : List ℕ
  /-- The coded list of sparse candidate affine constraints on the pool. -/
  candidates : CodeList
  goodPool : PoolConstruction.GoodPool (fun i => (s i).normalize.scan)
    H (n + 1) (listError : ℝ) z density (SparseParameters.blockSize rank) pool
  list_eval : candidates ∈ SparseListConstruction.construct density listError rank
  pool_eval : PoolAdvice.encodePool pool ∈ poolProgram.eval (SparseParameters.blockSize rank)
  /-- The selected candidate's index in the finite list. -/
  index : Fin candidates.length
  rank_pos : 0 < rank
  index_lt : index.val < rank ^ 24
  program_correct : ∀ r q b,
    AffineDescription.run (AffineDescription.programFor program (Nat.pair r (Nat.pair q b))) =
      StageReconstruction.run (protectedRules s n) (StagePrefixCode.prefixHeader old n)
        poolProgram error density listError (r, (q, b))
  program_budget : ∀ b, b ≤ StageHorizon.adviceBound error (n + 1) →
    2 * (AffineDescription.programFor program (Nat.pair rank (Nat.pair index.val b))).length +
      n + 1 ≤ rank
  high_miss : ∀ a ≤ n, (∑ i : Fin (n + 1),
    (PrefixStage.law old a).real (StagePreHorizon.highMissInput (s i) (H i) pool)) < error
  scores : ∀ y : Fin rank → ZMod 2,
    (∑ i : Fin (n + 1), StageChoice.wagerCost (PrefixStage.law old n) (s i)
      (StagePreHorizon.candidate goodPool.1 goodPool.2.1 list_eval index y)) < error ∧
    ∀ a ≤ n, (∑ i : Fin (n + 1), (PrefixStage.law old a).real
      (StagePreHorizon.lowDropInput (s i) (H i)
        (StagePreHorizon.candidate goodPool.1 goodPool.2.1 list_eval index y))) < error

/-- The entire finite-stage preparation exists without an effectiveness
assumption on the infinite sequence of stages or the enumeration of strategies. -/
theorem exists_fixed_partitions_prepared (s : ℕ → BettingStrategy) :
    ∃ H : ℕ → Set Cantor, (∀ i, MeasurableSet (H i)) ∧
      ∀ (old : ℕ → AffineBlock),
        Pairwise (fun i j => Disjoint (old i).support (old j).support) →
        ∀ (n z : ℕ) (error : ℚ), 0 < error →
          Nonempty (Prepared s H old n z error) := by
  obtain ⟨H, hH, hstage⟩ := StagePreHorizon.exists_fixed_partitions_eventual_candidates s
  refine ⟨H, hH, ?_⟩
  intro old hold n z error he
  have heR : (0 : ℝ) < error := by exact_mod_cast he
  obtain ⟨η, hη, _, τ, hτ, hτlt, poolProgram, heventually⟩ :=
    hstage old hold n z (error : ℝ) heR
  obtain ⟨program, hprogram⟩ := StageReconstruction.exists_fixed_program
    (protectedRules s n) (StagePrefixCode.prefixHeader old n) poolProgram error τ η
  have hlength := StageProgramLength.eventually_programFor_stage_budget
    program (StageHorizon.adviceBound error (n + 1)) n
  obtain ⟨r, hr, hbudget⟩ := (heventually.and hlength).exists
  obtain ⟨G, L, hG, hL, hGeval, q, hrpos, hq, hhigh, hscores⟩ := hr
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
    scores := hscores }⟩

end Klr.StagePrepared
