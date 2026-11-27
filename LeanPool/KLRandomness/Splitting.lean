/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.SplittingWitness
public import LeanPool.KLRandomness.SplittingScheduler

/-!
# The even/odd splitting property of KL randomness

This is the instance of the Merkle--Miller--Nies--Reimann--Stephan splitting
theorem needed for base-four separation. The proof constructs a rational
source run explicitly and uses the repository's proved totalization theorem.
No equivalence with an external partial-real betting convention is assumed.
-/

@[expose] public section

namespace Klr

namespace Splitting

theorem not_random_of_witness_comparison (side : Bool) (X : Cantor)
    (O T : MartinLofTest) (hO : O.Fails (SplittingScheduler.oracle side X))
    (hT : T.Fails (SplittingScheduler.target side X))
    (hcomp : ∀ N, ∃ m ≥ N,
      witnessTime T (SplittingScheduler.target side X) hT m ≤
        witnessTime O (SplittingScheduler.oracle side X) hO m) :
    ¬KolmogorovLovelandRandom X := by
  let d := family T (witnessTime O (SplittingScheduler.oracle side X) hO)
  apply SplittingScheduler.not_kolmogorovLovelandRandom_of_bets side
    (primrec_ready O.code).to_comp (computable_bet O.code T.code) X
    d.reserveValue d.stake d.reserveValue_nil d.reserve_positive d.stake_legal
    d.reserveValue_snoc
  · exact eventually_ready O (SplittingScheduler.oracle side X) hO
  · intro m n hready
    exact bet_correct O T (SplittingScheduler.oracle side X) hO m
      (ScanRule.inputPrefix (SplittingScheduler.target side X) n)
      (by simpa only [ScanRule.length_inputPrefix] using hready)
  · exact reserve_unbounded O T _ _ hO hT hcomp

end Splitting

/-- Splitting a KL-random sequence into its even and odd coordinates leaves
at least one Martin-Löf-random half. -/
theorem kolmogorovLovelandRandom_even_or_odd (X : Cantor)
    (hX : KolmogorovLovelandRandom X) :
    MartinLofRandom (fun n => X (2 * n)) ∨ MartinLofRandom (fun n => X (2 * n + 1)) := by
  classical
  by_contra h
  obtain ⟨he, ho⟩ := not_or.mp h
  obtain ⟨E, hE⟩ := (not_martinLofRandom_iff _).mp he
  obtain ⟨O, hO⟩ := (not_martinLofRandom_iff _).mp ho
  have heven : SplittingScheduler.target false X = (fun n => X (2 * n)) := rfl
  have hodd : SplittingScheduler.target true X = (fun n => X (2 * n + 1)) := rfl
  have horacleEven : SplittingScheduler.oracle true X = (fun n => X (2 * n)) := rfl
  have horacleOdd : SplittingScheduler.oracle false X = (fun n => X (2 * n + 1)) := rfl
  rcases Splitting.witness_comparison
    (Splitting.witnessTime E (fun n => X (2 * n)) hE)
    (Splitting.witnessTime O (fun n => X (2 * n + 1)) hO) with hcomp | hcomp
  · apply Splitting.not_random_of_witness_comparison false X O E
      (by simpa only [horacleOdd] using hO) (by simpa only [heven] using hE) _ hX
    simpa only [horacleOdd, heven] using hcomp
  · apply Splitting.not_random_of_witness_comparison true X E O
      (by simpa only [horacleEven] using hE) (by simpa only [hodd] using hO) _ hX
    simpa only [horacleEven, hodd] using hcomp

/-- Two failing half-tests are already enough to refute binary KL randomness. -/
theorem not_kolmogorovLovelandRandom_of_halves_fail (T0 T1 : MartinLofTest) (X : Cantor)
    (h0 : T0.Fails (fun n => X (2 * n))) (h1 : T1.Fails (fun n => X (2 * n + 1))) :
    ¬KolmogorovLovelandRandom X := by
  intro hX
  rcases kolmogorovLovelandRandom_even_or_odd X hX with h | h
  · exact h T0 h0
  · exact h T1 h1

end Klr
