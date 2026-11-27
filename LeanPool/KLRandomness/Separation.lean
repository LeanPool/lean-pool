/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageConstruction
public import LeanPool.KLRandomness.StageEnumeration
public import LeanPool.KLRandomness.MLImpliesKL
public import LeanPool.KLRandomness.PartialBettingCapital

/-!
# Separation for the total computable-real strategy convention

The completed stage construction supplies all analytic estimates and all
actual short affine programs. A classical enumeration covers every strategy
in the repository's total computable-real `BettingStrategy` type. Thus the
separation below has no construction or description premise.

The theorem uses the repository's explicit total-strategy convention. It
does not assert a new equivalence with a general partial computable-real
strategy convention.
-/

@[expose] public section

namespace Klr

/-- There is a sequence which defeats every total computable-real
Kolmogorov–Loveland betting strategy but fails a Martin-Löf test. -/
theorem exists_kolmogorovLovelandRandom_not_martinLofRandom :
    ∃ X : Cantor, KolmogorovLovelandRandom X ∧ ¬MartinLofRandom X := by
  obtain ⟨s, hs⟩ := StageEnumeration.exists_surjective
  obtain ⟨H, hH, hstep⟩ := StageConstruction.exists_fixed_partitions_steps s
  exact StageRecursion.exists_separating_of_steps s H hstep hs hH

/-- The same witness also defeats every infinite fresh run of an actual
partial rational-wager source program, by the proved even/odd totalization. -/
theorem exists_not_martinLofRandom_no_partial_rational_success :
    ∃ X : Cantor, ¬MartinLofRandom X ∧
      ∀ (c : Nat.Partrec.Code) (r : PartialBetting.SourceRun c X), ¬r.Succeeds := by
  obtain ⟨X, hKL, hML⟩ := exists_kolmogorovLovelandRandom_not_martinLofRandom
  exact ⟨X, hML, fun _ r => PartialBetting.no_partial_rational_success hKL r⟩

/-- Martin-Löf randomness and the repository's Kolmogorov–Loveland
randomness predicate define different classes. -/
theorem kolmogorovLovelandRandom_ne_martinLofRandom :
    {X : Cantor | KolmogorovLovelandRandom X} ≠ {X : Cantor | MartinLofRandom X} := by
  obtain ⟨X, hKL, hML⟩ := exists_kolmogorovLovelandRandom_not_martinLofRandom
  intro h
  exact hML (show X ∈ {X : Cantor | MartinLofRandom X} from h ▸ hKL)

/-- The Martin-Löf random class is a proper subset of the class defined
by total computable-real Kolmogorov–Loveland betting strategies. -/
theorem martinLofRandom_ssubset_kolmogorovLovelandRandom :
    {X : Cantor | MartinLofRandom X} ⊂ {X : Cantor | KolmogorovLovelandRandom X} := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · exact fun _ h => h.kolmogorovLovelandRandom
  · exact Ne.symm kolmogorovLovelandRandom_ne_martinLofRandom

end Klr
