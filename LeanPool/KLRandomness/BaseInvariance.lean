/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.BaseFour
public import LeanPool.KLRandomness.ParityConstruction
public import LeanPool.KLRandomness.Splitting

/-!
# KL randomness is not invariant under binary/base-four regrouping

The witness resists every strategy reading whole pairs, but its even and
odd halves both fail Martin-Löf randomness. The proved splitting theorem
therefore rules out binary KL randomness. Both bases use total fresh scans
and uniformly computable real capital, with the appropriate fair averaging.
-/

@[expose] public section

namespace Klr

/-- A base-four KL-random digit stream whose binary ungrouping is not
KL-random, with the base-four stream displayed as adjacent pairs of bits. -/
theorem exists_baseFour_random_not_binary_random :
    ∃ X : Cantor, BaseFour.KolmogorovLovelandRandom (BaseFour.pairDigits X) ∧
      ¬KolmogorovLovelandRandom X := by
  obtain ⟨X, hpair, h0, h1⟩ :=
    ParityConstruction.exists_pairRespectingRandom_halves_not_martinLofRandom
  refine ⟨X, (BaseFour.kolmogorovLovelandRandom_pairDigits_iff X).mpr hpair, ?_⟩
  intro hX
  exact (kolmogorovLovelandRandom_even_or_odd X hX).elim h0 h1

/-- Binary KL randomness implies base-four KL randomness, and the converse
fails for the canonical grouping of adjacent bits. -/
theorem binary_random_ssubset_baseFour_random :
    {X : Cantor | KolmogorovLovelandRandom X} ⊂
      {X : Cantor | BaseFour.KolmogorovLovelandRandom (BaseFour.pairDigits X)} := by
  apply Set.ssubset_iff_exists.mpr
  refine ⟨fun _ hX => BaseFour.of_binary_kolmogorovLovelandRandom hX, ?_⟩
  exact exists_baseFour_random_not_binary_random

end Klr
