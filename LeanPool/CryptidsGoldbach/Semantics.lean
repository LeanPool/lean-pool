/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maxence Faldor, Moritz Firsching
-/
module

public import LeanPool.CryptidsGoldbach.Goldbach21
public import LeanPool.CryptidsGoldbach.Propositions

/-!
# Semantics of the Goldbach Turing Machines (`goldbach_25` and `goldbach_21`)

This file proves that the 25-state baseline Turing machine `reference` (`goldbach_25`) and the
21-state compressed Turing machine `candidate` (`goldbach_21`) halt on the blank tape if and only
if Goldbach's conjecture is false (i.e., there exists an even integer $n > 2$ that cannot be
written as the sum of two primes).

## Provenance and Attribution

* **Original 27-state (26-state reachable) Goldbach Turing machine (2016)**:
  Published anonymously in a GitHub Gist
  (<https://gist.github.com/anonymous/a64213f391339236c2fe31f8749a0df6>) and popularized by
  Scott Aaronson and the Busy Beaver Challenge community
  (<https://wiki.bbchallenge.org/wiki/Cryptids>).
* **25-state optimization and first Lean 4 verification (2024)**:
  Yijun Leng optimized the machine from 26 reachable states to 25 states (`goldbach_25`, the
  `reference` machine here) and formalized its correctness in Lean 4 in
  <https://github.com/lengyijun/goldbach_tm> (released under the Apache-2.0 license).
* **21-state compression and halting-equivalence proof (2026)**:
  Maxence Faldor and Moritz Firsching (using Gemini Argon) found the 21-state machine `candidate`
  (`goldbach_21`) and proved `Halts reference ↔ ∃ w : ℕ, ¬ HasGoldbachPair (2 * w + 4)` and
  `Halts candidate ↔ Halts reference` in `Cryptids.Goldbach21`.
-/

@[expose] public section

namespace ConjectureMachines.Goldbach21.Semantics

open Turing StateTransition
open ConjectureMachines.Goldbach21

/-- Equivalence between `IsPrime` in `Cryptids.Goldbach21` and Mathlib's `Nat.Prime`. -/
theorem isPrime_iff_prime (n : ℕ) : IsPrime n ↔ Nat.Prime n :=
  Nat.prime_def_lt'.symm

/-- Equivalence between `HasGoldbachPair (2 * w + 4)` for all `w` and `GoldbachConjecture`. -/
theorem goldbachConjecture_iff_all_stages :
    GoldbachConjecture ↔ ∀ w : ℕ, HasGoldbachPair (2 * w + 4) := by
  constructor
  · intro hG w
    obtain ⟨p, q, hp, hq, hn⟩ := hG (2 * w + 4) (by omega) ⟨w + 2, by omega⟩
    exact ⟨p, q, (isPrime_iff_prime p).mpr hp, (isPrime_iff_prime q).mpr hq, hn.symm⟩
  · intro hall n hn2 ⟨k, hk⟩
    have hk2 : 2 ≤ k := by omega
    obtain ⟨a, b, ha, hb, hab⟩ := hall (k - 2)
    exact ⟨a, b, (isPrime_iff_prime a).mp ha, (isPrime_iff_prime b).mp hb, by omega⟩

/-- The 25-state baseline machine `reference` (`goldbach_25`) halts on the blank tape
if and only if Goldbach's conjecture is false. -/
theorem halts_reference_iff_not_goldbach :
    Halts reference ↔ ¬ GoldbachConjecture := by
  change Halts refM ↔ ¬ GoldbachConjecture
  rw [halts_reference_iff_exists_counterexample, goldbachConjecture_iff_all_stages]
  push Not
  rfl

/-- The 21-state machine `candidate` (`goldbach_21`) halts on the blank tape
if and only if Goldbach's conjecture is false. -/
theorem halts_candidate_iff_not_goldbach :
    Halts candidate ↔ ¬ GoldbachConjecture :=
  candidate_equivalent.trans halts_reference_iff_not_goldbach

end ConjectureMachines.Goldbach21.Semantics
