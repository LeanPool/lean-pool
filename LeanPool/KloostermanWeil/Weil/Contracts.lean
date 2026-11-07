/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Weil


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Unconditional bounds derived from the prime theorem

The underlying general lemmas in `rml.weil.crt_and_completion` accept a
`PrimeNondegenerateWeil` proof explicitly. Here they are instantiated with
`prime_bound`; callers do not need to supply that argument.
-/

@[expose] public section

namespace KloostermanWeil

/-- Squarefree-modulus estimate for a unit numerator. -/
theorem squarefreeUnitNumerator_bound
    {q : ℕ} [NeZero q] (hsq : Squarefree q)
    (a b : ZMod q) (ha : IsUnit a) :
    ‖kloostermanUnitSum q a b‖ ≤
      (2 : ℝ) ^ q.primeFactors.card * Real.sqrt q :=
  kloostermanUnitSum_squarefree_unit_le prime_bound hsq a b ha

/-- Bound on the sum at the reduced modulus, with no lifting assertion. -/
theorem reducedModulusSum_bound
    {A q : ℕ} (hq : 0 < q) (hsq : Squarefree q)
    (b : ZMod (reducedModulus A q)) :
    letI : NeZero (reducedModulus A q) :=
      ⟨Nat.ne_of_gt (reducedModulus_pos hq)⟩
    ‖kloostermanUnitSum (reducedModulus A q)
       (reducedNumerator A q : ZMod (reducedModulus A q)) b‖ ≤
       (2 : ℝ) ^ (reducedModulus A q).primeFactors.card *
       Real.sqrt (reducedModulus A q) :=
  kloostermanUnitSum_reduced_le prime_bound hq hsq b

/-- Centered completion on the reduced squarefree modulus. -/
theorem centeredReducedIntervalSum_bound
    {A q : ℕ} (hq : 0 < q) (hsq : Squarefree q)
    (x : ZMod (reducedModulus A q)) (L : ℕ) :
    letI : NeZero (reducedModulus A q) :=
      ⟨Nat.ne_of_gt (reducedModulus_pos hq)⟩
    ‖centeredIntervalSum
        (reducedModulus A q)
        (reducedNumerator A q : ZMod (reducedModulus A q))
        x L‖ ≤
      ((2 : ℝ) ^ (reducedModulus A q).primeFactors.card *
          Real.sqrt (reducedModulus A q)) *
        (1 + Real.log (reducedModulus A q)) :=
  centeredReducedIntervalSum_le prime_bound hq hsq x L

/-- Weighted centered completion with positive initial weight `Y`. -/
theorem weightedCenteredReducedIntervalSum_bound
    {A q : ℕ} (hq : 0 < q) (hsq : Squarefree q)
    (x : ZMod (reducedModulus A q))
    (Y L : ℕ) (hY : 0 < Y) :
    letI : NeZero (reducedModulus A q) :=
      ⟨Nat.ne_of_gt (reducedModulus_pos hq)⟩
    ‖weightedCenteredIntervalSum
        (reducedModulus A q)
        (reducedNumerator A q : ZMod (reducedModulus A q))
        x Y L‖ ≤
      2 *
        (((2 : ℝ) ^ (reducedModulus A q).primeFactors.card *
            Real.sqrt (reducedModulus A q)) *
          (1 + Real.log (reducedModulus A q))) / Y :=
  weightedCenteredReducedIntervalSum_le prime_bound hq hsq x Y L hY

end KloostermanWeil
