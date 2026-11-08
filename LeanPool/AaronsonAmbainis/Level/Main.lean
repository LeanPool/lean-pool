/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import LeanPool.AaronsonAmbainis.Level.Integrated
public import LeanPool.AaronsonAmbainis.Level.Increments

/-!
# Real functions with a row at every point: the three implications

Section 7 of the paper.

* `AaronsonAmbainis.integratedAllPairs_of_allPairs :
  AllPairsInequality → IntegratedAllPairsInequality`
  (the integrated all-pairs inequality, Proposition 7.4 of the paper, from the all-pairs
  inequality for Boolean functions, Proposition 5.2, applied to the level functions `1_{f > t}`
  and integrated over the level `t`; file `Integrated.lean`, helpers in `Rows`, `AllPairs`,
  `Integral`)
* `AaronsonAmbainis.thirdMoment_of_integratedAllPairs :
  IntegratedAllPairsInequality → ThirdMomentInequality`
  (the third-moment inequality, Theorem 7.6, from the integrated all-pairs inequality and the
  lemma that removes the weights, Lemma 5.3, which is in `TwoSided/CauchySchwarz.lean`; file
  `ThirdMoment.lean`)
* `AaronsonAmbainis.meanIncrement_of_thirdMoment : ThirdMomentInequality → MeanIncrementBound`
  (the bound for the mean absolute increments, Theorem 7.10, from the third-moment inequality at
  a median; file `Increments.lean`, helpers in `Basic`, `Median`)
-/

@[expose] public section
