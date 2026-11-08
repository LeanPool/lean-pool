/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import LeanPool.AaronsonAmbainis.DetTheorem
public import LeanPool.AaronsonAmbainis.TwoSided.Main
public import LeanPool.AaronsonAmbainis.Level.Main
public import LeanPool.AaronsonAmbainis.Average.Main
public import LeanPool.AaronsonAmbainis.Row.Main
public import LeanPool.AaronsonAmbainis.Row.DisjointBlocks
public import LeanPool.AaronsonAmbainis.Pack.Main
public import LeanPool.AaronsonAmbainis.Dual.Main
public import LeanPool.AaronsonAmbainis.MainTheorem

/-!
# The chain

This file chains the links of the proof of the paper: every theorem below is one implication,
applied to theorems that precede it.

Boolean functions (directories `DetLow`, `DetBij`, `TwoSided`):

* `detInequality`         — the determinant inequality (Corollary 3.2), in `DetTheorem.lean`;
* `antipodal_of_det`      — the antipodal inequality (Theorem 4.3);
* `allPairs_of_antipodal` — the all-pairs inequality (Proposition 5.2);
* `twoSided_of_allPairs`  — the two-sided inequality (Theorem 5.4).

Real functions with a row of cost at most `K` at every point (directories `Level`, `Average`):

* `integratedAllPairs_of_allPairs`    — the integrated all-pairs inequality (Proposition 7.4);
* `thirdMoment_of_integratedAllPairs` — the third-moment inequality (Theorem 7.6);
* `meanIncrement_of_thirdMoment`      — the bound for the mean absolute increments
                                        (Theorem 7.10);
* `influence_of_meanIncrement`        — the bound for the influences (Theorem 8.3).

Bounded functions of degree at most `d` (directories `Row`, `Pack`, `Dual`):

* `blockInequality`       — the block inequality (Lemma 6.4), in `Row/Main.lean`;
* `sensitivity_of_block`  — the sensitivity bound at every point (Corollary 6.10);
* `packingBound_of_block` — the packing bound (Lemma 6.5);
* `rowBoundPM_of_packing` — the row bound (Theorem 6.8: rows of cost at most `π² d²`).

The theorems for bounded functions of degree at most `d` (`MainTheorem.lean`):

* `mainTheorem_of_influence`             — the main theorem (Theorem 1.1);
* `meanIncrementDegree_of_meanIncrement` — the bound for the mean absolute increments
                                           (Corollary 7.11);
* `mainTheoremImproved_of_influence`     — the main theorem with the constant that the row bound
                                           of Agarwal and Ben-David gives (Remark 8.4).

All theorems of this file except the last one have no hypothesis. The hypothesis of the last
one, `mainTheoremImproved_of_rowBound : RowBound → MainTheoremImproved`, is `RowBound`, the row
bound of Agarwal and Ben-David (Theorem 1.7 of arXiv:2410.19062), which is not proved in this
project. The two-sided inequality is a result of the paper in its own right; the main theorem
does not use it.
-/

@[expose] public section

namespace AaronsonAmbainis

/-! ### Boolean functions -/

/-- The antipodal inequality (the inequality of Theorem 4.3 of the paper), with no hypothesis. -/
theorem antipodalInequality : AntipodalInequality := antipodal_of_det detInequality

/-- The all-pairs inequality (the inequality of Proposition 5.2 of the paper), with no
hypothesis. -/
theorem allPairsInequality : AllPairsInequality := allPairs_of_antipodal antipodalInequality

/-- The two-sided inequality (the inequality of Theorem 5.4 of the paper), with no hypothesis. -/
theorem twoSidedInequality : TwoSidedInequality := twoSided_of_allPairs allPairsInequality

/-! ### Real functions with a row at every point -/

/-- The integrated all-pairs inequality (the inequality of Proposition 7.4 of the paper), with no
hypothesis. -/
theorem integratedAllPairsInequality : IntegratedAllPairsInequality :=
  integratedAllPairs_of_allPairs allPairsInequality

/-- The third-moment inequality (Theorem 7.6 of the paper), with no hypothesis. -/
theorem thirdMomentInequality : ThirdMomentInequality :=
  thirdMoment_of_integratedAllPairs integratedAllPairsInequality

/-- The bound for the mean absolute increments (Theorem 7.10 of the paper), with no
hypothesis. -/
theorem meanIncrementBound : MeanIncrementBound :=
  meanIncrement_of_thirdMoment thirdMomentInequality

/-- The bound for the influences (Theorem 8.3 of the paper), with no hypothesis. -/
theorem influenceBound : InfluenceBound := influence_of_meanIncrement meanIncrementBound

/-! ### Bounded functions of degree at most `d` -/

/-- The sensitivity bound at every point (Corollary 6.10 of the paper), with no hypothesis. -/
theorem sensitivityBound : SensitivityBound := sensitivity_of_block blockInequality

/-- The packing bound (Lemma 6.5 of the paper), with no hypothesis. -/
theorem packingBound : PackingBound := packingBound_of_block blockInequality

/-- The row bound (Theorem 6.8 of the paper: rows of cost at most `π² d²`), with no
hypothesis. -/
theorem rowBoundPM : RowBoundPM := rowBoundPM_of_packing packingBound

/-! ### The theorems for bounded functions of degree at most `d` -/

/-- The main theorem (Theorem 1.1 of the paper), with no hypothesis. -/
theorem mainTheorem : MainTheorem :=
  mainTheorem_of_influence influenceBound sensitivityBound rowBoundPM

/-- The bound for the mean absolute increments of a bounded function of degree at most `d`
(Corollary 7.11 of the paper), with no hypothesis. -/
theorem meanIncrementDegreeBound : MeanIncrementDegreeBound :=
  meanIncrementDegree_of_meanIncrement meanIncrementBound rowBoundPM

/-- The row bound of Agarwal and Ben-David, which is a hypothesis here, implies the main theorem
with the constant `3125 π^8` (Remark 8.4 of the paper). -/
theorem mainTheoremImproved_of_rowBound : RowBound → MainTheoremImproved :=
  mainTheoremImproved_of_influence influenceBound sensitivityBound

end AaronsonAmbainis
