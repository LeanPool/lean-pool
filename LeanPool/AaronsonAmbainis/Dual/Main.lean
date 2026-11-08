/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import LeanPool.AaronsonAmbainis.Dual.Cover
public import LeanPool.AaronsonAmbainis.Dual.Row

/-!
# Duality and the row bound

* `coverDuality : CoverDuality`
  (linear-programming duality between fractional packings and rows; it corresponds to
  Proposition 6.7 of the paper, which is `Dual.exists_cover`; file `Cover.lean`, helpers in
  `Sets`, `Functional`, `Core`)
* `rowBoundPM_of_packing : PackingBound → RowBoundPM`
  (the row bound, Theorem 6.8 of the paper, from the packing bound, Lemma 6.5; file `Row.lean`,
  helper in `RowAux`)
-/

@[expose] public section
