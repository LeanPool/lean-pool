/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.SumOfSetsInSeveralDimensions.ClosedForm
public import LeanPool.SumOfSetsInSeveralDimensions.FreimanDimensionSumsetBounds
public import LeanPool.SumOfSetsInSeveralDimensions.LowerBound
public import LeanPool.SumOfSetsInSeveralDimensions.MinCardAdd

/-!
# Sum of sets in several dimensions

Source: doi:10.1007/BF01302969, url:https://github.com/gdahia/SumOfSetsInSeveralDimensions/tree/bd2694b89fbe18ee5c4365a6330eba36d9f7ed8e
Authors: Gabriel Dahia
Status: verified
Main declarations:
  `SumOfSetsInSeveralDimensions.card_add_sum_min_le_card_add_of_finrank_span_sub_eq`,
  `SumOfSetsInSeveralDimensions.card_add_mul_card_le_card_add_add_of_le_finrank_span_sub`,
  `SumOfSetsInSeveralDimensions.sInf_card_add_eq_add_sum_min`,
  `SumOfSetsInSeveralDimensions.freimanDim_le_two_mul_sub_one_of_card_add_le`
Tags: additive-combinatorics, sumsets, freiman-dimension, discrete-geometry
MSC: 11P70, 11B13, 11B75
-/

/-!
## Upstream attribution

Adapted for Lean Pool from upstream commit `bd2694b89fbe18ee5c4365a6330eba36d9f7ed8e` by
moving the library under `LeanPool.SumOfSetsInSeveralDimensions` and by dropping the unused
`[DecidableEq G]` arguments of `freimanModelDim`, `freimanDim` and three lemmas about them, which
Mathlib's unused-arguments linter rejects. The upstream Palomar
`Challenge` and `Solution` modules are omitted: `Solution` only restates library theorems under
primed names.
-/
