/-
Copyright (c) 2026 Yujie Sun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yujie Sun, Claude Opus 5.5 (AI)
-/
module

public import LeanPool.RowlandPrimes.Basic
public import LeanPool.RowlandPrimes.Sequence

/-!
# Rowland's prime-generating recurrence

Source: arxiv:0710.3217, url:https://cs.uwaterloo.ca/journals/JIS/VOL11/Rowland/rowland21.html
Authors: Yujie Sun, Claude Opus 5.5 (AI)
Status: verified
Main declarations: `RowlandPrimes.rowland_diff_eq_one_or_prime`,
  `RowlandPrimes.increment_eq_one_or_minFac`
Tags: prime-generating-sequences, gcd-recurrence, formal-conjectures
MSC: 11A41, 11B37
-/
