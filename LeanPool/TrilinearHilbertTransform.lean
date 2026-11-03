/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

public import LeanPool.TrilinearHilbertTransform.Theorems

/-!
# Boundedness of the trilinear Hilbert transform

Source: url:https://github.com/roos-j/lean-trilinearht/tree/7b4209609e6a7fb9d9935973ee8541495f943660
Authors: Joris Roos
Status: verified
Main declarations: `TrilinearHT.trilinear_ht_bound`
Tags: harmonic-analysis, singular-integrals, additive-combinatorics, time-frequency-analysis
MSC: 42B20, 42B25
-/

/-!
## Attribution and scope

Joris Roos supplied the canonical interface; the upstream credits Claude and Codex for AI proofs in
[the upstream formalization](https://github.com/roos-j/lean-trilinearht).
The mathematics is the fixed-slope result in OpenAI's *An L³ bound for the trilinear
Hilbert transform* (October 5, 2026). The formalization was publicly announced on
October 20, 2026. The exact source revision and announcement are recorded in the project card.

The integral here uses `x + jt`; reflection of the integration variable changes the
paper's `x - jt` operator by an overall minus sign, preserving the stated norm bound.
The result concerns slopes `1, 2, 3` and exponents `3, 3, 3, 1`.
-/
