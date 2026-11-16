/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.Kingman.Easy

/-!
# Kingman's subadditive ergodic theorem

Section 4 of `proof_met.tex`, up to (not including) the backward Vitali lemma and the balanced
Kingman theorem, which live in `ProofMet.BalancedKingman`.

This module is a re-export; the material is split across `ProofMet.Kingman.*` so that editing
one part does not force the whole downstream chain to re-elaborate:

| module | contents |
|---|---|
| `Basic` | `SubadditiveFamily`, block decompositions, Fekete's limit for the means |
| `ZeroOne` | `liminfGE` and the zero-one law |
| `Walk` | Steele's greedy walk and the transition argument |
| `Truncate` | normalisation, truncation, `lowerIntegral` |
| `Core` | `bkingman`, `kingman`, `kingman_backward_of_integrable`, `L1_orbit_decay` |
| `Easy` | `easyking`, `kingman_backward`, and the `ℝ`/`EReal` wrappers |
-/
@[expose] public section

namespace MultiplicativeErgodic


end MultiplicativeErgodic
