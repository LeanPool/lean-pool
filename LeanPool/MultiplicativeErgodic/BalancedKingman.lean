/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.BalancedKingman.Main

/-!
# Kingman's theorem for balanced intervals

The novel part of Section 4 of `proof_met.tex`: Lemma \ref{kingsyn}, the Backward Vitali
lemma \ref{bvit}, and Theorem \ref{balancedkingman}. This is the hardest single argument in
the paper and the last piece of ergodic-theory infrastructure needed before Section 5.

This module is a re-export; the material is split across `ProofMet.BalancedKingman.*` so that
editing one part does not force the whole file to re-elaborate:

| module | contents |
|---|---|
| `Vitali` | hitting times and measure bookkeeping for the backward Vitali windows |
| `Windows` | the endpoints `Λ₋`, `Λ₊`, their measurability, the counting estimates |
| `Walk` | the greedy decomposition of `[0, n)`: `bWalk`, `aWalk`, `blockCount` |
| `Gaps` | `gapMaj`, `gapCount`, `uncovered`, and the telescoping gap estimates |
| `Pointwise` | `covering_pointwise`, `covering_pointwise_clean`, `covering_bound` |
| `Main` | `balancedKingman`, `kingsyn`, `kingsyn_real`, `balancedKingman_of_integrable` |
-/
@[expose] public section

namespace MultiplicativeErgodic


end MultiplicativeErgodic
