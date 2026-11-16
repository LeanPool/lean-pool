/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.Birkhoff.Ergodic

/-!
# Birkhoff's pointwise ergodic theorem

Mathlib carries only the L²/von Neumann *mean* ergodic theorem; it has no pointwise ergodic
theorem and no maximal ergodic theorem. This file builds towards the pointwise theorem.

## Why this file exists

`ProofMet.Kingman` used to derive Birkhoff-flavoured facts (`L1_orbit_decay`, `easyking`'s
`hupper`) *from* Kingman, applied to an auxiliary additive family. That inverted the real
dependency order and left every §4 result carrying `sorryAx`. Birkhoff is proved directly here,
so the dependency now runs the right way round and §4 is clean.

## Route

Following the author's own write-up (`~/git/maths/dyn.tex`, copied to
`reference/own-writeups/`), in four stages:

1. the **maximal ergodic theorem**;
2. its weak-type consequence `μ(Mf > ε) ≤ ‖f‖₁/ε`;
3. a.e. convergence on the dense subspace `H = {g - g ∘ σ : g ∈ L²}`, where `birkhoffSum`
   telescopes and Borel–Cantelli applies;
4. extension to all of `L¹` by (2), since `H ⊕ Hᗮ` is dense in `L²` and so in `L¹`.

**Deviation from `dyn.tex` at stage 1, deliberate.** `dyn.tex` proves the maximal inequality
first for the shift on `ℤ` by a greedy interval covering, then transfers to a general
measure-preserving system through windowed sequences. That transfer is awkward to formalize.
This file instead proves Garsia's form of the maximal ergodic theorem directly
(`∫_{Eₙ} f ≥ 0`, Rudolph 1990 Lemma 3.2), from which the weak-type bound `dyn.tex` actually
uses follows by a standard argument. Same theorem, shorter path in Lean; the mathematics of
stages 2–4 is unchanged.

## Module layout

This module is a re-export; the material is split across `ProofMet.Birkhoff.*` so that editing
one stage does not re-elaborate the other four:

| module | stage |
|---|---|
| `Maximal` | `maxBirkhoff`, the maximal ergodic theorem, the weak-type inequality |
| `Mean` | coboundaries, `L²` orbit decay, the Hilbert-space/mean ergodic input |
| `OscIO` | the oscillation set and the density upgrade |
| `Average` | `ae_tendsto_birkhoffAverage` for `L¹` |
| `Ergodic` | the ergodic case: the limit is the constant `∫ f` |

Note that splitting here does **not** stop a change in this file from re-elaborating
`ProofMet.Kingman` and everything below it: lake keys a module's trace on its source hash, so any
edit -- a docstring included -- invalidates every module that imports it. Only 3 of the 44
declarations here are unused downstream, so there is no set of "leaf" lemmas that could be moved
below the chain to avoid that. What the split does buy is that an edit re-elaborates ~250 lines
of Birkhoff instead of 1335.
-/
@[expose] public section

namespace MultiplicativeErgodic


end MultiplicativeErgodic
