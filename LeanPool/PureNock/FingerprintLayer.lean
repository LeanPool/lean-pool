/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

public import LeanPool.PureNock.Modular
public import LeanPool.PureNock.NPR
public import LeanPool.PureNock.Fingerprint

/-!
# Pure Nock — Fingerprint layer (L2)

Extends the modular layer `NockPure.Modular` (L1) with the noun polynomial representation and its
computable fingerprint:

* the NPR `Φ` and fingerprint `fn`, decomposition `NPR_decomp`, and collision-soundness bounds
  over an arbitrary finite field (`Nock/NPR.lean`, `main.tex:1170–1226`), and
* the extractable Horner fingerprint `fnHorner` with `fnHorner_eq_fn` (`Nock/Fingerprint.lean`).

This root imports `NockPure.Modular`, so L0 ⊂ L1 ⊂ L2 as mechanically verified sub-closures.
No project-declared axioms.
-/

@[expose] public section

