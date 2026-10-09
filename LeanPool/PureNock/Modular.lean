/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

public import LeanPool.PureNock.Language
public import LeanPool.PureNock.ModularEval
public import LeanPool.PureNock.PaperReferenceMod
public import LeanPool.PureNock.PaperFieldBridge
public import LeanPool.PureNock.Determinism
public import LeanPool.PureNock.TraceCertificate

/-!
# Pure Nock — Modular layer (L1)

Extends the language core `NockPure` (L0) with the executable modular/field layer:

* modular field-noun evaluation `evalFBy` / guarded `evalGBy` (`Nock/ModularEval.lean`),
* the strict modular paper oracle `evalPaperMod q` (`main.tex:1531–1534`),
* the paper-fragment ↔ finite-field bridge `paper_field_bridge` (no-overflow sublanguage),
* output-uniqueness capstones for the machines, and
* executable evaluation-trace certificates.

This root imports `NockPure`, so the L0 closure is a mechanically verified sub-closure of L1.
No project-declared axioms; capstones stay within `{propext, Classical.choice, Quot.sound}`.
-/

@[expose] public section

