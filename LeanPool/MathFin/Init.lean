/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module -- shake: keep-downstream

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import Lean.Meta.Tactic.Grind.RegisterCommand

/-!
# Library conventions

Every MathFin module imports this file: a module that imports no other library module imports
it directly, and the rest see it through their imports (`tests/test_architecture.py`). It holds
the library's Lean-level conventions, so a new one reaches every module without a sweep
(`docs/specs/2026-11-05-library-practices-design.md` §5; CSLib's `Cslib.Init`).

The conventions it does not hold are written down in `docs/design.md` §5. Notation is `scoped` in
the namespace of the object it writes, or `local`, and never global; an abstraction comes with
the automation its users need.

## Main definitions

* `pricing`: the library's grind set for pricing identities: put–call parity on the closed
  forms and the risk-neutral probabilities of the trees. Tag a lemma `@[pricing =]` (or with
  any other grind modifier) and close goals with `grind [pricing]`. Kept separate from the
  global `grind` set so that a finance identity never slows an unrelated `grind` call.
  `MathFinTest/Automation.lean` pins what it closes.

## References

* [CSLib][CSLib], `Cslib/Init.lean` (the conventions module every file imports).

## Tags

conventions, grind set, attributes, automation
-/

@[expose] public section

/-- The library's grind set for pricing identities (put–call parity, the risk-neutral
probabilities of the trees): `grind [pricing]`. -/
register_grind_attr pricing
