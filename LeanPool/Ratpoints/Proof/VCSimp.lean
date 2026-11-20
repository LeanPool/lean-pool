/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

import Std.WP

/-!
# The simplification of the verification conditions

The Hoare specifications of the loops give verification conditions that
encode the weakest preconditions in the order of `Prop`: meets, propositions of the order, the
measures that end the loops and the applied invariants of the `while` loops. The tactic `vc_simp`
rewrites these encodings into plain propositions in all the hypotheses and the goal, with further
lemmas of each contract (the invariants to unfold and propositional clean-up), before the dispatch
of the conditions.

## Implementation notes

The file uses Lean core and `Std` only, as the contracts that use the tactic do.
-/

public meta section

open Lean.Parser.Tactic in
/-- `vc_simp [l₁, …]` rewrites, in all the hypotheses and the goal, the encodings of the weakest
preconditions of the loop contracts into plain propositions: meets and
propositions of the order (`Lean.Order.meet_prop_eq_and`,
`Lean.Order.CompleteLattice.ofProp_prop_eq`), the measures that end the loops
(`Std.WP.Variant.evalsTo_ofMeasure`, `Std.WP.Variant.evalsBelow_ofMeasure_nat`,
`Std.WP.Assertion.NondetFun.evalsTo_pure`) and the applied invariants of `while` loops
(`Std.WP.WhileInvariant.mk_apply`), with the further simp lemmas `l₁, …`. It is
`simp only [these lemmas, l₁, …] at *`. -/
syntax (name := vcSimp) "vc_simp" (" [" withoutPosition((simpErase <|> simpLemma),*,?) "]")? :
  tactic

macro_rules
  | `(tactic| vc_simp $[[$args,*]]?) => do
    let args := args.map (·.getElems) |>.getD #[]
    `(tactic| simp only [Std.WP.Variant.evalsTo_ofMeasure, Std.WP.Variant.evalsBelow_ofMeasure_nat,
      Std.WP.Assertion.NondetFun.evalsTo_pure, Lean.Order.meet_prop_eq_and,
      Lean.Order.CompleteLattice.ofProp_prop_eq, Std.WP.WhileInvariant.mk_apply, $args,*] at *)

end
