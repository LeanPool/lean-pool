/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import Mathlib.Tactic.Common

/-!
# Plain local hypotheses for long analytic proofs
-/

public meta section
namespace TrilinearHT.Auto

/-- `have! h : T := v` (or `have! h := v`) adds the hypothesis `h : T` proved by `v` as a plain
local hypothesis. Unlike `have`, the proof `v` does not stay in the local context as the value
of `h`, and unlike `obtain h : T := v`, nothing is generalized in the goal. Both matter in very
long tactic proofs: every nested `by` block instantiates the whole local context (including the
values of earlier `have`s), and `obtain` traverses the goal at every step. -/
syntax (name := haveBang) "have! " ident (" : " term)? " := " term : tactic

macro_rules
  | `(tactic| have! $h:ident : $t := $v) =>
    `(tactic| refine no_implicit_lambda% ((fun ($h : $t) => ?_) ($v)))
  | `(tactic| have! $h:ident := $v) =>
    `(tactic| refine no_implicit_lambda% ((fun $h => ?_) ($v)))

end TrilinearHT.Auto
end
