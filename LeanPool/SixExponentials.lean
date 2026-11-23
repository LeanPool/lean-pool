/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SixExponentials.Statement

/-!
# The six exponentials theorem of Lang and Ramachandra

Source: url:https://github.com/carlok/six-exponentials-lean
Authors: Carlo Perassi
Status: verified
Main declarations: `SixExponentials.SX.six_exponentials_of_numberField`,
  `SixExponentials.exists_transcendental_exp`, `SixExponentials.six_exponentials_theorem`
Tags: transcendence, six-exponentials, schneider-method, number-fields
MSC: 11J81, 68V20
-/

/-!
Ported from `carlok/six-exponentials-lean` at `b42d65be65fc4e4a7cea3ba965aabea8f1df8028`
(Apache-2.0), the commit registered with Palomar as `PALOMAR-2026-11-22-000020`. That repository
is a self-contained extract of `Diaz.six_exponentials` and its import closure from
`carlok/diaz-modulus-lean` (commit `edb9c5b92df0935ed6834e1d965fe9c18cfa21bb`), where Claude agents
wrote the proofs under the author's direction and the Prove2Me platform checked them. The port
renames the modules, replaces `import Mathlib` by the imports each file needs, wraps lines to 100
characters, removes the unused definition `SX.OrderAtMost`, and generalises `six_exponentials` to
`exists_transcendental_exp`, the theorem for every `(d, l)` with `d + l < d l`, of which it is now
the case `d = 2`, `l = 3`.
For Mathlib v4.36 and its linters it also replaces `push_neg` by `push Not` and goal-changing
`show` by `change`, drops two unused `simp` arguments and the unused hypothesis `hx` of
`SX.descent_step`, and closes one goal with `nlinarith` instead of `positivity`.

The pool's `RoyStrongSix` proves Roy's strong six exponentials theorem, which assumes linear
independence over the algebraic numbers. The statements here assume only linear independence over
`ℚ`, and the proof is Schneider's auxiliary-function method, with no multiplicity estimate.
-/

@[expose] public section
