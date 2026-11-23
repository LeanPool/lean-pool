/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.Theorem1

/-!
# Sharp symmetry bounds for real plane algebraic curves

Source: url:https://github.com/carlok/curve-symmetry-lean/blob/18d3984fd32e7482b98bc0ac42753e8508d236dd/sharp_symmetry_bounds.pdf
Authors: Carlo Perassi
Status: verified
Main declarations: `SharpSymmetryBounds.sharp_bounds`, `SharpSymmetryBounds.rotation_bound_sharp`,
  `SharpSymmetryBounds.full_bound_sharp`, `SharpSymmetryBounds.equality_classification`,
  `SharpSymmetryBounds.family_attains_bound`
Tags: algebraic-curves, symmetry, real-algebraic-geometry, euclidean-geometry
MSC: 14H50, 14P05, 51N20, 68V20
-/

/-!
Ported from `carlok/sharp-symmetry-bounds-lean` at `26deee2e033ee17037c051e2ce7c9c739e4b0d59`
(Apache-2.0). AI coding agents wrote the Lean proofs under the author's direction, from the
author's note. That commit is the one registered with Palomar as `PALOMAR-2026-09-18-000007`
(`ced9fe2`) plus the upstream bump to Lean and Mathlib v4.34, which edited proof scripts in 18
files for compatibility: renamed lemmas (for instance `Polynomial.finite_setOfPred_isRoot`),
`let` in place of `letI`, explicit `Complex.star_def` rewrites and updated `simp` sets. The
registered statements did not change.

This port adds the module system, file headers, module docstrings and docstrings for 41
definitions, wraps lines to 100 characters, removes `set_option autoImplicit false` and
`#print axioms` lines, and replaces the upstream `Challenge`/`Solution` pair by `Theorem1`. It
changes no proof script.
-/

@[expose] public section
