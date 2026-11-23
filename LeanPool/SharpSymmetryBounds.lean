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
Ported from `carlok/sharp-symmetry-bounds-lean` at `ced9fe2d4d2aa42aa03bbc19b1b56cdcd18c9413`
(Apache-2.0), the commit registered with Palomar as `PALOMAR-2026-09-18-000007`. AI coding agents
wrote the Lean proofs under the author's direction, from the author's note. The port adds the
module system, file headers, module docstrings and docstrings for 41 definitions, wraps lines to
100 characters, removes `set_option autoImplicit false` and `#print axioms` lines, and replaces the
upstream `Challenge`/`Solution` pair by `Theorem1`, which keeps the registered statements
unchanged. No proof was changed.
-/

@[expose] public section
