/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Weil
public import LeanPool.KloostermanWeil.Weil.Contracts

/-!
# Kloosterman–Weil bounds via Carlitz and Stepanov

Source: url:https://github.com/charliedorsey/weil-bounds-toolkit/tree/7adcd23667b063ae54cc0e8707c89ce259e8fd31
Authors: Charlie Dorsey
Status: verified
Main declarations: `KloostermanWeil.weil1948_bound`, `KloostermanWeil.kloostermanUnitSum_crt`,
  `KloostermanWeil.centeredReducedIntervalSum_bound`
Tags: analytic-number-theory, exponential-sums, finite-fields
MSC: 11L05, 11T23
-/

@[expose] public section


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system and pinned Mathlib version.

The prime estimate is due to Weil. The proof follows Carlitz's extension-field
recurrence and Stepanov's auxiliary-polynomial method, as presented in
[Harcos's notes](https://users.renyi.hu/~gharcos/weil.pdf). Harcos states the
odd-prime case; this development proves the characteristic-two case separately.
The exact generating-series normalization is proved here, but its correspondence
with Carlitz's original equations has not been checked equation by equation.

The upstream software credits Charlie Dorsey (Raccoon Labs), who directed its
scope and publication. Generative AI contributed substantially to the mathematical
development and Lean proofs; the project card records `provenance: AI`.
The upstream source contains the full bibliography and attribution record.
-/
