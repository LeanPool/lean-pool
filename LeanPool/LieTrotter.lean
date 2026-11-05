/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import LeanPool.LieTrotter.Basic
public import LeanPool.LieTrotter.Commutator

/-!
# Lie–Trotter product formula with commutator scaling

Source: url:https://github.com/zblore/lie-trotter-lean
Authors: Zayn Blore
Status: verified
Main declarations: `LieTrotter.norm_trotter_sub_le_commutator`, `LieTrotter.trotter_product`
Tags: functional-analysis, banach-algebras, operator-splitting
MSC: 46H30, 47D06, 15A16
-/

/-!
# Lie–Trotter product formula with commutator scaling

Imported from Zayn Blore’s <https://github.com/zblore/lie-trotter-lean>, commit
`24e7c036dbef3b6cfd33cff4ed05be7339519fde` (28 October 2026), under Apache-2.0.
The commutator bound was completed in that commit; the older convergence proof
originated in the author’s csd-lean4 project in August 2026. The upstream
metadata records that Claude drafted the proofs under the author’s direction.

Adapted for Lean Pool’s module paths, quality requirements and pinned Mathlib.
The setting is a complete normed real algebra with norm-one unit; the result
does not address unbounded generators or claim the sharper unitary bound.

The commutator-sensitive estimate follows the first-order splitting method of
Childs, Su, Tran, Wiebe and Zhu, “Theory of Trotter Error with Commutator
Scaling”, Physical Review X 11 (2021), 011020, extended here to real Banach
algebras with the exponential factor stated in the theorem.
-/
