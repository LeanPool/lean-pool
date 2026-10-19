/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.ClassicalMatchingFactors.Regular.EulerTrail

/-!
# Eulerian circuit compatibility import

The circuit theorems originally imported from
[jtraverso/euler-petersen](https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Basic.lean),
registered as PALOMAR-2026-10-16-000016, are publicly re-exported here.
Their shared helpers and proofs are in `EulerTrail`, where circuit existence is
now a corollary of the prescribed-start parity theorem. Both original import paths
and the circuit and trail declaration names remain available.
-/
