/-
Copyright (c) 2022 The Iris-Lean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Iris-Lean Contributors
-/

module

public import LeanPool.IrisAlgebra.Algebra.CMRAConstructors
public import LeanPool.IrisAlgebra.Algebra.IProp

/-!
# Ordered resource algebras and the Iris recursive domain model

Source: arxiv:2609.24252, url:https://github.com/leanprover-community/iris-lean
Authors: The Iris-Lean Contributors
Status: verified
Main declarations: `Iris.IProp.fold_unfold`, `Iris.IProp.unfold_fold`
Tags: program-semantics, separation-logic, resource-algebras, guarded-recursion, domain-equations
MSC: 03B70, 68Q55, 68N30
-/

/-!
# Ordered resource algebras and the Iris recursive domain model

This is the algebraic dependency closure of `Iris.Algebra.IProp` from
`leanprover-community/iris-lean` at `81bc35088ba67d465db008f5261a9b341eb6cf6c`.
It includes the ordered resource algebras added on October 14, 2026, and retains
the general complete step-indexed space and guarded recursive domain constructions.
The separation logic proof mode, program logics, HeapLang, and verification automation
are outside this import's scope.

Upstream NOTICE:

Iris-Lean — Copyright (c) 2022–2026 The Iris-Lean Contributors.
Prior per-file copyright notices are preserved in the upstream repository's git history
(tag `copyright-notices`). Individual authors are retained in file headers; the project YAML
also preserves the original notices verbatim, including names transliterated in Lean headers.

The upstream code is Apache-2.0. The port removes source-tracking commands, replaces
implemented opaque definitions by ordinary irreducible definitions, and adapts proofs
to Lean Pool's pinned Lean and Mathlib. No program-logic soundness theorem is claimed here.
-/
