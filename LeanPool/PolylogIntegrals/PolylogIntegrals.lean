/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.Zeta
public import LeanPool.PolylogIntegrals.Statements

/-!
# Polylogarithms and sixteen log-trigonometric integral identities

Source: url:https://github.com/rainrzk/LeanPolyLog/tree/056b7b42fd1a26f241e2945c67ae821ec5bdc49b
Authors: rainrzk
Status: verified
Main declarations: `LeanPolyLog.Proofs.A016`
Tags: analysis, polylogarithms, special-functions, integration, complex-analysis
MSC: 33B30, 26A36, 30B10
-/

/-!
# Polylogarithm integrals

The sixteen identities of rainrzk’s PolyLog Integrals, together with their
series, differentiation, dilogarithm and radial integration infrastructure.

Adapted from https://github.com/rainrzk/LeanPolyLog at commit
056b7b42fd1a26f241e2945c67ae821ec5bdc49b, completed on 1 October 2026.
The Lean formalization was written with Claude assistance and reviewed by rainrzk.
-/
