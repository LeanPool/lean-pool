/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.Conjecture

/-!
# Sendov's conjecture and the Phelps–Rodriguez conjecture

Source: url:https://github.com/teorth/sendov/tree/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d
Authors: Terence Tao
Status: verified
Main declarations: `Sendov.sendov`, `Sendov.phelps_rodriguez`
Tags: sendov-conjecture, polynomial-zeros, critical-points, bernstein-certificates
MSC: 30C15, 30C10, 12D10
-/

/-!
# Sendov's conjecture in Lean Pool

Adapted from Terence Tao's Apache-2.0-licensed repository `teorth/sendov` at commit
`1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d`, a Lean formalization of Sendov's conjecture and
the Phelps–Rodriguez conjecture following Tao's digestion of Lech Mazur's proof. The Lean
source was written by Claude Opus 5 under Tao's direction and review.

Modifications for Lean Pool: Lean/Mathlib v4.35.0-rc3 port and module-system migration;
the numerical certificates of `Sendov.FiniteRange` and `Sendov.LargeDegree.Endgame` are
now checked by the kernel through the list-polynomial infrastructure of
`Sendov.FiniteRange.Certificate` instead of `ring` identities under raised heartbeat
budgets, long numerals are assembled from decimal chunks, and the remaining nonlinear
arithmetic in `Sendov.Reduction.Alpha17` is closed from explicit product hints. Seven
upstream modules outside the dependency closure of the main theorems (six development
cross-checks and one unused reduction-lemma file) were not imported.
-/
