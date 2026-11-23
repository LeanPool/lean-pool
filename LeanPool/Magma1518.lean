/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.Magma1518.Family
public import LeanPool.Magma1518.OneGenerated

/-!
# One-generated (1518 + 3862)-magmas are trivial or the Z/3 shift

Source: arxiv:2512.07087, url:https://github.com/carlok/magma-1518-obstruction-lean
Authors: Carlo Perassi
Status: verified
Main declarations: `Magma1518.table`, `Magma1518.cube`, `Magma1518.words_in_T`,
  `Magma1518.one_or_three`, `Magma1518.family_members`
Tags: universal-algebra, magmas, equational-theories, equational-logic
MSC: 20N02, 08B05, 03C05, 68V20
-/

/-!
Ported from `carlok/magma-1518-obstruction-lean` at `eb2bbde8c137570d0e281a237187f5323a1b0a2d`
(Apache-2.0), the commit registered with Palomar as `PALOMAR-2026-09-30-000005`. The proofs were
transcribed by an AI agent from equational proofs found by the Vampire prover, under the author's
direction. The finite family members are restated from their coefficient matrices, and their
kernel checks use `decide +kernel` in place of the upstream option overrides; the `bv_decide`
census and the certificate identities of the upstream repository are not ported.
-/

@[expose] public section
