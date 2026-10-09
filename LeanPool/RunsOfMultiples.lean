/-
Copyright (c) 2026 Jason Hoelscher-Obermaier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5
-/

module

-- Adapted for Lean Pool: module visibility, imports, and proof organization.

public import LeanPool.RunsOfMultiples.Main
public import LeanPool.RunsOfMultiples.Alt.Main
public import LeanPool.RunsOfMultiples.Examples

/-!
# Sharp asymptotic bounds for runs of multiples in finite sets

Source: url:https://github.com/jas-ho/runs-of-multiples-lean/blob/8b7e5f23534c321722725f78b6e64981557f0ef5/docs/runs-of-multiples.pdf
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5 (Lean proofs)
Status: verified
Main declarations: `RunsOfMultiples.main_theorem`, `RunsOfMultiples.main_theorem_alt`
Tags: extremal-number-theory, smooth-numbers, entropy, compression
MSC: 11N25, 11B75, 05D05
-/

/-!
# Runs of multiples in finite sets

The two proofs and their supporting entropy, prime-counting, smooth-number and chain-compression
lemmas were produced with AI under Jason Hoelscher-Obermaier's direction. The original source is
https://github.com/jas-ho/runs-of-multiples-lean/tree/8b7e5f23534c321722725f78b6e64981557f0ef5.
The Lean proofs were written by Claude Opus 5.5. The compression argument was written informally
by GPT-6-Astra; its write-up is `docs/first-missing-multiple.pdf` at the same upstream commit.
Lean Pool ports the project to its pinned toolchain, factors out shared block padding, and
preserves the entropy and compression routes and both lower-bound constructions.
-/
