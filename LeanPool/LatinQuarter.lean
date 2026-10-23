/-
Copyright (c) 2026 Richard Bean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Bean
-/
module

public import LeanPool.LatinQuarter.Textbook

/-!
# The smallest critical set in a Latin square

Source: arxiv:2610.18199, url:https://github.com/RichardBean/latin-quarter-lean/tree/9997439dee62e1ede0aa995ddb7160dbceeff7b7
Authors: Richard Bean
Status: verified
Main declarations: `LatinQuarter.Textbook.completions_even`, `LatinQuarter.Textbook.scs_eq_quarter`
Tags: combinatorics, latin-squares, critical-sets, parity
MSC: 05B15
-/

/-!
# Critical sets of Latin squares

Adapted from RichardBean/latin-quarter-lean at 9997439dee62e1ede0aa995ddb7160dbceeff7b7.
Upstream NOTICE:

The smallest critical set in a Latin square: Lean 4 formalization
Copyright 2026 Richard Bean

Licensed under the Apache License, Version 2.0. See LICENSE.

This formalization and its documentation were substantially AI-generated
with Codex under Richard Bean's direction. The version 0.2.0 additions
(LatinQuarter/Parity.lean, LatinQuarter/Textbook.lean, and the kernel-replay
and nanoda checks in the GitHub workflow) were written by Claude (Anthropic)
at Richard Bean's request. The mathematical manuscript was
developed with substantial assistance from Codex and Claude. See README.md.

Dependencies retain their own licences; dependency sources and compiled
libraries are not included in this source distribution.

The complete modular proof is preserved, including general results about matrix minors,
square-zero ideals, and polynomial coefficients. The duplicate standalone compilation
and upstream audit scripts are not imported.
-/
