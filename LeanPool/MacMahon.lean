/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.MacMahon.Submission

/-!
# The ten minimum universal collections of MacMahon cubes

Source: url:https://github.com/jasondavies/macmahon-min-universal-sets/tree/d8856c97e43e6fa66383c81b8ac4f5bd1c285bc8
Authors: Jason Davies
Status: verified
Main declarations: `MacMahon.minimum_size`, `MacMahon.physical_exactly_ten`
Tags: combinatorics, coloured-cubes, classification, finite-geometry
MSC: 05A15, 05C70, 68V15, 00A08
-/

/-!
## Attribution

Adapted for Lean Pool from Jason Davies's Apache-2.0 formalization at
https://github.com/jasondavies/macmahon-min-universal-sets, commit
`d8856c97e43e6fa66383c81b8ac4f5bd1c285bc8`. Module paths and proof engineering
have been adapted for the pool. Proofs were primarily AI generated under the
author's direction; see the upstream `formalization.yaml`.

The original conjectures are Conjectures 4 and 8 of Inga Johnson and Erika Roldán,
*Solution Numbers for Eight Blocks to Madness Puzzle* (arXiv:2407.13208v1).
Kazuya Haraguchi proved the minimum size twelve (arXiv:1408.3696v2).
The formalization uses finite signed-axis geometry. The upstream computational
target-count histograms are not part of these Lean theorems.
-/
