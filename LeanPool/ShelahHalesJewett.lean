/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.ShelahHalesJewett.Ackermann

/-!
# Shelah's bound for the Hales–Jewett numbers

Source: doi:10.1090/S0894-0347-1988-0929498-X, url:https://github.com/gdahia/ShelahHalesJewett/tree/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45
Authors: Gabriel Dahia
Status: verified
Main declarations: `Combinatorics.Line.exists_mono_of_shelahBound_le`,
  `Combinatorics.Line.shelahBound_lt_ack`, `Combinatorics.Line.exists_mono_of_ack_le`
Tags: combinatorics, ramsey-theory, hales-jewett, ackermann-function
MSC: 05D10, 03D20
-/

/-!
## Upstream attribution

Adapted for Lean Pool from upstream commit `8a91fc0e8a9617f8ade16ccb3b56e543990c9f45` by
moving the library under `LeanPool.ShelahHalesJewett`. The upstream Palomar `Challenge` and
`Solution` modules are omitted: `Solution` only restates
`Combinatorics.Line.exists_mono_of_ack_le` for words indexed by `Fin n` under a primed name.
-/
