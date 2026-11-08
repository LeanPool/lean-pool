/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.GrahamRothschild
public import LeanPool.DensityHalesJewett.Main

/-!
# The density Hales–Jewett theorem and Szemerédi's theorem

Source: arxiv:1209.4986, doi:10.1093/imrn/rnt041, url:https://github.com/gdahia/DensityHalesJewett/tree/478533c44dbfbb286362cb37e19b0ba53fdc5120
Authors: Gabriel Dahia
Status: verified
Main declarations: `Combinatorics.Line.exists_of_density`, `Combinatorics.Line.dhjNumber_le_ack`,
  `Combinatorics.ArithmeticProgression.exists_of_density_nat`,
  `Combinatorics.ArithmeticProgression.exists_many_of_density_nat`
Tags: combinatorics, ramsey-theory, hales-jewett, szemeredi-theorem, density-increment
MSC: 05D10, 05A05, 11B75, 68R15
-/

/-!
## Upstream attribution

Adapted for Lean Pool from upstream commit `478533c44dbfbb286362cb37e19b0ba53fdc5120` by moving
the library under `LeanPool.DensityHalesJewett` and importing Shelah's bound from
`LeanPool.ShelahHalesJewett`. `pullback` is defined from `parameterPreimage`, as in the earlier
Lean Pool version of this project. The upstream Palomar `Challenge` and `Solution` modules are
omitted: `Solution` only restates `Combinatorics.Line.exists_of_density` and
`Combinatorics.ArithmeticProgression.exists_of_density_nat` under primed names.
-/
