/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.DiamondCellDomain
public import LeanPool.ApollonianSuperharmonic.ProtoTile

-- [TABLET NODE: DiamondTile]

/-!
# DiamondTile

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The explicit diamond prototile of parameter $k$ is the prototile whose cell
set is $D^{\mathrm D}_k$ and whose auxiliary anchor is $0$.  For $k>0$ the
cell set is nonempty.
-/
def DiamondTile (k : Nat) : ProtoTile :=
-- BODY
  ⟨DiamondCellDomain k, 0⟩

end ApollonianSuperharmonic

end
