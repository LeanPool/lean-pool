/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderAeLimit
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderAssembly

/-!
# CubeSchauderClose

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the assembly at **one** residue

`CubeSchauderAssembly.zeroDatumCubeSchauder_of_residues` reduces
`ZeroDatumCubeSchauder` to two named residues:

* `hE` — the Campanato datum at every base point of `□_m`;
* `hae` — the almost-everywhere identification `Ψ = ∇w`.

`CubeSchauderAeLimit.ae_campanatoSlopeLimit_eq_grad` proves `hae` **off `hE`
alone**.  This module performs that substitution once and for all: the route
now carries exactly **one** residue, the Campanato datum, and every other
ingredient of the zero-datum core is discharged.

```text
  hE at every z ∈ □_m, every j ≤ m+1   ⟹   ZeroDatumCubeSchauder d (zeroDatumRouteConst d C)
```

## References

* ABK26; `Algsuperdiff/Frozen/External/CubeSchauder.lean`.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory Filter Topology
open HCPolySupport
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-- **`ZeroDatumCubeSchauder` off the Campanato datum alone.**

The `a.e.` identification residue of
`CubeSchauderAssembly.zeroDatumCubeSchauder_of_residues` is discharged by
`CubeSchauderAeLimit.ae_campanatoSlopeLimit_eq_grad`, which consumes exactly the
Campanato datum that the first residue already supplies.  What remains is a
single hypothesis: the Campanato bound at **every** base point of `□_m`. -/
theorem zeroDatumCubeSchauder_of_campanato (hd : 0 < d) {C : ℝ} (hC : 0 ≤ C)
    (hres : ∀ (m : ℤ) (G : Vec d → Vec d) (KG : ℝ), 0 ≤ KG →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) KG G →
      ∃ w : H10Function (openCubeSet (originCube d m)),
        IsDivFormWeakSolutionOn (fun _ => (1 : Mat d)) (openCubeSet (originCube d m))
            w.toH1Function G ∧
          (∀ z ∈ openCubeSet (originCube d m), ∀ j : ℤ, j ≤ m + 1 →
            affineExcess (truncatedWindow z m j) w.toH1Function.toFun
              ≤ C * KG * Real.sqrt ((3 : ℝ) ^ j))) :
    ZeroDatumCubeSchauder d (zeroDatumRouteConst d C) := by
  refine zeroDatumCubeSchauder_of_residues hd hC ?_
  intro m G KG hKG hG
  obtain ⟨w, hw, hE⟩ := hres m G KG hKG hG
  exact ⟨w, hw, hE,
    ae_campanatoSlopeLimit_eq_grad hd w.toH1Function (mul_nonneg hC hKG) hE⟩

end

end Algsuperdiff.Section4.Provider.Schauder
