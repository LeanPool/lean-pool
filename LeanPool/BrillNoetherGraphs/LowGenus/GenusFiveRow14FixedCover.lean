/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveClosedCover
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCoreAtlas
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow14CoverReceipts
import LeanPool.BrillNoetherGraphs.LowGenus.CompactCellTreeLookup
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.IndexedClosedCheck

/-! **Independent generated check.** The main row-14 proof is the readable
`GenusFiveRow14` construction via `ConfigurationBananaTail`; this module gives
an additional exact replay.

Generated exact replay of the fixed AR row-14 divisor.
`cells_check` and `tree_check` replay every arithmetic obligation in the kernel. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow14FixedCover

open Utilities

open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

/-- Decode an integer coefficient list as a twelve-variable affine form: the first entry is the
constant and missing entries are zero. -/
def aff (data : List ℤ) : ExplicitPotential.AffineForm 12 where
  fixedValue := data.getD 0 0
  coefficient := fun coordinate => data.getD (coordinate.val + 1) 0

/-- The fixed degree-four row-14 divisor, with one chip at each of vertices zero, three, five,
and seven. -/
def rowDivisor : Fin 8 → ℤ := fun vertex =>
  ([1, 0, 0, 1, 0, 1, 0, 1] : List ℤ).getD vertex.val 0

/-- The zero endpoint slopes and zero core potential used for an out-of-range witness-table
lookup. -/
def defaultWitness : AnchorWitness 12 8 12 :=
  { alpha := fun _ => 0, beta := fun _ => 0, potential := fun _ => 0 }

/-- Endpoint-slope witness 0 for the row-14 closed cover: `alpha` is zero. `beta` is zero. The
affine potential is zero. -/
def witness0 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [], [], [],
      []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 1 for the row-14 closed cover: `alpha` is -1 at slots 0, 6; 1 at
slots 7, and zero elsewhere. `beta` is -1 at slots 7, and zero elsewhere. The nonzero affine
potentials occur at vertices 1, 6, 7. -/
def witness1 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, 0, 0, 0, 0, 0, 0, -1], [], [], [], [], [0, 0, 0,
      0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 2 for the row-14 closed cover: `alpha` is -1 at slots 4; 1 at slots
10, and zero elsewhere. `beta` is -1 at slots 5, 10, and zero elsewhere. The nonzero affine
potentials occur at vertices 2. -/
def witness2 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], [], [],
      [], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 3 for the row-14 closed cover: `alpha` is -1 at slots 8, 11, and zero
elsewhere. `beta` is -1 at slots 9; 1 at slots 11, and zero elsewhere. The nonzero affine
potentials occur at vertices 4. -/
def witness3 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [],
      [], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 4 for the row-14 closed cover: `alpha` is -1 at slots 0, 1, 6; 1 at
slots 7, and zero elsewhere. `beta` is -1 at slots 7; 1 at slots 0, and zero elsewhere. The
nonzero affine potentials occur at vertices 1, 6, 7. -/
def witness4 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, 0, 0, 0, 0, 0, 0, -1], [], [], [], [], [0, -1],
      [0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 5 for the row-14 closed cover: `alpha` is -1 at slots 8, 11, and zero
elsewhere. `beta` is -1 at slots 9; 1 at slots 8, and zero elsewhere. The nonzero affine
potentials occur at vertices 4. -/
def witness5 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], [],
      []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 6 for the row-14 closed cover: `alpha` is -1 at slots 4; 1 at slots
5, and zero elsewhere. `beta` is -1 at slots 5, 10, and zero elsewhere. The nonzero affine
potentials occur at vertices 2. -/
def witness6 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, -1], [], [], [], [],
      []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 7 for the row-14 closed cover: `alpha` is -1 at slots 0, 6; 1 at
slots 7, and zero elsewhere. `beta` is -1 at slots 1, 7; 1 at slots 0, and zero elsewhere. The
nonzero affine potentials occur at vertices 1, 6, 7. -/
def witness7 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, 0, 0, 0, 0, 0, 0, -1], [], [], [], [], [0, -1],
      [0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 8 for the row-14 closed cover: `alpha` is -1 at slots 0, 2, 3, 6; 1
at slots 1, 7, and zero elsewhere. `beta` is -1 at slots 1, 7; 1 at slots 3, and zero elsewhere.
The nonzero affine potentials occur at vertices 1, 6, 7. -/
def witness8 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 1, -1, -1, 0, 0, -1, 1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, -1, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, 0, 0, 0, 0, 0, 0, -1], [], [], [], [], [0, 0, -1,
      0, -1, 0, 0, 0, -1], [0, 0, -1, 0, 0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 9 for the row-14 closed cover: `alpha` is -1 at slots 0, 2, 3, 6; 1
at slots 1, 7, and zero elsewhere. `beta` is -1 at slots 1, 7; 1 at slots 0, and zero elsewhere.
The nonzero affine potentials occur at vertices 1, 6, 7. -/
def witness9 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 1, -1, -1, 0, 0, -1, 1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, 0, 0, 0, 0, 0, 0, -1], [], [], [], [], [0, -1],
      [0, 0, -1, 0, 0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 10 for the row-14 closed cover: `alpha` is -1 at slots 0, 2, 3, 6; 1
at slots 1, 7, and zero elsewhere. `beta` is -1 at slots 1, 7; 1 at slots 2, and zero elsewhere.
The nonzero affine potentials occur at vertices 1, 6, 7. -/
def witness10 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 1, -1, -1, 0, 0, -1, 1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, -1, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, 0, 0, 0, 0, 0, 0, -1], [], [], [], [], [0, 0, -1,
      -1, 0, 0, 0, 0, -1], [0, 0, -1, 0, 0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 11 for the row-14 closed cover: `alpha` is -1 at slots 1, 6; 1 at
slots 7, and zero elsewhere. `beta` is -1 at slots 7, and zero elsewhere. The nonzero affine
potentials occur at vertices 1. -/
def witness11 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, -1, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, 0, 0, 0, 0, 0, 0, -1], [], [], [], [], [],
      []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 12 for the row-14 closed cover: `alpha` is -1 at slots 1, 6, and zero
elsewhere. `beta` is -1 at slots 7; 1 at slots 1, and zero elsewhere. The nonzero affine
potentials occur at vertices 1. -/
def witness12 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, -1], [], [], [], [], [],
      []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 13 for the row-14 closed cover: `alpha` is -1 at slots 0, 6, and zero
elsewhere. `beta` is -1 at slots 7; 1 at slots 0, and zero elsewhere. The nonzero affine
potentials occur at vertices 1, 6, 7. -/
def witness13 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, -1], [], [], [], [], [0, -1], [0,
      -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 14 for the row-14 closed cover: `alpha` is -1 at slots 4, and zero
elsewhere. `beta` is -1 at slots 5, 10; 1 at slots 4, and zero elsewhere. The nonzero affine
potentials occur at vertices 2. -/
def witness14 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 1, -1, 0, 0, 0, 0, -1, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, -1], [], [], [], [],
      []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 15 for the row-14 closed cover: `alpha` is -1 at slots 0, 6, and zero
elsewhere. `beta` is -1 at slots 7; 1 at slots 6, and zero elsewhere. The nonzero affine
potentials occur at vertices 1, 6, 7. -/
def witness15 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, 0, 0, 0, 0, 0, -1], [], [], [], [], [0, 0, 0, 0,
      0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 16 for the row-14 closed cover: `alpha` is -1 at slots 0, 6, and zero
elsewhere. `beta` is -1 at slots 7; 1 at slots 0, 6, and zero elsewhere. The nonzero affine
potentials occur at vertices 1, 6, 7. -/
def witness16 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, 0, 0, 0, 0, 0, -1], [], [], [], [], [0, -1], [0,
      -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 17 for the row-14 closed cover: `alpha` is -1 at slots 0, 6, and zero
elsewhere. `beta` is -1 at slots 1, 7; 1 at slots 0, 6, and zero elsewhere. The nonzero affine
potentials occur at vertices 1, 6, 7. -/
def witness17 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, -1, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, 0, 0, 0, 0, 0, -1], [], [], [], [], [0, -1], [0,
      -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 18 for the row-14 closed cover: `alpha` is -1 at slots 0, 2, 3, 6; 1
at slots 1, and zero elsewhere. `beta` is -1 at slots 1, 7; 1 at slots 3, 6, and zero elsewhere.
The nonzero affine potentials occur at vertices 1, 6, 7. -/
def witness18 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 1, -1, -1, 0, 0, -1, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, -1, 0, 1, 0, 0, 1, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, 0, 0, 0, 0, 0, -1], [], [], [], [], [0, 0, -1, 0,
      -1, 0, 0, -1], [0, 0, -1, 0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 19 for the row-14 closed cover: `alpha` is -1 at slots 0, 2, 3, 6; 1
at slots 1, and zero elsewhere. `beta` is -1 at slots 1, 7; 1 at slots 2, 6, and zero elsewhere.
The nonzero affine potentials occur at vertices 1, 6, 7. -/
def witness19 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 1, -1, -1, 0, 0, -1, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, -1, 1, 0, 0, 0, 1, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, 0, 0, 0, 0, 0, -1], [], [], [], [], [0, 0, -1, -1,
      0, 0, 0, -1], [0, 0, -1, 0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 20 for the row-14 closed cover: `alpha` is -1 at slots 0, 2, 3, 6; 1
at slots 1, and zero elsewhere. `beta` is -1 at slots 1, 7; 1 at slots 0, 6, and zero elsewhere.
The nonzero affine potentials occur at vertices 1, 6, 7. -/
def witness20 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 1, -1, -1, 0, 0, -1, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, -1, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, 0, 0, 0, 0, 0, -1], [], [], [], [], [0, -1], [0,
      0, -1, 0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 21 for the row-14 closed cover: `alpha` is -1 at slots 1, 6, and zero
elsewhere. `beta` is -1 at slots 7; 1 at slots 6, and zero elsewhere. The nonzero affine
potentials occur at vertices 1. -/
def witness21 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, 0, 0, 0, 0, 0, -1], [], [], [], [], [],
      []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 22 for the row-14 closed cover: `alpha` is -1 at slots 0, 1, 6, and
zero elsewhere. `beta` is -1 at slots 7; 1 at slots 0, 6, and zero elsewhere. The nonzero affine
potentials occur at vertices 1, 6, 7. -/
def witness22 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, 0, 0, 0, 0, 0, -1], [], [], [], [], [0, -1], [0,
      -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 23 for the row-14 closed cover: `alpha` is -1 at slots 0, 1, 6, and
zero elsewhere. `beta` is -1 at slots 7; 1 at slots 0, 1, and zero elsewhere. The nonzero affine
potentials occur at vertices 1, 6, 7. -/
def witness23 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, -1, -1], [], [], [], [], [0, -1], [0,
      -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 24 for the row-14 closed cover: `alpha` is -1 at slots 8, 11; 1 at
slots 9, and zero elsewhere. `beta` is -1 at slots 9, and zero elsewhere. The nonzero affine
potentials occur at vertices 4. -/
def witness24 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], [],
      []] : List (List ℤ)).getD vertex.val []) }

/-- The twenty-five endpoint-slope and affine-potential witnesses shared by the row-14
closed-cover cells. -/
def witnesses : List (AnchorWitness 12 8 12) :=
  [witness0, witness1, witness2, witness3, witness4, witness5, witness6, witness7, witness8,
  witness9, witness10, witness11, witness12, witness13, witness14, witness15, witness16, witness17,
  witness18, witness19, witness20, witness21, witness22, witness23, witness24]


/-! Anchor geometry does not depend on the cone; check each used pair once. -/

/-- Witness indices used at each anchor by the generated closed-cover cells. -/
private def witnessGeometryRows : List (List ℕ) :=
  [[0], [1, 11, 12, 15, 21], [2, 6, 14], [0], [3, 5, 24], [0], [4, 7, 8, 9, 10, 13, 16, 17, 18,
   19, 20, 22, 23], [0]]

/-- Every used anchor/witness pair passes the original slope and endpoint checks. -/
private theorem witnessGeometryChecked :
    CertificateData.checkWitnessPool row14Core rowDivisor witnesses defaultWitness
      witnessGeometryRows = true := by
  decide +kernel

/-- Closed-cover cell 0 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 0, 3, 0, 4, 0]`; `cell0_check` verifies its
explicit-potential certificate. -/
def cell0 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 0, 3, 0, 4, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell0_check_indexed : cell0.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11, 16],
     [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12, 18], [], [0, 0, 19, 20, 0,
     0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell0_check :
    cell0.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 0, 3, 0, 4, 0] witnessGeometryChecked (by decide))
      cell0_check_indexed

/-- Closed-cover cell 1 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 0, 5, 0, 4, 0]`; `cell1_check` verifies its
explicit-potential certificate. -/
def cell1 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 0, 5, 0, 4, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell1_check_indexed : cell1.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11, 16],
     [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17, 0, 0, 18, 9], [], [0, 0,
     19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell1_check :
    cell1.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 0, 5, 0, 4, 0] witnessGeometryChecked (by decide))
      cell1_check_indexed

/-- Closed-cover cell 2 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 6, 0, 3, 0, 4, 0]`; `cell2_check` verifies its
explicit-potential certificate. -/
def cell2 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 6, 0, 3, 0, 4, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell2_check_indexed : cell2.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12,
     18], [], [0, 0, 19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell2_check :
    cell2.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 6, 0, 3, 0, 4, 0] witnessGeometryChecked (by decide))
      cell2_check_indexed

/-- Closed-cover cell 3 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 6, 0, 5, 0, 4, 0]`; `cell3_check` verifies its
explicit-potential certificate. -/
def cell3 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 6, 0, 5, 0, 4, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell3_check_indexed : cell3.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17,
     0, 0, 18, 9], [], [0, 0, 19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell3_check :
    cell3.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 6, 0, 5, 0, 4, 0] witnessGeometryChecked (by decide))
      cell3_check_indexed

/-- Closed-cover cell 4 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 0, 3, 0, 7, 0]`; `cell4_check` verifies its
explicit-potential certificate. -/
def cell4 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 0, 3, 0, 7, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell4_check_indexed : cell4.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11, 16],
     [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12, 18], [], [0, 0, 13, 19, 0,
     0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell4_check :
    cell4.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 0, 3, 0, 7, 0] witnessGeometryChecked (by decide))
      cell4_check_indexed

/-- Closed-cover cell 5 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 0, 5, 0, 7, 0]`; `cell5_check` verifies its
explicit-potential certificate. -/
def cell5 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 0, 5, 0, 7, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell5_check_indexed : cell5.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11, 16],
     [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17, 0, 0, 18, 9], [], [0, 0,
     13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell5_check :
    cell5.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 0, 5, 0, 7, 0] witnessGeometryChecked (by decide))
      cell5_check_indexed

/-- Closed-cover cell 6 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 6, 0, 3, 0, 7, 0]`; `cell6_check` verifies its
explicit-potential certificate. -/
def cell6 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 6, 0, 3, 0, 7, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell6_check_indexed : cell6.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12,
     18], [], [0, 0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell6_check :
    cell6.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 6, 0, 3, 0, 7, 0] witnessGeometryChecked (by decide))
      cell6_check_indexed

/-- Closed-cover cell 7 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 6, 0, 5, 0, 7, 0]`; `cell7_check` verifies its
explicit-potential certificate. -/
def cell7 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 6, 0, 5, 0, 7, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell7_check_indexed : cell7.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17,
     0, 0, 18, 9], [], [0, 0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell7_check :
    cell7.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 6, 0, 5, 0, 7, 0] witnessGeometryChecked (by decide))
      cell7_check_indexed

/-- Closed-cover cell 8 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 0, 3, 0, 8, 0]`; `cell8_check` verifies its
explicit-potential certificate. -/
def cell8 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 0, 3, 0, 8, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, -1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell8_check_indexed : cell8.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11, 16],
     [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12, 18], [], [19, 20, 0, 0, 21,
     4, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell8_check :
    cell8.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 0, 3, 0, 8, 0] witnessGeometryChecked (by decide))
      cell8_check_indexed

/-- Closed-cover cell 9 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 0, 3, 0, 9, 0]`; `cell9_check` verifies its
explicit-potential certificate. -/
def cell9 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 0, 3, 0, 9, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, -1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
      aff [0, -1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell9_check_indexed : cell9.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11, 16],
     [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12, 18], [], [0, 0, 0, 0, 19,
     20, 21, 20, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell9_check :
    cell9.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 0, 3, 0, 9, 0] witnessGeometryChecked (by decide))
      cell9_check_indexed

/-- Closed-cover cell 10 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 0, 3, 0, 10, 0]`; `cell10_check` verifies its
explicit-potential certificate. -/
def cell10 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 0, 3, 0, 10, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, -1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell10_check_indexed : cell10.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11, 16],
     [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12, 18], [], [19, 20, 0, 0, 0,
     0, 21, 3, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell10_check :
    cell10.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 0, 3, 0, 10, 0] witnessGeometryChecked (by decide))
      cell10_check_indexed

/-- Closed-cover cell 11 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 0, 5, 0, 8, 0]`; `cell11_check` verifies its
explicit-potential certificate. -/
def cell11 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 0, 5, 0, 8, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, -1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell11_check_indexed : cell11.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11, 16],
     [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17, 0, 0, 18, 9], [], [19, 20,
     0, 0, 21, 4, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell11_check :
    cell11.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 0, 5, 0, 8, 0] witnessGeometryChecked (by decide))
      cell11_check_indexed

/-- Closed-cover cell 12 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 0, 5, 0, 10, 0]`; `cell12_check` verifies its
explicit-potential certificate. -/
def cell12 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 0, 5, 0, 10, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, -1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell12_check_indexed : cell12.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11, 16],
     [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17, 0, 0, 18, 9], [], [19, 20,
     0, 0, 0, 0, 21, 3, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell12_check :
    cell12.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 0, 5, 0, 10, 0] witnessGeometryChecked (by decide))
      cell12_check_indexed

/-- Closed-cover cell 13 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 0, 5, 0, 9, 0]`; `cell13_check` verifies its
explicit-potential certificate. -/
def cell13 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 0, 5, 0, 9, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
      aff [0, -1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell13_check_indexed : cell13.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11, 16],
     [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17, 0, 0, 18, 9], [], [0, 0, 0,
     0, 19, 20, 21, 20, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell13_check :
    cell13.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 0, 5, 0, 9, 0] witnessGeometryChecked (by decide))
      cell13_check_indexed

/-- Closed-cover cell 14 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 6, 0, 3, 0, 8, 0]`; `cell14_check` verifies its
explicit-potential certificate. -/
def cell14 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 6, 0, 3, 0, 8, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, -1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell14_check_indexed : cell14.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12,
     18], [], [19, 20, 0, 0, 21, 4, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell14_check :
    cell14.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 6, 0, 3, 0, 8, 0] witnessGeometryChecked (by decide))
      cell14_check_indexed

/-- Closed-cover cell 15 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 6, 0, 3, 0, 9, 0]`; `cell15_check` verifies its
explicit-potential certificate. -/
def cell15 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 6, 0, 3, 0, 9, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, -1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
      aff [0, -1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell15_check_indexed : cell15.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12,
     18], [], [0, 0, 0, 0, 19, 20, 21, 20, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell15_check :
    cell15.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 6, 0, 3, 0, 9, 0] witnessGeometryChecked (by decide))
      cell15_check_indexed

/-- Closed-cover cell 16 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 6, 0, 5, 0, 8, 0]`; `cell16_check` verifies its
explicit-potential certificate. -/
def cell16 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 6, 0, 5, 0, 8, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, -1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell16_check_indexed : cell16.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17,
     0, 0, 18, 9], [], [19, 20, 0, 0, 21, 4, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell16_check :
    cell16.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 6, 0, 5, 0, 8, 0] witnessGeometryChecked (by decide))
      cell16_check_indexed

/-- Closed-cover cell 17 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 6, 0, 5, 0, 9, 0]`; `cell17_check` verifies its
explicit-potential certificate. -/
def cell17 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 6, 0, 5, 0, 9, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
      aff [0, -1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell17_check_indexed : cell17.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17,
     0, 0, 18, 9], [], [0, 0, 0, 0, 19, 20, 21, 20, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell17_check :
    cell17.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 6, 0, 5, 0, 9, 0] witnessGeometryChecked (by decide))
      cell17_check_indexed

/-- Closed-cover cell 18 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 6, 0, 3, 0, 10, 0]`; `cell18_check` verifies its
explicit-potential certificate. -/
def cell18 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 6, 0, 3, 0, 10, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, -1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell18_check_indexed : cell18.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12,
     18], [], [19, 20, 0, 0, 0, 0, 21, 3, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell18_check :
    cell18.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 6, 0, 3, 0, 10, 0] witnessGeometryChecked (by decide))
      cell18_check_indexed

/-- Closed-cover cell 19 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 6, 0, 5, 0, 10, 0]`; `cell19_check` verifies its
explicit-potential certificate. -/
def cell19 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 6, 0, 5, 0, 10, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, -1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell19_check_indexed : cell19.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17,
     0, 0, 18, 9], [], [19, 20, 0, 0, 0, 0, 21, 3, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell19_check :
    cell19.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 6, 0, 5, 0, 10, 0] witnessGeometryChecked (by decide))
      cell19_check_indexed

/-- Closed-cover cell 20 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 0, 3, 0, 4, 0]`; `cell20_check` verifies its
explicit-potential certificate. -/
def cell20 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 0, 3, 0, 4, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell20_check_indexed : cell20.certificate.checkClosedRows 4
    [[], [0, 0, 13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11, 16],
     [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12, 18], [], [0, 0, 19, 20, 0,
     0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell20_check :
    cell20.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 0, 3, 0, 4, 0] witnessGeometryChecked (by decide))
      cell20_check_indexed

/-- Closed-cover cell 21 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 0, 5, 0, 4, 0]`; `cell21_check` verifies its
explicit-potential certificate. -/
def cell21 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 0, 5, 0, 4, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell21_check_indexed : cell21.certificate.checkClosedRows 4
    [[], [0, 0, 13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11, 16],
     [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17, 0, 0, 18, 9], [], [0, 0,
     19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell21_check :
    cell21.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 0, 5, 0, 4, 0] witnessGeometryChecked (by decide))
      cell21_check_indexed

/-- Closed-cover cell 22 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 6, 0, 3, 0, 4, 0]`; `cell22_check` verifies its
explicit-potential certificate. -/
def cell22 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 6, 0, 3, 0, 4, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell22_check_indexed : cell22.certificate.checkClosedRows 4
    [[], [0, 0, 13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12,
     18], [], [0, 0, 19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell22_check :
    cell22.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 6, 0, 3, 0, 4, 0] witnessGeometryChecked (by decide))
      cell22_check_indexed

/-- Closed-cover cell 23 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 6, 0, 5, 0, 4, 0]`; `cell23_check` verifies its
explicit-potential certificate. -/
def cell23 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 6, 0, 5, 0, 4, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell23_check_indexed : cell23.certificate.checkClosedRows 4
    [[], [0, 0, 13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17,
     0, 0, 18, 9], [], [0, 0, 19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell23_check :
    cell23.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 6, 0, 5, 0, 4, 0] witnessGeometryChecked (by decide))
      cell23_check_indexed

/-- Closed-cover cell 24 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 12, 2, 0, 3, 0, 13, 0]`; `cell24_check` verifies its
explicit-potential certificate. -/
def cell24 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 12, 2, 0, 3, 0, 13, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell24_check_indexed : cell24.certificate.checkClosedRows 4
    [[], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 2, 2, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12, 18], [], [0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 19, 1, 1, 20]] = true := by
  decide +kernel

theorem cell24_check :
    cell24.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 12, 2, 0, 3, 0, 13, 0] witnessGeometryChecked (by decide))
      cell24_check_indexed

/-- Closed-cover cell 25 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 12, 2, 0, 5, 0, 13, 0]`; `cell25_check` verifies its
explicit-potential certificate. -/
def cell25 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 12, 2, 0, 5, 0, 13, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell25_check_indexed : cell25.certificate.checkClosedRows 4
    [[], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 2, 2, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17, 0, 0, 18, 9], [], [0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 1, 1, 20]] = true := by
  decide +kernel

theorem cell25_check :
    cell25.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 12, 2, 0, 5, 0, 13, 0] witnessGeometryChecked (by decide))
      cell25_check_indexed

/-- Closed-cover cell 26 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 12, 6, 0, 3, 0, 13, 0]`; `cell26_check` verifies its
explicit-potential certificate. -/
def cell26 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 12, 6, 0, 3, 0, 13, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell26_check_indexed : cell26.certificate.checkClosedRows 4
    [[], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 2, 2, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12,
     12, 18], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 1, 1, 20]] = true := by
  decide +kernel

theorem cell26_check :
    cell26.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 12, 6, 0, 3, 0, 13, 0] witnessGeometryChecked (by decide))
      cell26_check_indexed

/-- Closed-cover cell 27 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 12, 6, 0, 5, 0, 13, 0]`; `cell27_check` verifies its
explicit-potential certificate. -/
def cell27 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 12, 6, 0, 5, 0, 13, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell27_check_indexed : cell27.certificate.checkClosedRows 4
    [[], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 2, 2, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
     17, 0, 0, 18, 9], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 1, 1, 20]] = true := by
  decide +kernel

theorem cell27_check :
    cell27.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 12, 6, 0, 5, 0, 13, 0] witnessGeometryChecked (by decide))
      cell27_check_indexed

/-- Closed-cover cell 28 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 14, 0, 3, 0, 4, 0]`; `cell28_check` verifies its
explicit-potential certificate. -/
def cell28 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 14, 0, 3, 0, 4, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell28_check_indexed : cell28.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12,
     18], [], [0, 0, 19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell28_check :
    cell28.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 14, 0, 3, 0, 4, 0] witnessGeometryChecked (by decide))
      cell28_check_indexed

/-- Closed-cover cell 29 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 14, 0, 5, 0, 4, 0]`; `cell29_check` verifies its
explicit-potential certificate. -/
def cell29 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 14, 0, 5, 0, 4, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell29_check_indexed : cell29.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17,
     0, 0, 18, 9], [], [0, 0, 19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell29_check :
    cell29.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 14, 0, 5, 0, 4, 0] witnessGeometryChecked (by decide))
      cell29_check_indexed

/-- Closed-cover cell 30 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 14, 0, 3, 0, 7, 0]`; `cell30_check` verifies its
explicit-potential certificate. -/
def cell30 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 14, 0, 3, 0, 7, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell30_check_indexed : cell30.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12,
     18], [], [0, 0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell30_check :
    cell30.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 14, 0, 3, 0, 7, 0] witnessGeometryChecked (by decide))
      cell30_check_indexed

/-- Closed-cover cell 31 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 14, 0, 5, 0, 7, 0]`; `cell31_check` verifies its
explicit-potential certificate. -/
def cell31 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 14, 0, 5, 0, 7, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell31_check_indexed : cell31.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17,
     0, 0, 18, 9], [], [0, 0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell31_check :
    cell31.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 14, 0, 5, 0, 7, 0] witnessGeometryChecked (by decide))
      cell31_check_indexed

/-- Closed-cover cell 32 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 14, 0, 3, 0, 8, 0]`; `cell32_check` verifies its
explicit-potential certificate. -/
def cell32 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 14, 0, 3, 0, 8, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, -1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell32_check_indexed : cell32.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12,
     18], [], [19, 20, 0, 0, 21, 4, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell32_check :
    cell32.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 14, 0, 3, 0, 8, 0] witnessGeometryChecked (by decide))
      cell32_check_indexed

/-- Closed-cover cell 33 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 14, 0, 3, 0, 9, 0]`; `cell33_check` verifies its
explicit-potential certificate. -/
def cell33 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 14, 0, 3, 0, 9, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, -1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
      aff [0, -1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell33_check_indexed : cell33.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12,
     18], [], [0, 0, 0, 0, 19, 20, 21, 20, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell33_check :
    cell33.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 14, 0, 3, 0, 9, 0] witnessGeometryChecked (by decide))
      cell33_check_indexed

/-- Closed-cover cell 34 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 14, 0, 5, 0, 8, 0]`; `cell34_check` verifies its
explicit-potential certificate. -/
def cell34 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 14, 0, 5, 0, 8, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, -1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell34_check_indexed : cell34.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17,
     0, 0, 18, 9], [], [19, 20, 0, 0, 21, 4, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell34_check :
    cell34.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 14, 0, 5, 0, 8, 0] witnessGeometryChecked (by decide))
      cell34_check_indexed

/-- Closed-cover cell 35 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 14, 0, 5, 0, 9, 0]`; `cell35_check` verifies its
explicit-potential certificate. -/
def cell35 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 14, 0, 5, 0, 9, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
      aff [0, -1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell35_check_indexed : cell35.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17,
     0, 0, 18, 9], [], [0, 0, 0, 0, 19, 20, 21, 20, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell35_check :
    cell35.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 14, 0, 5, 0, 9, 0] witnessGeometryChecked (by decide))
      cell35_check_indexed

/-- Closed-cover cell 36 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 14, 0, 3, 0, 10, 0]`; `cell36_check` verifies its
explicit-potential certificate. -/
def cell36 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 14, 0, 3, 0, 10, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, -1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell36_check_indexed : cell36.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12,
     18], [], [19, 20, 0, 0, 0, 0, 21, 3, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell36_check :
    cell36.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 14, 0, 3, 0, 10, 0] witnessGeometryChecked (by decide))
      cell36_check_indexed

/-- Closed-cover cell 37 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 14, 0, 5, 0, 10, 0]`; `cell37_check` verifies its
explicit-potential certificate. -/
def cell37 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 14, 0, 5, 0, 10, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, -1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell37_check_indexed : cell37.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17,
     0, 0, 18, 9], [], [19, 20, 0, 0, 0, 0, 21, 3, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell37_check :
    cell37.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 14, 0, 5, 0, 10, 0] witnessGeometryChecked (by decide))
      cell37_check_indexed

/-- Closed-cover cell 38 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 14, 0, 3, 0, 4, 0]`; `cell38_check` verifies its
explicit-potential certificate. -/
def cell38 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 14, 0, 3, 0, 4, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell38_check_indexed : cell38.certificate.checkClosedRows 4
    [[], [0, 0, 13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12,
     18], [], [0, 0, 19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell38_check :
    cell38.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 14, 0, 3, 0, 4, 0] witnessGeometryChecked (by decide))
      cell38_check_indexed

/-- Closed-cover cell 39 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 14, 0, 5, 0, 4, 0]`; `cell39_check` verifies its
explicit-potential certificate. -/
def cell39 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 14, 0, 5, 0, 4, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell39_check_indexed : cell39.certificate.checkClosedRows 4
    [[], [0, 0, 13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17,
     0, 0, 18, 9], [], [0, 0, 19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell39_check :
    cell39.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 14, 0, 5, 0, 4, 0] witnessGeometryChecked (by decide))
      cell39_check_indexed

/-- Closed-cover cell 40 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 12, 14, 0, 3, 0, 13, 0]`; `cell40_check` verifies
its explicit-potential certificate. -/
def cell40 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 12, 14, 0, 3, 0, 13, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell40_check_indexed : cell40.certificate.checkClosedRows 4
    [[], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 2, 2, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12,
     12, 18], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 1, 1, 20]] = true := by
  decide +kernel

theorem cell40_check :
    cell40.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 12, 14, 0, 3, 0, 13, 0] witnessGeometryChecked (by decide))
      cell40_check_indexed

/-- Closed-cover cell 41 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 12, 14, 0, 5, 0, 13, 0]`; `cell41_check` verifies
its explicit-potential certificate. -/
def cell41 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 12, 14, 0, 5, 0, 13, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell41_check_indexed : cell41.certificate.checkClosedRows 4
    [[], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 2, 2, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
     17, 0, 0, 18, 9], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 1, 1, 20]] = true := by
  decide +kernel

theorem cell41_check :
    cell41.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 12, 14, 0, 5, 0, 13, 0] witnessGeometryChecked (by decide))
      cell41_check_indexed

/-- Closed-cover cell 42 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 2, 0, 3, 0, 16, 0]`; `cell42_check` verifies its
explicit-potential certificate. -/
def cell42 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 2, 0, 3, 0, 16, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell42_check_indexed : cell42.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12, 18], [], [0, 0, 13, 19,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell42_check :
    cell42.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 2, 0, 3, 0, 16, 0] witnessGeometryChecked (by decide))
      cell42_check_indexed

/-- Closed-cover cell 43 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 6, 0, 3, 0, 16, 0]`; `cell43_check` verifies its
explicit-potential certificate. -/
def cell43 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 6, 0, 3, 0, 16, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell43_check_indexed : cell43.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12,
     12, 18], [], [0, 0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell43_check :
    cell43.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 6, 0, 3, 0, 16, 0] witnessGeometryChecked (by decide))
      cell43_check_indexed

/-- Closed-cover cell 44 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 14, 0, 3, 0, 16, 0]`; `cell44_check` verifies
its explicit-potential certificate. -/
def cell44 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 14, 0, 3, 0, 16, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell44_check_indexed : cell44.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12,
     12, 18], [], [0, 0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell44_check :
    cell44.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 14, 0, 3, 0, 16, 0] witnessGeometryChecked (by decide))
      cell44_check_indexed

/-- Closed-cover cell 45 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 2, 0, 3, 0, 17, 0]`; `cell45_check` verifies its
explicit-potential certificate. -/
def cell45 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 2, 0, 3, 0, 17, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell45_check_indexed : cell45.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12, 18], [], [0, 0, 13, 19,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell45_check :
    cell45.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 2, 0, 3, 0, 17, 0] witnessGeometryChecked (by decide))
      cell45_check_indexed

/-- Closed-cover cell 46 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 6, 0, 3, 0, 17, 0]`; `cell46_check` verifies its
explicit-potential certificate. -/
def cell46 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 6, 0, 3, 0, 17, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell46_check_indexed : cell46.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12,
     12, 18], [], [0, 0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell46_check :
    cell46.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 6, 0, 3, 0, 17, 0] witnessGeometryChecked (by decide))
      cell46_check_indexed

/-- Closed-cover cell 47 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 14, 0, 3, 0, 17, 0]`; `cell47_check` verifies
its explicit-potential certificate. -/
def cell47 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 14, 0, 3, 0, 17, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell47_check_indexed : cell47.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12,
     12, 18], [], [0, 0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell47_check :
    cell47.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 14, 0, 3, 0, 17, 0] witnessGeometryChecked (by decide))
      cell47_check_indexed

/-- Closed-cover cell 48 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 2, 0, 3, 0, 18, 0]`; `cell48_check` verifies its
explicit-potential certificate. -/
def cell48 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 2, 0, 3, 0, 18, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, -1, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell48_check_indexed : cell48.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12, 18], [], [19, 20, 0, 0,
     21, 4, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell48_check :
    cell48.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 2, 0, 3, 0, 18, 0] witnessGeometryChecked (by decide))
      cell48_check_indexed

/-- Closed-cover cell 49 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 6, 0, 3, 0, 18, 0]`; `cell49_check` verifies its
explicit-potential certificate. -/
def cell49 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 6, 0, 3, 0, 18, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, -1, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell49_check_indexed : cell49.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12,
     12, 18], [], [19, 20, 0, 0, 21, 4, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell49_check :
    cell49.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 6, 0, 3, 0, 18, 0] witnessGeometryChecked (by decide))
      cell49_check_indexed

/-- Closed-cover cell 50 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 14, 0, 3, 0, 18, 0]`; `cell50_check` verifies
its explicit-potential certificate. -/
def cell50 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 14, 0, 3, 0, 18, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, -1, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell50_check_indexed : cell50.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12,
     12, 18], [], [19, 20, 0, 0, 21, 4, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell50_check :
    cell50.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 14, 0, 3, 0, 18, 0] witnessGeometryChecked (by decide))
      cell50_check_indexed

/-- Closed-cover cell 51 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 2, 0, 3, 0, 19, 0]`; `cell51_check` verifies its
explicit-potential certificate. -/
def cell51 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 2, 0, 3, 0, 19, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, -1, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell51_check_indexed : cell51.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12, 18], [], [19, 20, 0, 0,
     0, 0, 21, 3, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell51_check :
    cell51.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 2, 0, 3, 0, 19, 0] witnessGeometryChecked (by decide))
      cell51_check_indexed

/-- Closed-cover cell 52 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 6, 0, 3, 0, 19, 0]`; `cell52_check` verifies its
explicit-potential certificate. -/
def cell52 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 6, 0, 3, 0, 19, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, -1, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell52_check_indexed : cell52.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12,
     12, 18], [], [19, 20, 0, 0, 0, 0, 21, 3, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell52_check :
    cell52.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 6, 0, 3, 0, 19, 0] witnessGeometryChecked (by decide))
      cell52_check_indexed

/-- Closed-cover cell 53 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 14, 0, 3, 0, 19, 0]`; `cell53_check` verifies
its explicit-potential certificate. -/
def cell53 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 14, 0, 3, 0, 19, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, -1, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell53_check_indexed : cell53.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12,
     12, 18], [], [19, 20, 0, 0, 0, 0, 21, 3, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell53_check :
    cell53.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 14, 0, 3, 0, 19, 0] witnessGeometryChecked (by decide))
      cell53_check_indexed

/-- Closed-cover cell 54 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 2, 0, 3, 0, 20, 0]`; `cell54_check` verifies its
explicit-potential certificate. -/
def cell54 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 2, 0, 3, 0, 20, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, -1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
      aff [0, -1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell54_check_indexed : cell54.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12, 18], [], [0, 0, 0, 0,
     19, 20, 21, 20, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell54_check :
    cell54.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 2, 0, 3, 0, 20, 0] witnessGeometryChecked (by decide))
      cell54_check_indexed

/-- Closed-cover cell 55 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 6, 0, 3, 0, 20, 0]`; `cell55_check` verifies its
explicit-potential certificate. -/
def cell55 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 6, 0, 3, 0, 20, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, -1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
      aff [0, -1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell55_check_indexed : cell55.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12,
     12, 18], [], [0, 0, 0, 0, 19, 20, 21, 20, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell55_check :
    cell55.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 6, 0, 3, 0, 20, 0] witnessGeometryChecked (by decide))
      cell55_check_indexed

/-- Closed-cover cell 56 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 14, 0, 3, 0, 20, 0]`; `cell56_check` verifies
its explicit-potential certificate. -/
def cell56 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 14, 0, 3, 0, 20, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, -1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
      aff [0, -1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell56_check_indexed : cell56.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12,
     12, 18], [], [0, 0, 0, 0, 19, 20, 21, 20, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell56_check :
    cell56.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 14, 0, 3, 0, 20, 0] witnessGeometryChecked (by decide))
      cell56_check_indexed

/-- Closed-cover cell 57 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 21, 2, 0, 3, 0, 22, 0]`; `cell57_check` verifies its
explicit-potential certificate. -/
def cell57 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 21, 2, 0, 3, 0, 22, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell57_check_indexed : cell57.certificate.checkClosedRows 4
    [[], [0, 0, 13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12, 12, 18], [], [0, 0, 19, 20,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell57_check :
    cell57.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 21, 2, 0, 3, 0, 22, 0] witnessGeometryChecked (by decide))
      cell57_check_indexed

/-- Closed-cover cell 58 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 21, 6, 0, 3, 0, 22, 0]`; `cell58_check` verifies its
explicit-potential certificate. -/
def cell58 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 21, 6, 0, 3, 0, 22, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell58_check_indexed : cell58.certificate.checkClosedRows 4
    [[], [0, 0, 13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12,
     12, 18], [], [0, 0, 19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell58_check :
    cell58.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 21, 6, 0, 3, 0, 22, 0] witnessGeometryChecked (by decide))
      cell58_check_indexed

/-- Closed-cover cell 59 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 21, 14, 0, 3, 0, 22, 0]`; `cell59_check` verifies
its explicit-potential certificate. -/
def cell59 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 21, 14, 0, 3, 0, 22, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell59_check_indexed : cell59.certificate.checkClosedRows 4
    [[], [0, 0, 13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 12,
     12, 18], [], [0, 0, 19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell59_check :
    cell59.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 21, 14, 0, 3, 0, 22, 0] witnessGeometryChecked (by decide))
      cell59_check_indexed

/-- Closed-cover cell 60 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 2, 0, 5, 0, 23, 0]`; `cell60_check` verifies its
explicit-potential certificate. -/
def cell60 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 2, 0, 5, 0, 23, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell60_check_indexed : cell60.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17, 0, 0, 18, 9], [], [0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20, 20, 21]] = true := by
  decide +kernel

theorem cell60_check :
    cell60.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 2, 0, 5, 0, 23, 0] witnessGeometryChecked (by decide))
      cell60_check_indexed

/-- Closed-cover cell 61 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 2, 0, 5, 0, 13, 0]`; `cell61_check` verifies its
explicit-potential certificate. -/
def cell61 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 2, 0, 5, 0, 13, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell61_check_indexed : cell61.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17, 0, 0, 18, 9], [], [0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 1, 1, 20]] = true := by
  decide +kernel

theorem cell61_check :
    cell61.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 2, 0, 5, 0, 13, 0] witnessGeometryChecked (by decide))
      cell61_check_indexed

/-- Closed-cover cell 62 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 2, 0, 5, 0, 17, 0]`; `cell62_check` verifies its
explicit-potential certificate. -/
def cell62 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 2, 0, 5, 0, 17, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell62_check_indexed : cell62.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17, 0, 0, 18, 9], [], [0,
     0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell62_check :
    cell62.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 2, 0, 5, 0, 17, 0] witnessGeometryChecked (by decide))
      cell62_check_indexed

/-- Closed-cover cell 63 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 2, 0, 5, 0, 18, 0]`; `cell63_check` verifies its
explicit-potential certificate. -/
def cell63 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 2, 0, 5, 0, 18, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, -1, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell63_check_indexed : cell63.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17, 0, 0, 18, 9], [], [19,
     20, 0, 0, 21, 4, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell63_check :
    cell63.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 2, 0, 5, 0, 18, 0] witnessGeometryChecked (by decide))
      cell63_check_indexed

/-- Closed-cover cell 64 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 2, 0, 5, 0, 19, 0]`; `cell64_check` verifies its
explicit-potential certificate. -/
def cell64 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 2, 0, 5, 0, 19, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, -1, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell64_check_indexed : cell64.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17, 0, 0, 18, 9], [], [19,
     20, 0, 0, 0, 0, 21, 3, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell64_check :
    cell64.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 2, 0, 5, 0, 19, 0] witnessGeometryChecked (by decide))
      cell64_check_indexed

/-- Closed-cover cell 65 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 2, 0, 5, 0, 20, 0]`; `cell65_check` verifies its
explicit-potential certificate. -/
def cell65 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 2, 0, 5, 0, 20, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
      aff [0, -1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell65_check_indexed : cell65.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17, 0, 0, 18, 9], [], [0,
     0, 0, 0, 19, 20, 21, 20, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell65_check :
    cell65.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 2, 0, 5, 0, 20, 0] witnessGeometryChecked (by decide))
      cell65_check_indexed

/-- Closed-cover cell 66 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 14, 0, 5, 0, 23, 0]`; `cell66_check` verifies
its explicit-potential certificate. -/
def cell66 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 14, 0, 5, 0, 23, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell66_check_indexed : cell66.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
     17, 0, 0, 18, 9], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20, 20, 21]] = true := by
  decide +kernel

theorem cell66_check :
    cell66.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 14, 0, 5, 0, 23, 0] witnessGeometryChecked (by decide))
      cell66_check_indexed

/-- Closed-cover cell 67 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 14, 0, 5, 0, 13, 0]`; `cell67_check` verifies
its explicit-potential certificate. -/
def cell67 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 14, 0, 5, 0, 13, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell67_check_indexed : cell67.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
     17, 0, 0, 18, 9], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 1, 1, 20]] = true := by
  decide +kernel

theorem cell67_check :
    cell67.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 14, 0, 5, 0, 13, 0] witnessGeometryChecked (by decide))
      cell67_check_indexed

/-- Closed-cover cell 68 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 14, 0, 5, 0, 17, 0]`; `cell68_check` verifies
its explicit-potential certificate. -/
def cell68 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 14, 0, 5, 0, 17, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell68_check_indexed : cell68.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
     17, 0, 0, 18, 9], [], [0, 0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell68_check :
    cell68.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 14, 0, 5, 0, 17, 0] witnessGeometryChecked (by decide))
      cell68_check_indexed

/-- Closed-cover cell 69 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 14, 0, 5, 0, 18, 0]`; `cell69_check` verifies
its explicit-potential certificate. -/
def cell69 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 14, 0, 5, 0, 18, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, -1, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell69_check_indexed : cell69.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
     17, 0, 0, 18, 9], [], [19, 20, 0, 0, 21, 4, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell69_check :
    cell69.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 14, 0, 5, 0, 18, 0] witnessGeometryChecked (by decide))
      cell69_check_indexed

/-- Closed-cover cell 70 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 14, 0, 5, 0, 19, 0]`; `cell70_check` verifies
its explicit-potential certificate. -/
def cell70 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 14, 0, 5, 0, 19, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, -1, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell70_check_indexed : cell70.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
     17, 0, 0, 18, 9], [], [19, 20, 0, 0, 0, 0, 21, 3, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell70_check :
    cell70.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 14, 0, 5, 0, 19, 0] witnessGeometryChecked (by decide))
      cell70_check_indexed

/-- Closed-cover cell 71 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 14, 0, 5, 0, 20, 0]`; `cell71_check` verifies
its explicit-potential certificate. -/
def cell71 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 14, 0, 5, 0, 20, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
      aff [0, -1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell71_check_indexed : cell71.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
     17, 0, 0, 18, 9], [], [0, 0, 0, 0, 19, 20, 21, 20, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell71_check :
    cell71.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 14, 0, 5, 0, 20, 0] witnessGeometryChecked (by decide))
      cell71_check_indexed

/-- Closed-cover cell 72 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 21, 2, 0, 5, 0, 13, 0]`; `cell72_check` verifies its
explicit-potential certificate. -/
def cell72 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 21, 2, 0, 5, 0, 13, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell72_check_indexed : cell72.certificate.checkClosedRows 4
    [[], [0, 0, 13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17, 0, 0, 18, 9], [], [0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 1, 1, 20]] = true := by
  decide +kernel

theorem cell72_check :
    cell72.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 21, 2, 0, 5, 0, 13, 0] witnessGeometryChecked (by decide))
      cell72_check_indexed

/-- Closed-cover cell 73 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 21, 14, 0, 5, 0, 13, 0]`; `cell73_check` verifies
its explicit-potential certificate. -/
def cell73 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 21, 14, 0, 5, 0, 13, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell73_check_indexed : cell73.certificate.checkClosedRows 4
    [[], [0, 0, 13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
     17, 0, 0, 18, 9], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 1, 1, 20]] = true := by
  decide +kernel

theorem cell73_check :
    cell73.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 21, 14, 0, 5, 0, 13, 0] witnessGeometryChecked (by decide))
      cell73_check_indexed

/-- Closed-cover cell 74 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 6, 0, 5, 0, 23, 0]`; `cell74_check` verifies its
explicit-potential certificate. -/
def cell74 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 6, 0, 5, 0, 23, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell74_check_indexed : cell74.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
     17, 0, 0, 18, 9], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20, 20, 21]] = true := by
  decide +kernel

theorem cell74_check :
    cell74.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 6, 0, 5, 0, 23, 0] witnessGeometryChecked (by decide))
      cell74_check_indexed

/-- Closed-cover cell 75 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 6, 0, 5, 0, 13, 0]`; `cell75_check` verifies its
explicit-potential certificate. -/
def cell75 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 6, 0, 5, 0, 13, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell75_check_indexed : cell75.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
     17, 0, 0, 18, 9], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 1, 1, 20]] = true := by
  decide +kernel

theorem cell75_check :
    cell75.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 6, 0, 5, 0, 13, 0] witnessGeometryChecked (by decide))
      cell75_check_indexed

/-- Closed-cover cell 76 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 6, 0, 5, 0, 17, 0]`; `cell76_check` verifies its
explicit-potential certificate. -/
def cell76 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 6, 0, 5, 0, 17, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell76_check_indexed : cell76.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
     17, 0, 0, 18, 9], [], [0, 0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell76_check :
    cell76.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 6, 0, 5, 0, 17, 0] witnessGeometryChecked (by decide))
      cell76_check_indexed

/-- Closed-cover cell 77 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 6, 0, 5, 0, 18, 0]`; `cell77_check` verifies its
explicit-potential certificate. -/
def cell77 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 6, 0, 5, 0, 18, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, -1, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell77_check_indexed : cell77.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
     17, 0, 0, 18, 9], [], [19, 20, 0, 0, 21, 4, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell77_check :
    cell77.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 6, 0, 5, 0, 18, 0] witnessGeometryChecked (by decide))
      cell77_check_indexed

/-- Closed-cover cell 78 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 6, 0, 5, 0, 19, 0]`; `cell78_check` verifies its
explicit-potential certificate. -/
def cell78 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 6, 0, 5, 0, 19, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, -1, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell78_check_indexed : cell78.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
     17, 0, 0, 18, 9], [], [19, 20, 0, 0, 0, 0, 21, 3, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell78_check :
    cell78.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 6, 0, 5, 0, 19, 0] witnessGeometryChecked (by decide))
      cell78_check_indexed

/-- Closed-cover cell 79 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 6, 0, 5, 0, 20, 0]`; `cell79_check` verifies its
explicit-potential certificate. -/
def cell79 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 6, 0, 5, 0, 20, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
      aff [0, -1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell79_check_indexed : cell79.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
     17, 0, 0, 18, 9], [], [0, 0, 0, 0, 19, 20, 21, 20, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell79_check :
    cell79.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 6, 0, 5, 0, 20, 0] witnessGeometryChecked (by decide))
      cell79_check_indexed

/-- Closed-cover cell 80 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 21, 6, 0, 5, 0, 13, 0]`; `cell80_check` verifies its
explicit-potential certificate. -/
def cell80 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 21, 6, 0, 5, 0, 13, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell80_check_indexed : cell80.certificate.checkClosedRows 4
    [[], [0, 0, 13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
     17, 0, 0, 18, 9], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 1, 1, 20]] = true := by
  decide +kernel

theorem cell80_check :
    cell80.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 21, 6, 0, 5, 0, 13, 0] witnessGeometryChecked (by decide))
      cell80_check_indexed

/-- Closed-cover cell 81 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 2, 0, 5, 0, 16, 0]`; `cell81_check` verifies its
explicit-potential certificate. -/
def cell81 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 2, 0, 5, 0, 16, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell81_check_indexed : cell81.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17, 0, 0, 18, 9], [], [0,
     0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell81_check :
    cell81.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 2, 0, 5, 0, 16, 0] witnessGeometryChecked (by decide))
      cell81_check_indexed

/-- Closed-cover cell 82 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 6, 0, 5, 0, 16, 0]`; `cell82_check` verifies its
explicit-potential certificate. -/
def cell82 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 6, 0, 5, 0, 16, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell82_check_indexed : cell82.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
     17, 0, 0, 18, 9], [], [0, 0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell82_check :
    cell82.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 6, 0, 5, 0, 16, 0] witnessGeometryChecked (by decide))
      cell82_check_indexed

/-- Closed-cover cell 83 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 21, 2, 0, 5, 0, 22, 0]`; `cell83_check` verifies its
explicit-potential certificate. -/
def cell83 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 21, 2, 0, 5, 0, 22, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell83_check_indexed : cell83.certificate.checkClosedRows 4
    [[], [0, 0, 13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17, 0, 0, 18, 9], [], [0,
     0, 19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell83_check :
    cell83.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 21, 2, 0, 5, 0, 22, 0] witnessGeometryChecked (by decide))
      cell83_check_indexed

/-- Closed-cover cell 84 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 21, 6, 0, 5, 0, 22, 0]`; `cell84_check` verifies its
explicit-potential certificate. -/
def cell84 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 21, 6, 0, 5, 0, 22, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell84_check_indexed : cell84.certificate.checkClosedRows 4
    [[], [0, 0, 13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
     17, 0, 0, 18, 9], [], [0, 0, 19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell84_check :
    cell84.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 21, 6, 0, 5, 0, 22, 0] witnessGeometryChecked (by decide))
      cell84_check_indexed

/-- Closed-cover cell 85 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 14, 0, 5, 0, 16, 0]`; `cell85_check` verifies
its explicit-potential certificate. -/
def cell85 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 14, 0, 5, 0, 16, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell85_check_indexed : cell85.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
     17, 0, 0, 18, 9], [], [0, 0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell85_check :
    cell85.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 14, 0, 5, 0, 16, 0] witnessGeometryChecked (by decide))
      cell85_check_indexed

/-- Closed-cover cell 86 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 21, 14, 0, 5, 0, 22, 0]`; `cell86_check` verifies
its explicit-potential certificate. -/
def cell86 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 21, 14, 0, 5, 0, 22, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, 1, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell86_check_indexed : cell86.certificate.checkClosedRows 4
    [[], [0, 0, 13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
     17, 0, 0, 18, 9], [], [0, 0, 19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell86_check :
    cell86.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 21, 14, 0, 5, 0, 22, 0] witnessGeometryChecked (by decide))
      cell86_check_indexed

/-- Closed-cover cell 87 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 0, 24, 0, 4, 0]`; `cell87_check` verifies its
explicit-potential certificate. -/
def cell87 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 0, 24, 0, 4, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell87_check_indexed : cell87.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11, 16],
     [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0, 0, 0, 18, 10], [], [0, 0,
     19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell87_check :
    cell87.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 0, 24, 0, 4, 0] witnessGeometryChecked (by decide))
      cell87_check_indexed

/-- Closed-cover cell 88 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 0, 24, 0, 7, 0]`; `cell88_check` verifies its
explicit-potential certificate. -/
def cell88 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 0, 24, 0, 7, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell88_check_indexed : cell88.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11, 16],
     [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0, 0, 0, 18, 10], [], [0, 0,
     13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell88_check :
    cell88.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 0, 24, 0, 7, 0] witnessGeometryChecked (by decide))
      cell88_check_indexed

/-- Closed-cover cell 89 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 0, 24, 0, 8, 0]`; `cell89_check` verifies its
explicit-potential certificate. -/
def cell89 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 0, 24, 0, 8, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, 1, -1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell89_check_indexed : cell89.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11, 16],
     [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0, 0, 0, 18, 10], [], [19,
     20, 0, 0, 21, 4, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell89_check :
    cell89.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 0, 24, 0, 8, 0] witnessGeometryChecked (by decide))
      cell89_check_indexed

/-- Closed-cover cell 90 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 0, 24, 0, 9, 0]`; `cell90_check` verifies its
explicit-potential certificate. -/
def cell90 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 0, 24, 0, 9, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
      aff [0, -1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell90_check_indexed : cell90.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11, 16],
     [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0, 0, 0, 18, 10], [], [0, 0,
     0, 0, 19, 20, 21, 20, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell90_check :
    cell90.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 0, 24, 0, 9, 0] witnessGeometryChecked (by decide))
      cell90_check_indexed

/-- Closed-cover cell 91 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 0, 24, 0, 10, 0]`; `cell91_check` verifies its
explicit-potential certificate. -/
def cell91 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 0, 24, 0, 10, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, 1, -1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell91_check_indexed : cell91.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11, 16],
     [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0, 0, 0, 18, 10], [], [19,
     20, 0, 0, 0, 0, 21, 3, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell91_check :
    cell91.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 0, 24, 0, 10, 0] witnessGeometryChecked (by decide))
      cell91_check_indexed

/-- Closed-cover cell 92 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 0, 24, 0, 4, 0]`; `cell92_check` verifies its
explicit-potential certificate. -/
def cell92 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 0, 24, 0, 4, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell92_check_indexed : cell92.certificate.checkClosedRows 4
    [[], [0, 0, 13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11, 16],
     [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0, 0, 0, 18, 10], [], [0, 0,
     19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell92_check :
    cell92.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 0, 24, 0, 4, 0] witnessGeometryChecked (by decide))
      cell92_check_indexed

/-- Closed-cover cell 93 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 12, 2, 0, 24, 0, 13, 0]`; `cell93_check` verifies
its explicit-potential certificate. -/
def cell93 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 12, 2, 0, 24, 0, 13, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell93_check_indexed : cell93.certificate.checkClosedRows 4
    [[], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 2, 2, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0, 0, 0, 18, 10], [],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 1, 1, 20]] = true := by
  decide +kernel

theorem cell93_check :
    cell93.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 12, 2, 0, 24, 0, 13, 0] witnessGeometryChecked (by decide))
      cell93_check_indexed

/-- Closed-cover cell 94 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 14, 0, 24, 0, 4, 0]`; `cell94_check` verifies its
explicit-potential certificate. -/
def cell94 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 14, 0, 24, 0, 4, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell94_check_indexed : cell94.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0,
     0, 0, 18, 10], [], [0, 0, 19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell94_check :
    cell94.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 14, 0, 24, 0, 4, 0] witnessGeometryChecked (by decide))
      cell94_check_indexed

/-- Closed-cover cell 95 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 14, 0, 24, 0, 7, 0]`; `cell95_check` verifies its
explicit-potential certificate. -/
def cell95 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 14, 0, 24, 0, 7, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell95_check_indexed : cell95.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0,
     0, 0, 18, 10], [], [0, 0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell95_check :
    cell95.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 14, 0, 24, 0, 7, 0] witnessGeometryChecked (by decide))
      cell95_check_indexed

/-- Closed-cover cell 96 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 14, 0, 24, 0, 8, 0]`; `cell96_check` verifies its
explicit-potential certificate. -/
def cell96 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 14, 0, 24, 0, 8, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, 1, -1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell96_check_indexed : cell96.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0,
     0, 0, 18, 10], [], [19, 20, 0, 0, 21, 4, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell96_check :
    cell96.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 14, 0, 24, 0, 8, 0] witnessGeometryChecked (by decide))
      cell96_check_indexed

/-- Closed-cover cell 97 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 14, 0, 24, 0, 9, 0]`; `cell97_check` verifies its
explicit-potential certificate. -/
def cell97 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 14, 0, 24, 0, 9, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
      aff [0, -1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell97_check_indexed : cell97.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0,
     0, 0, 18, 10], [], [0, 0, 0, 0, 19, 20, 21, 20, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell97_check :
    cell97.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 14, 0, 24, 0, 9, 0] witnessGeometryChecked (by decide))
      cell97_check_indexed

/-- Closed-cover cell 98 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 14, 0, 24, 0, 10, 0]`; `cell98_check` verifies
its explicit-potential certificate. -/
def cell98 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 14, 0, 24, 0, 10, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, 1, -1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell98_check_indexed : cell98.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0,
     0, 0, 18, 10], [], [19, 20, 0, 0, 0, 0, 21, 3, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell98_check :
    cell98.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 14, 0, 24, 0, 10, 0] witnessGeometryChecked (by decide))
      cell98_check_indexed

/-- Closed-cover cell 99 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 14, 0, 24, 0, 13, 0]`; `cell99_check` verifies
its explicit-potential certificate. -/
def cell99 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 14, 0, 24, 0, 13, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell99_check_indexed : cell99.certificate.checkClosedRows 4
    [[], [0, 0, 13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0,
     0, 0, 18, 10], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 1, 1, 20]] = true := by
  decide +kernel

theorem cell99_check :
    cell99.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 14, 0, 24, 0, 13, 0] witnessGeometryChecked (by decide))
      cell99_check_indexed

/-- Closed-cover cell 100 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 12, 14, 0, 24, 0, 13, 0]`; `cell100_check` verifies
its explicit-potential certificate. -/
def cell100 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 12, 14, 0, 24, 0, 13, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell100_check_indexed : cell100.certificate.checkClosedRows 4
    [[], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 2, 2, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10,
     0, 0, 0, 0, 18, 10], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 1, 1, 20]] = true := by
  decide +kernel

theorem cell100_check :
    cell100.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 12, 14, 0, 24, 0, 13, 0] witnessGeometryChecked (by decide))
      cell100_check_indexed

/-- Closed-cover cell 101 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 14, 0, 5, 0, 13, 0]`; `cell101_check` verifies
its explicit-potential certificate. -/
def cell101 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 14, 0, 5, 0, 13, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell101_check_indexed : cell101.certificate.checkClosedRows 4
    [[], [0, 0, 13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17,
     0, 0, 18, 9], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 1, 1, 20]] = true := by
  decide +kernel

theorem cell101_check :
    cell101.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 14, 0, 5, 0, 13, 0] witnessGeometryChecked (by decide))
      cell101_check_indexed

/-- Closed-cover cell 102 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 6, 0, 24, 0, 4, 0]`; `cell102_check` verifies its
explicit-potential certificate. -/
def cell102 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 6, 0, 24, 0, 4, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell102_check_indexed : cell102.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0,
     0, 0, 18, 10], [], [0, 0, 19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell102_check :
    cell102.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 6, 0, 24, 0, 4, 0] witnessGeometryChecked (by decide))
      cell102_check_indexed

/-- Closed-cover cell 103 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 6, 0, 24, 0, 7, 0]`; `cell103_check` verifies its
explicit-potential certificate. -/
def cell103 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 6, 0, 24, 0, 7, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell103_check_indexed : cell103.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0,
     0, 0, 18, 10], [], [0, 0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell103_check :
    cell103.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 6, 0, 24, 0, 7, 0] witnessGeometryChecked (by decide))
      cell103_check_indexed

/-- Closed-cover cell 104 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 6, 0, 24, 0, 8, 0]`; `cell104_check` verifies its
explicit-potential certificate. -/
def cell104 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 6, 0, 24, 0, 8, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, 1, -1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell104_check_indexed : cell104.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0,
     0, 0, 18, 10], [], [19, 20, 0, 0, 21, 4, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell104_check :
    cell104.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 6, 0, 24, 0, 8, 0] witnessGeometryChecked (by decide))
      cell104_check_indexed

/-- Closed-cover cell 105 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 6, 0, 24, 0, 9, 0]`; `cell105_check` verifies its
explicit-potential certificate. -/
def cell105 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 6, 0, 24, 0, 9, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
      aff [0, -1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell105_check_indexed : cell105.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0,
     0, 0, 18, 10], [], [0, 0, 0, 0, 19, 20, 21, 20, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell105_check :
    cell105.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 6, 0, 24, 0, 9, 0] witnessGeometryChecked (by decide))
      cell105_check_indexed

/-- Closed-cover cell 106 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 6, 0, 24, 0, 10, 0]`; `cell106_check` verifies
its explicit-potential certificate. -/
def cell106 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 6, 0, 24, 0, 10, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, 1, -1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell106_check_indexed : cell106.certificate.checkClosedRows 4
    [[], [13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0,
     0, 0, 18, 10], [], [19, 20, 0, 0, 0, 0, 21, 3, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell106_check :
    cell106.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 6, 0, 24, 0, 10, 0] witnessGeometryChecked (by decide))
      cell106_check_indexed

/-- Closed-cover cell 107 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 6, 0, 24, 0, 4, 0]`; `cell107_check` verifies
its explicit-potential certificate. -/
def cell107 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 6, 0, 24, 0, 4, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell107_check_indexed : cell107.certificate.checkClosedRows 4
    [[], [0, 0, 13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0,
     0, 0, 18, 10], [], [0, 0, 19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell107_check :
    cell107.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 6, 0, 24, 0, 4, 0] witnessGeometryChecked (by decide))
      cell107_check_indexed

/-- Closed-cover cell 108 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 14, 0, 24, 0, 4, 0]`; `cell108_check` verifies
its explicit-potential certificate. -/
def cell108 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 14, 0, 24, 0, 4, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell108_check_indexed : cell108.certificate.checkClosedRows 4
    [[], [0, 0, 13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0,
     0, 0, 18, 10], [], [0, 0, 19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8]] = true := by
  decide +kernel

theorem cell108_check :
    cell108.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 14, 0, 24, 0, 4, 0] witnessGeometryChecked (by decide))
      cell108_check_indexed

/-- Closed-cover cell 109 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 12, 6, 0, 24, 0, 13, 0]`; `cell109_check` verifies
its explicit-potential certificate. -/
def cell109 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 12, 6, 0, 24, 0, 13, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell109_check_indexed : cell109.certificate.checkClosedRows 4
    [[], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 2, 2, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10,
     0, 0, 0, 0, 18, 10], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 1, 1, 20]] = true := by
  decide +kernel

theorem cell109_check :
    cell109.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 12, 6, 0, 24, 0, 13, 0] witnessGeometryChecked (by decide))
      cell109_check_indexed

/-- Closed-cover cell 110 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 6, 0, 5, 0, 13, 0]`; `cell110_check` verifies
its explicit-potential certificate. -/
def cell110 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 6, 0, 5, 0, 13, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell110_check_indexed : cell110.certificate.checkClosedRows 4
    [[], [0, 0, 13, 8, 0, 0, 0, 0, 0, 0, 0, 0, 14, 8], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17,
     0, 0, 18, 9], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 1, 1, 20]] = true := by
  decide +kernel

theorem cell110_check :
    cell110.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 6, 0, 5, 0, 13, 0] witnessGeometryChecked (by decide))
      cell110_check_indexed

/-- Closed-cover cell 111 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 2, 0, 24, 0, 23, 0]`; `cell111_check` verifies
its explicit-potential certificate. -/
def cell111 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 2, 0, 24, 0, 23, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell111_check_indexed : cell111.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0, 0, 0, 18, 10], [],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20, 20, 21]] = true := by
  decide +kernel

theorem cell111_check :
    cell111.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 2, 0, 24, 0, 23, 0] witnessGeometryChecked (by decide))
      cell111_check_indexed

/-- Closed-cover cell 112 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 2, 0, 24, 0, 13, 0]`; `cell112_check` verifies
its explicit-potential certificate. -/
def cell112 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 2, 0, 24, 0, 13, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell112_check_indexed : cell112.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0, 0, 0, 18, 10], [],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 1, 1, 20]] = true := by
  decide +kernel

theorem cell112_check :
    cell112.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 2, 0, 24, 0, 13, 0] witnessGeometryChecked (by decide))
      cell112_check_indexed

/-- Closed-cover cell 113 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 2, 0, 24, 0, 17, 0]`; `cell113_check` verifies
its explicit-potential certificate. -/
def cell113 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 2, 0, 24, 0, 17, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell113_check_indexed : cell113.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0, 0, 0, 18, 10], [],
     [0, 0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell113_check :
    cell113.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 2, 0, 24, 0, 17, 0] witnessGeometryChecked (by decide))
      cell113_check_indexed

/-- Closed-cover cell 114 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 2, 0, 24, 0, 18, 0]`; `cell114_check` verifies
its explicit-potential certificate. -/
def cell114 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 2, 0, 24, 0, 18, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, 1, -1, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell114_check_indexed : cell114.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0, 0, 0, 18, 10], [],
     [19, 20, 0, 0, 21, 4, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell114_check :
    cell114.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 2, 0, 24, 0, 18, 0] witnessGeometryChecked (by decide))
      cell114_check_indexed

/-- Closed-cover cell 115 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 2, 0, 24, 0, 19, 0]`; `cell115_check` verifies
its explicit-potential certificate. -/
def cell115 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 2, 0, 24, 0, 19, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, 1, -1, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell115_check_indexed : cell115.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0, 0, 0, 18, 10], [],
     [19, 20, 0, 0, 0, 0, 21, 3, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell115_check :
    cell115.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 2, 0, 24, 0, 19, 0] witnessGeometryChecked (by decide))
      cell115_check_indexed

/-- Closed-cover cell 116 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 2, 0, 24, 0, 20, 0]`; `cell116_check` verifies
its explicit-potential certificate. -/
def cell116 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 2, 0, 24, 0, 20, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
      aff [0, -1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell116_check_indexed : cell116.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0, 0, 0, 18, 10], [],
     [0, 0, 0, 0, 19, 20, 21, 20, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell116_check :
    cell116.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 2, 0, 24, 0, 20, 0] witnessGeometryChecked (by decide))
      cell116_check_indexed

/-- Closed-cover cell 117 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 21, 2, 0, 24, 0, 13, 0]`; `cell117_check` verifies
its explicit-potential certificate. -/
def cell117 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 21, 2, 0, 24, 0, 13, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell117_check_indexed : cell117.certificate.checkClosedRows 4
    [[], [0, 0, 13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0, 0, 0, 18, 10], [],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 1, 1, 20]] = true := by
  decide +kernel

theorem cell117_check :
    cell117.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 21, 2, 0, 24, 0, 13, 0] witnessGeometryChecked (by decide))
      cell117_check_indexed

/-- Closed-cover cell 118 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 2, 0, 24, 0, 16, 0]`; `cell118_check` verifies
its explicit-potential certificate. -/
def cell118 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 2, 0, 24, 0, 16, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell118_check_indexed : cell118.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 11, 11,
     16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10, 0, 0, 0, 0, 18, 10], [],
     [0, 0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell118_check :
    cell118.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 2, 0, 24, 0, 16, 0] witnessGeometryChecked (by decide))
      cell118_check_indexed

/-- Closed-cover cell 119 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 6, 0, 24, 0, 16, 0]`; `cell119_check` verifies
its explicit-potential certificate. -/
def cell119 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 6, 0, 24, 0, 16, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell119_check_indexed : cell119.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10,
     0, 0, 0, 0, 18, 10], [], [0, 0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell119_check :
    cell119.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 6, 0, 24, 0, 16, 0] witnessGeometryChecked (by decide))
      cell119_check_indexed

/-- Closed-cover cell 120 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 6, 0, 24, 0, 17, 0]`; `cell120_check` verifies
its explicit-potential certificate. -/
def cell120 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 6, 0, 24, 0, 17, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell120_check_indexed : cell120.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10,
     0, 0, 0, 0, 18, 10], [], [0, 0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell120_check :
    cell120.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 6, 0, 24, 0, 17, 0] witnessGeometryChecked (by decide))
      cell120_check_indexed

/-- Closed-cover cell 121 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 6, 0, 24, 0, 18, 0]`; `cell121_check` verifies
its explicit-potential certificate. -/
def cell121 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 6, 0, 24, 0, 18, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, 1, -1, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell121_check_indexed : cell121.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10,
     0, 0, 0, 0, 18, 10], [], [19, 20, 0, 0, 21, 4, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell121_check :
    cell121.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 6, 0, 24, 0, 18, 0] witnessGeometryChecked (by decide))
      cell121_check_indexed

/-- Closed-cover cell 122 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 6, 0, 24, 0, 19, 0]`; `cell122_check` verifies
its explicit-potential certificate. -/
def cell122 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 6, 0, 24, 0, 19, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, 1, -1, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell122_check_indexed : cell122.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10,
     0, 0, 0, 0, 18, 10], [], [19, 20, 0, 0, 0, 0, 21, 3, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell122_check :
    cell122.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 6, 0, 24, 0, 19, 0] witnessGeometryChecked (by decide))
      cell122_check_indexed

/-- Closed-cover cell 123 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 6, 0, 24, 0, 20, 0]`; `cell123_check` verifies
its explicit-potential certificate. -/
def cell123 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 6, 0, 24, 0, 20, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
      aff [0, -1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell123_check_indexed : cell123.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10,
     0, 0, 0, 0, 18, 10], [], [0, 0, 0, 0, 19, 20, 21, 20, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell123_check :
    cell123.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 6, 0, 24, 0, 20, 0] witnessGeometryChecked (by decide))
      cell123_check_indexed

/-- Closed-cover cell 124 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 21, 6, 0, 24, 0, 22, 0]`; `cell124_check` verifies
its explicit-potential certificate. -/
def cell124 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 21, 6, 0, 24, 0, 22, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, 1, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell124_check_indexed : cell124.certificate.checkClosedRows 4
    [[], [0, 0, 13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 15, 6, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 6, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10,
     0, 0, 0, 0, 18, 10], [], [0, 0, 19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell124_check :
    cell124.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 21, 6, 0, 24, 0, 22, 0] witnessGeometryChecked (by decide))
      cell124_check_indexed

/-- Closed-cover cell 125 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 14, 0, 24, 0, 16, 0]`; `cell125_check` verifies
its explicit-potential certificate. -/
def cell125 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 14, 0, 24, 0, 16, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell125_check_indexed : cell125.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10,
     0, 0, 0, 0, 18, 10], [], [0, 0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell125_check :
    cell125.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 14, 0, 24, 0, 16, 0] witnessGeometryChecked (by decide))
      cell125_check_indexed

/-- Closed-cover cell 126 for the fixed row-14 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 14, 0, 24, 0, 17, 0]`; `cell126_check` verifies
its explicit-potential certificate. -/
def cell126 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 14, 0, 24, 0, 17, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell126_check_indexed : cell126.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10,
     0, 0, 0, 0, 18, 10], [], [0, 0, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell126_check :
    cell126.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 14, 0, 24, 0, 17, 0] witnessGeometryChecked (by decide))
      cell126_check_indexed

/-- Closed-cover cell 127 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 14, 0, 24, 0, 18, 0]`; `cell127_check` verifies
its explicit-potential certificate. -/
def cell127 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 14, 0, 24, 0, 18, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, 1, -1, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell127_check_indexed : cell127.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10,
     0, 0, 0, 0, 18, 10], [], [19, 20, 0, 0, 21, 4, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell127_check :
    cell127.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 14, 0, 24, 0, 18, 0] witnessGeometryChecked (by decide))
      cell127_check_indexed

/-- Closed-cover cell 128 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 14, 0, 24, 0, 19, 0]`; `cell128_check` verifies
its explicit-potential certificate. -/
def cell128 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 14, 0, 24, 0, 19, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, 1, -1, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell128_check_indexed : cell128.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10,
     0, 0, 0, 0, 18, 10], [], [19, 20, 0, 0, 0, 0, 21, 3, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell128_check :
    cell128.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 14, 0, 24, 0, 19, 0] witnessGeometryChecked (by decide))
      cell128_check_indexed

/-- Closed-cover cell 129 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 14, 0, 24, 0, 20, 0]`; `cell129_check` verifies
its explicit-potential certificate. -/
def cell129 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 14, 0, 24, 0, 20, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, -1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
      aff [0, -1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell129_check_indexed : cell129.certificate.checkClosedRows 4
    [[], [13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10,
     0, 0, 0, 0, 18, 10], [], [0, 0, 0, 0, 19, 20, 21, 20, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell129_check :
    cell129.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 14, 0, 24, 0, 20, 0] witnessGeometryChecked (by decide))
      cell129_check_indexed

/-- Closed-cover cell 130 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 21, 14, 0, 24, 0, 22, 0]`; `cell130_check` verifies
its explicit-potential certificate. -/
def cell130 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 21, 14, 0, 24, 0, 22, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
      aff [0, 1, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]] }

private theorem cell130_check_indexed : cell130.certificate.checkClosedRows 4
    [[], [0, 0, 13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 10,
     0, 0, 0, 0, 18, 10], [], [0, 0, 19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 14]] = true := by
  decide +kernel

theorem cell130_check :
    cell130.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row14Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 21, 14, 0, 24, 0, 22, 0] witnessGeometryChecked (by decide))
      cell130_check_indexed

/-- The 131 row-14 closed-cover cells in global index order, covering the full cone of
nonnegative edge lengths. -/
def cells : List (CoordinateCell row14Core) :=
  [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12,
  cell13, cell14, cell15, cell16, cell17, cell18, cell19, cell20, cell21, cell22, cell23, cell24,
  cell25, cell26, cell27, cell28, cell29, cell30, cell31, cell32, cell33, cell34, cell35, cell36,
  cell37, cell38, cell39, cell40, cell41, cell42, cell43, cell44, cell45, cell46, cell47, cell48,
  cell49, cell50, cell51, cell52, cell53, cell54, cell55, cell56, cell57, cell58, cell59, cell60,
  cell61, cell62, cell63, cell64, cell65, cell66, cell67, cell68, cell69, cell70, cell71, cell72,
  cell73, cell74, cell75, cell76, cell77, cell78, cell79, cell80, cell81, cell82, cell83, cell84,
  cell85, cell86, cell87, cell88, cell89, cell90, cell91, cell92, cell93, cell94, cell95, cell96,
  cell97, cell98, cell99, cell100, cell101, cell102, cell103, cell104, cell105, cell106, cell107,
  cell108, cell109, cell110, cell111, cell112, cell113, cell114, cell115, cell116, cell117, cell118,
  cell119, cell120, cell121, cell122, cell123, cell124, cell125, cell126, cell127, cell128, cell129,
  cell130]

/-- The twelve coordinate forms imposing nonnegativity of every edge length, which define the
full domain of the row-14 cover. -/
def base : List (ExplicitPotential.AffineForm 12) :=
  [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0,
  0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0,
  0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0,
  1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
  0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
  0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- The 34 homogeneous affine forms whose signs determine branches of the row-14 decision tree;
coefficients are indexed by the twelve edge lengths. -/
def splitForms : List (ExplicitPotential.AffineForm 12) :=
  [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0], aff
  [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0,
  -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0,
  0, 0, 0, 1, 0, 0, 0, 0, -1, 0], aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 1,
  -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 1, 0, 0, 0, 0,
  0, -1, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 1,
  0, 0, 0, 0, 0], aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, -1, 0, 0, -1, 0,
  0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0,
  0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
  aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff
  [0, 1, -1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0,
  1, -1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0,
  0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, -1, 0,
  0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 1, -1, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, -1, 1, 1, 0,
  0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0,
  0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0], aff [0, -1, 1, 0, 1, 0, 0, 1, 0,
  0, 0, 0, 0]]

theorem splitForm0 : splitForms.getD 0 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1] := by rfl

theorem splitForm1 : splitForms.getD 1 0 = aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0] := by rfl

theorem splitForm2 : splitForms.getD 2 0 = aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0] := by rfl

theorem splitForm3 : splitForms.getD 3 0 = aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] := by rfl

theorem splitForm4 : splitForms.getD 4 0 = aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] := by rfl

theorem splitForm5 : splitForms.getD 5 0 = aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] := by rfl

theorem splitForm6 : splitForms.getD 6 0 = aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0] := by rfl

theorem splitForm7 : splitForms.getD 7 0 = aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] := by rfl

theorem splitForm8 : splitForms.getD 8 0 = aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm9 : splitForms.getD 9 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1] := by rfl

theorem splitForm10 : splitForms.getD 10 0 = aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] := by rfl

theorem splitForm11 : splitForms.getD 11 0 = aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] := by rfl

theorem splitForm12 : splitForms.getD 12 0 = aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] := by rfl

theorem splitForm13 : splitForms.getD 13 0 = aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] := by rfl

theorem splitForm14 :
    splitForms.getD 14 0 = aff [0, 1, -1, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0] := by rfl

theorem splitForm15 : splitForms.getD 15 0 = aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm16 : splitForms.getD 16 0 = aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm17 : splitForms.getD 17 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0] := by rfl

theorem splitForm18 : splitForms.getD 18 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1] := by rfl

theorem splitForm19 : splitForms.getD 19 0 = aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0] := by rfl

theorem splitForm20 : splitForms.getD 20 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0] := by rfl

theorem splitForm21 :
    splitForms.getD 21 0 = aff [0, 1, -1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0] := by rfl

theorem splitForm22 : splitForms.getD 22 0 = aff [0, -1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0] := by rfl

theorem splitForm23 :
    splitForms.getD 23 0 = aff [0, 1, -1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0] := by rfl

theorem splitForm24 : splitForms.getD 24 0 = aff [0, -1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0] := by rfl

theorem splitForm25 : splitForms.getD 25 0 = aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm26 : splitForms.getD 26 0 = aff [0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] := by rfl

theorem splitForm27 : splitForms.getD 27 0 = aff [0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] := by rfl

theorem splitForm28 :
    splitForms.getD 28 0 = aff [0, 1, -1, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0] := by rfl

theorem splitForm29 : splitForms.getD 29 0 = aff [0, -1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0] := by rfl

theorem splitForm30 : splitForms.getD 30 0 = aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] := by rfl

theorem splitForm31 : splitForms.getD 31 0 = aff [0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] := by rfl

theorem splitForm32 : splitForms.getD 32 0 = aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0] := by rfl

theorem splitForm33 : splitForms.getD 33 0 = aff [0, -1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] := by rfl

/-- Subtree splitting on `length[5] - length[10]` in the row-14 length cone, with leaves
selecting cells 0, 1, 2, 3 and Farkas receipts excluding inconsistent sign branches. -/
def treePart0 : CompactCellTree :=
  .split 6
    (.split 9
        (.cell 0 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19])
        (.split 20
            (.cell 1 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38,
              39])
            (.absurd 40)))
    (.split 15
        (.split 9
            (.cell 2 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 37, 35, 36, 41, 38,
              39])
            (.split 20
                (.cell 3 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
                  60, 61])
                (.absurd 62)))
        (.absurd 63))

private theorem treePart0_check_chunked :
    treePart0.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart0_check :
    treePart0.check splitForms farkasReceipts cells
      (((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart0_check_chunked

/-- Subtree splitting on `length[5] - length[10]` in the row-14 length cone, with leaves
selecting cells 4, 5, 6, 7 and Farkas receipts excluding inconsistent sign branches. -/
def treePart1 : CompactCellTree :=
  .split 6
    (.split 9
        (.cell 4 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 37, 36, 41, 35])
        (.split 20
            (.cell 5 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 64, 56, 58, 59, 57])
            (.absurd 62)))
    (.split 15
        (.split 9
            (.cell 6 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 59, 56, 58, 65, 57])
            (.split 20
                (.cell 7 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83,
                  84])
                (.absurd 85)))
        (.absurd 86))

private theorem treePart1_check_chunked :
    treePart1.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart1_check :
    treePart1.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart1_check_chunked

/-- Subtree splitting on `length[8] - length[11]` in the row-14 length cone, with leaves
selecting cells 0, 8, 9, 10, 11, 12, 13 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart2 : CompactCellTree :=
  .split 9
    (.split 7
        (.cell 0 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 64, 56, 59, 65, 60, 87])
        (.split 8
            (.split 21
                (.cell 8 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104,
                  105, 106, 107, 108])
                (.split 22
                    (.cell 9 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
                      123, 124, 125, 126, 127, 128, 129])
                    (.absurd 130)))
            (.split 23
                (.cell 10 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104,
                  105, 106, 131, 108])
                (.split 24
                    (.cell 9 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
                      123, 124, 125, 126, 129, 128, 127])
                    (.absurd 130)))))
    (.split 7
        (.absurd 132)
        (.split 20
            (.split 21
                (.split 8
                    (.cell 11 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121,
                      122, 123, 124, 133, 125, 129, 134, 127])
                    (.split 23
                        (.cell 12 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                          148, 149, 150, 151, 152, 153, 154, 155])
                        (.absurd 156)))
                (.split 22
                    (.cell 13 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121,
                      122, 123, 124, 133, 125, 127, 128, 129])
                    (.split 25
                        (.cell 12 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                          148, 149, 150, 151, 152, 155, 154, 153])
                        (.absurd 156))))
            (.absurd 157)))

private theorem treePart2_check_chunked :
    treePart2.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      1, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0,
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) = true := by
  decide +kernel

theorem treePart2_check :
    treePart2.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      1, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0,
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart2_check_chunked

/-- Contradiction leaf using Farkas receipt 158 to exclude the accumulated affine constraints in
this row-14 branch. -/
def treePart3 : CompactCellTree :=
  .absurd 158

private theorem treePart3_check_chunked :
    treePart3.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      1, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, -1, -1, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart3_check :
    treePart3.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      1, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, -1, -1, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart3_check_chunked

/-- Subtree splitting on `length[2] - length[3]` in the row-14 length cone, with leaves
selecting cells 14, 15, 16, 17, 18, 19 and Farkas receipts excluding inconsistent sign branches. -/
def treePart4 : CompactCellTree :=
  .split 8
    (.split 15
        (.split 9
            (.split 21
                (.cell 14 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
                  133, 124, 129, 126, 127, 134, 159])
                (.split 22
                    (.cell 15 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                      148, 151, 150, 160, 161, 153, 162, 155])
                    (.absurd 163)))
            (.split 20
                (.split 21
                    (.cell 16 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                      148, 151, 150, 155, 160, 153, 164, 165])
                    (.split 22
                        (.cell 17 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178,
                          179, 180, 181, 182, 183, 184, 185, 186])
                        (.absurd 187)))
                (.absurd 188)))
        (.absurd 189))
    (.split 15
        (.split 9
            (.split 23
                (.cell 18 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
                  133, 124, 129, 126, 127, 190, 159])
                (.split 24
                    (.cell 15 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                      148, 151, 150, 160, 161, 155, 162, 153])
                    (.absurd 163)))
            (.split 20
                (.split 23
                    (.cell 19 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                      148, 151, 150, 155, 160, 153, 154, 165])
                    (.split 24
                        (.cell 17 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178,
                          179, 180, 181, 182, 183, 186, 185, 184])
                        (.absurd 187)))
                (.absurd 188)))
        (.absurd 189))

private theorem treePart4_check_chunked :
    treePart4.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      1, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart4_check :
    treePart4.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      1, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart4_check_chunked

/-- Subtree splitting on `length[1] - length[7]` in the row-14 length cone, with leaves
selecting cells 20, 21, 22, 23, 24, 25, 26, 27 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart5 : CompactCellTree :=
  .split 26
    (.split 6
        (.split 9
            (.cell 20 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 19, 13, 14, 15, 16, 17, 191, 12])
            (.split 20
                (.cell 21 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 39, 33, 34, 35, 36, 37,
                  192, 32])
                (.absurd 40)))
        (.split 15
            (.split 9
                (.cell 22 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 39, 33, 37, 35, 36, 41,
                  192, 32])
                (.split 20
                    (.cell 23 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 61, 55, 56, 57, 58,
                      59, 193, 54])
                    (.absurd 62)))
            (.absurd 63)))
    (.split 27
        (.split 11
            (.split 6
                (.split 9
                    (.cell 24 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 57, 61, 64, 59, 58,
                      65, 56, 54])
                    (.split 20
                        (.cell 25 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 84, 194, 195,
                          80, 82, 83, 81, 78])
                        (.absurd 85)))
                (.split 15
                    (.split 9
                        (.cell 26 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 84, 194, 83, 80,
                          82, 196, 81, 78])
                        (.split 20
                            (.cell 27 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 197, 198,
                              199, 104, 106, 108, 103, 100])
                            (.absurd 200)))
                    (.absurd 201)))
            (.absurd 202))
        (.absurd 203))

private theorem treePart5_check_chunked :
    treePart5.checkLookup splitForms farkasReceiptLookup cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation
      (aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart5_check :
    treePart5.check splitForms farkasReceipts cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation
      (aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart5_check_chunked

/-- Subtree splitting on `- length[4] + length[5]` in the row-14 length cone, with leaves
selecting cells 2, 3, 28, 29 and Farkas receipts excluding inconsistent sign branches. -/
def treePart6 : CompactCellTree :=
  .split 16
    (.split 9
        (.cell 28 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 14, 16, 17, 18, 19])
        (.split 20
            (.cell 29 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 35, 34, 36, 37, 38,
              39])
            (.absurd 40)))
    (.split 19
        (.split 9
            (.cell 2 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 35, 37, 36, 41, 38,
              39])
            (.split 20
                (.cell 3 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 57, 56, 58, 59,
                  60, 61])
                (.absurd 62)))
        (.absurd 63))

private theorem treePart6_check_chunked :
    treePart6.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++
      [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0]]) = true := by
  decide +kernel

theorem treePart6_check :
    treePart6.check splitForms farkasReceipts cells
      (((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++
      [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart6_check_chunked

/-- Subtree splitting on `- length[4] + length[5]` in the row-14 length cone, with leaves
selecting cells 6, 7, 30, 31 and Farkas receipts excluding inconsistent sign branches. -/
def treePart7 : CompactCellTree :=
  .split 16
    (.split 9
        (.cell 30 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 37, 34, 36, 41, 35])
        (.split 20
            (.cell 31 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 64, 58, 59, 57])
            (.absurd 62)))
    (.split 19
        (.split 9
            (.cell 6 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 59, 58, 65, 57])
            (.split 20
                (.cell 7 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 81, 80, 82, 83,
                  84])
                (.absurd 85)))
        (.absurd 86))

private theorem treePart7_check_chunked :
    treePart7.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++
      [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart7_check :
    treePart7.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++
      [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart7_check_chunked

/-- Contradiction leaf using Farkas receipt 204 to exclude the accumulated affine constraints in
this row-14 branch. -/
def treePart8 : CompactCellTree :=
  .absurd 204

private theorem treePart8_check_chunked :
    treePart8.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])])
      ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart8_check :
    treePart8.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])])
      ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart8_check_chunked

/-- Subtree splitting on `- length[4] + length[5]` in the row-14 length cone, with leaves
selecting cells 14, 15, 16, 17, 32, 33, 34, 35 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart9 : CompactCellTree :=
  .split 16
    (.split 9
        (.split 21
            (.cell 32 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 199, 102, 108,
              105, 106, 107, 104])
            (.split 22
                (.cell 33 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
                  159, 123, 133, 126, 127, 128, 129])
                (.absurd 205)))
        (.split 20
            (.split 21
                (.cell 34 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
                  159, 123, 129, 133, 127, 134, 125])
                (.split 22
                    (.cell 35 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                      148, 165, 149, 160, 151, 153, 162, 155])
                    (.absurd 206)))
            (.absurd 200)))
    (.split 19
        (.split 9
            (.split 21
                (.cell 14 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
                  159, 133, 129, 126, 127, 134, 125])
                (.split 22
                    (.cell 15 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                      148, 165, 151, 160, 161, 153, 162, 155])
                    (.absurd 206)))
            (.split 20
                (.split 21
                    (.cell 16 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                      148, 165, 151, 155, 160, 153, 164, 152])
                    (.split 22
                        (.cell 17 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178,
                          179, 207, 180, 182, 183, 184, 185, 186])
                        (.absurd 208)))
                (.absurd 188)))
        (.absurd 209))

private theorem treePart9_check_chunked :
    treePart9.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])])
      ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart9_check :
    treePart9.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])])
      ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart9_check_chunked

/-- Subtree splitting on `- length[4] + length[5]` in the row-14 length cone, with leaves
selecting cells 15, 17, 18, 19, 33, 35, 36, 37 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart10 : CompactCellTree :=
  .split 16
    (.split 9
        (.split 23
            (.cell 36 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 199, 102, 108,
              105, 106, 131, 104])
            (.split 24
                (.cell 33 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
                  159, 123, 133, 126, 129, 128, 127])
                (.absurd 205)))
        (.split 20
            (.split 23
                (.cell 37 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
                  159, 123, 129, 133, 127, 190, 125])
                (.split 24
                    (.cell 35 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                      148, 165, 149, 160, 151, 155, 162, 153])
                    (.absurd 206)))
            (.absurd 200)))
    (.split 19
        (.split 9
            (.split 23
                (.cell 18 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
                  159, 133, 129, 126, 127, 190, 125])
                (.split 24
                    (.cell 15 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                      148, 165, 151, 160, 161, 155, 162, 153])
                    (.absurd 206)))
            (.split 20
                (.split 23
                    (.cell 19 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                      148, 165, 151, 155, 160, 153, 154, 152])
                    (.split 24
                        (.cell 17 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178,
                          179, 207, 180, 182, 183, 186, 185, 184])
                        (.absurd 208)))
                (.absurd 188)))
        (.absurd 209))

private theorem treePart10_check_chunked :
    treePart10.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])])
      ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart10_check :
    treePart10.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])])
      ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart10_check_chunked

/-- Subtree splitting on `length[1] - length[7]` in the row-14 length cone, with leaves
selecting cells 22, 23, 26, 27, 38, 39, 40, 41 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart11 : CompactCellTree :=
  .split 26
    (.split 16
        (.split 9
            (.cell 38 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 19, 13, 15, 14, 16, 17, 191, 12])
            (.split 20
                (.cell 39 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 39, 33, 35, 34, 36, 37,
                  192, 32])
                (.absurd 40)))
        (.split 19
            (.split 9
                (.cell 22 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 39, 33, 35, 37, 36, 41,
                  192, 32])
                (.split 20
                    (.cell 23 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 61, 55, 57, 56, 58,
                      59, 193, 54])
                    (.absurd 62)))
            (.absurd 63)))
    (.split 27
        (.split 11
            (.split 16
                (.split 9
                    (.cell 40 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 57, 61, 59, 64, 58,
                      65, 56, 54])
                    (.split 20
                        (.cell 41 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 84, 194, 80,
                          195, 82, 83, 81, 78])
                        (.absurd 85)))
                (.split 19
                    (.split 9
                        (.cell 26 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 84, 194, 80, 83,
                          82, 196, 81, 78])
                        (.split 20
                            (.cell 27 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 197, 198,
                              104, 199, 106, 108, 103, 100])
                            (.absurd 200)))
                    (.absurd 201)))
            (.absurd 202))
        (.absurd 203))

private theorem treePart11_check_chunked :
    treePart11.checkLookup splitForms farkasReceiptLookup cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart11_check :
    treePart11.check splitForms farkasReceipts cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart11_check_chunked

/-- Subtree splitting on `length[4] - length[10]` in the row-14 length cone, with leaves
selecting cells 42, 43, 44 and Farkas receipts excluding inconsistent sign branches. -/
def treePart12 : CompactCellTree :=
  .split 2
    (.split 6
        (.cell 42 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 14, 17, 19])
        (.split 15
            (.cell 43 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 36, 37, 34, 41, 39])
            (.absurd 210)))
    (.split 16
        (.cell 44 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 15, 14, 17, 19])
        (.split 19
            (.cell 43 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 37, 36, 34, 41, 39])
            (.absurd 210)))

private theorem treePart12_check_chunked :
    treePart12.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1]]) ++
      [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      0]]) = true := by
  decide +kernel

theorem treePart12_check :
    treePart12.check splitForms farkasReceipts cells
      (((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1]]) ++
      [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart12_check_chunked

/-- Subtree splitting on `length[4] - length[10]` in the row-14 length cone, with leaves
selecting cells 45, 46, 47 and Farkas receipts excluding inconsistent sign branches. -/
def treePart13 : CompactCellTree :=
  .split 2
    (.split 6
        (.cell 45 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 37, 36, 34, 41, 35])
        (.split 15
            (.cell 46 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 58, 59, 64, 65, 57])
            (.absurd 211)))
    (.split 16
        (.cell 47 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 36, 37, 34, 41, 35])
        (.split 19
            (.cell 46 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 59, 58, 64, 65, 57])
            (.absurd 211)))

private theorem treePart13_check_chunked :
    treePart13.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1]])
      ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart13_check :
    treePart13.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1]])
      ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart13_check_chunked

/-- Contradiction leaf using Farkas receipt 204 to exclude the accumulated affine constraints in
this row-14 branch. -/
def treePart14 : CompactCellTree :=
  .absurd 204

private theorem treePart14_check_chunked :
    treePart14.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1]])
      ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0,
      0, 0])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart14_check :
    treePart14.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1]])
      ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0,
      0, 0])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart14_check_chunked

/-- Subtree splitting on `length[2] - length[3]` in the row-14 length cone, with leaves
selecting cells 48, 49, 50, 51, 52, 53 and Farkas receipts excluding inconsistent sign branches. -/
def treePart15 : CompactCellTree :=
  .split 8
    (.split 2
        (.split 6
            (.cell 48 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 108, 106, 102,
              105, 104, 212, 199])
            (.split 15
                (.cell 49 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
                  127, 129, 123, 126, 125, 213, 159])
                (.absurd 130)))
        (.split 16
            (.cell 50 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 106, 108, 102,
              105, 104, 212, 199])
            (.split 19
                (.cell 49 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
                  129, 127, 123, 126, 125, 213, 159])
                (.absurd 130))))
    (.split 28
        (.split 2
            (.split 6
                (.cell 51 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
                  129, 127, 123, 126, 133, 214, 159])
                (.split 15
                    (.cell 52 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                      148, 153, 155, 149, 161, 151, 215, 165])
                    (.absurd 156)))
            (.split 16
                (.cell 53 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
                  127, 129, 123, 126, 133, 214, 159])
                (.split 19
                    (.cell 52 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                      148, 155, 153, 149, 161, 151, 215, 165])
                    (.absurd 156))))
        (.absurd 216))

private theorem treePart15_check_chunked :
    treePart15.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1]])
      ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++ [aff
      [0, 1, -1, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart15_check :
    treePart15.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1]])
      ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++ [aff
      [0, 1, -1, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart15_check_chunked

/-- Subtree splitting on `- length[0] + length[1] + length[2] + length[6]` in the row-14 length
cone, with leaves selecting cells 51, 52, 53, 54, 55, 56 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart16 : CompactCellTree :=
  .split 29
    (.split 2
        (.split 6
            (.cell 54 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 108, 106, 102,
              105, 199, 197, 104])
            (.split 15
                (.cell 55 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
                  127, 129, 123, 126, 159, 128, 125])
                (.absurd 130)))
        (.split 16
            (.cell 56 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 106, 108, 102,
              105, 199, 197, 104])
            (.split 19
                (.cell 55 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
                  129, 127, 123, 126, 159, 128, 125])
                (.absurd 130))))
    (.split 25
        (.split 2
            (.split 6
                (.cell 51 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
                  129, 127, 123, 126, 159, 214, 133])
                (.split 15
                    (.cell 52 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                      148, 153, 155, 149, 161, 165, 215, 151])
                    (.absurd 156)))
            (.split 16
                (.cell 53 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
                  127, 129, 123, 126, 159, 214, 133])
                (.split 19
                    (.cell 52 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                      148, 155, 153, 149, 161, 165, 215, 151])
                    (.absurd 156))))
        (.absurd 216))

private theorem treePart16_check_chunked :
    treePart16.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1]])
      ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart16_check :
    treePart16.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1]])
      ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart16_check_chunked

/-- Subtree splitting on `length[1] - length[6]` in the row-14 length cone, with leaves
selecting cells 24, 26, 40, 57, 58, 59 and Farkas receipts excluding inconsistent sign branches. -/
def treePart17 : CompactCellTree :=
  .split 30
    (.split 2
        (.split 6
            (.cell 57 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 19, 13, 15, 16, 14, 17, 191, 12])
            (.split 15
                (.cell 58 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 39, 33, 36, 37, 34, 41,
                  192, 32])
                (.absurd 210)))
        (.split 16
            (.cell 59 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 19, 13, 16, 15, 14, 17, 191, 12])
            (.split 19
                (.cell 58 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 39, 33, 37, 36, 34, 41,
                  192, 32])
                (.absurd 210))))
    (.split 31
        (.split 4
            (.split 2
                (.split 6
                    (.cell 24 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 61, 57, 59, 58, 64,
                      65, 54, 56])
                    (.split 15
                        (.cell 26 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 194, 84, 82, 83,
                          195, 196, 78, 81])
                        (.absurd 216)))
                (.split 16
                    (.cell 40 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 61, 57, 58, 59, 64,
                      65, 54, 56])
                    (.split 19
                        (.cell 26 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 194, 84, 83, 82,
                          195, 196, 78, 81])
                        (.absurd 216))))
            (.absurd 202))
        (.absurd 203))

private theorem treePart17_check_chunked :
    treePart17.checkLookup splitForms farkasReceiptLookup cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart17_check :
    treePart17.check splitForms farkasReceipts cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart17_check_chunked

/-- Subtree splitting on `- length[8] + length[9]` in the row-14 length cone, with leaves
selecting cells 60, 61, 62, 63, 64, 65 and Farkas receipts excluding inconsistent sign branches. -/
def treePart18 : CompactCellTree :=
  .split 20
    (.split 13
        (.cell 60 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 57, 217, 56, 61, 59, 64, 58,
          218, 54])
        (.split 11
            (.cell 61 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 84, 219, 81, 194, 80, 195,
              82, 220])
            (.split 12
                (.cell 62 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 197, 221, 103, 198, 104,
                  102, 106])
                (.split 14
                    (.split 8
                        (.cell 63 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 162,
                          222, 150, 223, 152, 149, 155, 224, 153])
                        (.split 28
                            (.cell 64 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177,
                              185, 225, 181, 226, 227, 228, 184, 229, 186])
                            (.absurd 230)))
                    (.split 29
                        (.cell 65 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 162,
                          222, 150, 223, 152, 149, 153, 160, 155])
                        (.split 25
                            (.cell 64 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177,
                              185, 225, 181, 226, 227, 228, 186, 229, 184])
                            (.absurd 230)))))))
    (.absurd 231)

private theorem treePart18_check_chunked :
    treePart18.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++ [aff
      [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) = true := by
  decide +kernel

theorem treePart18_check :
    treePart18.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++ [aff
      [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart18_check_chunked

/-- Subtree splitting on `- length[4] + length[5]` in the row-14 length cone, with leaves
selecting cell 66 and Farkas receipts excluding inconsistent sign branches. -/
def treePart19 : CompactCellTree :=
  .split 16
    (.split 20
        (.cell 66 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 84, 219, 83, 81, 82, 195, 80,
          232, 78])
        (.absurd 233))
    (.absurd 234)

private theorem treePart19_check_chunked :
    treePart19.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, -1, -1, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart19_check :
    treePart19.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, -1, -1, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart19_check_chunked

/-- Subtree splitting on `- length[4] + length[5]` in the row-14 length cone, with leaves
selecting cell 67 and Farkas receipts excluding inconsistent sign branches. -/
def treePart20 : CompactCellTree :=
  .split 16
    (.split 20
        (.cell 67 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 197, 221, 108, 103, 106, 102,
          199, 235])
        (.absurd 236))
    (.absurd 237)

private theorem treePart20_check_chunked :
    treePart20.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart20_check :
    treePart20.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart20_check_chunked

/-- Subtree splitting on `- length[4] + length[5]` in the row-14 length cone, with leaves
selecting cell 68 and Farkas receipts excluding inconsistent sign branches. -/
def treePart21 : CompactCellTree :=
  .split 16
    (.split 20
        (.cell 68 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 128, 238, 129, 124,
          127, 123, 133])
        (.absurd 239))
    (.absurd 240)

private theorem treePart21_check_chunked :
    treePart21.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart21_check :
    treePart21.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart21_check_chunked

/-- Subtree splitting on `length[0] - length[1] - length[3] - length[6]` in the row-14 length
cone, with leaves selecting cells 69, 70, 71 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart22 : CompactCellTree :=
  .split 14
    (.split 8
        (.split 16
            (.split 20
                (.cell 69 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 185, 225,
                  186, 181, 184, 228, 183, 241, 182])
                (.absurd 242))
            (.absurd 243))
        (.split 28
            (.split 16
                (.split 20
                    (.cell 70 [244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256,
                      257, 258, 259, 260, 261, 262, 263, 264])
                    (.absurd 265))
                (.absurd 266))
            (.absurd 156)))
    (.split 29
        (.split 16
            (.split 20
                (.cell 71 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 185, 225,
                  186, 181, 184, 228, 182, 180, 183])
                (.absurd 242))
            (.absurd 243))
        (.split 25
            (.split 16
                (.split 20
                    (.cell 70 [244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256,
                      257, 258, 259, 260, 261, 264, 263, 262])
                    (.absurd 265))
                (.absurd 266))
            (.absurd 156)))

private theorem treePart22_check_chunked :
    treePart22.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart22_check :
    treePart22.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart22_check_chunked

/-- Subtree splitting on `length[1] - length[6]` in the row-14 length cone, with leaves
selecting cells 25, 41, 72, 73 and Farkas receipts excluding inconsistent sign branches. -/
def treePart23 : CompactCellTree :=
  .split 30
    (.split 2
        (.split 20
            (.cell 72 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 56, 267, 59, 61, 58, 64, 57,
              60])
            (.absurd 268))
        (.split 16
            (.split 20
                (.cell 73 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 81, 269, 83, 80, 82,
                  195, 84, 220])
                (.absurd 233))
            (.absurd 270)))
    (.split 2
        (.split 20
            (.cell 25 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 56, 271, 59, 61, 58, 64, 57,
              60])
            (.absurd 268))
        (.split 16
            (.split 20
                (.cell 41 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 81, 272, 83, 80, 82,
                  195, 84, 220])
                (.absurd 233))
            (.absurd 270)))

private theorem treePart23_check_chunked :
    treePart23.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0,
      0, 0, 0])]) = true := by
  decide +kernel

theorem treePart23_check :
    treePart23.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0,
      0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart23_check_chunked

/-- Subtree splitting on `- length[8] + length[9]` in the row-14 length cone, with leaves
selecting cells 74, 75, 76, 77, 78, 79 and Farkas receipts excluding inconsistent sign branches. -/
def treePart24 : CompactCellTree :=
  .split 20
    (.split 13
        (.cell 74 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 57, 217, 56, 61, 59, 64, 58,
          218, 54])
        (.split 11
            (.cell 75 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 84, 219, 81, 194, 80, 195,
              82, 220])
            (.split 12
                (.cell 76 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 197, 221, 103, 198, 104,
                  102, 106])
                (.split 14
                    (.split 8
                        (.cell 77 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 162,
                          222, 150, 223, 152, 149, 155, 224, 153])
                        (.split 28
                            (.cell 78 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177,
                              185, 225, 181, 226, 227, 228, 184, 229, 186])
                            (.absurd 230)))
                    (.split 29
                        (.cell 79 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 162,
                          222, 150, 223, 152, 149, 153, 160, 155])
                        (.split 25
                            (.cell 78 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177,
                              185, 225, 181, 226, 227, 228, 186, 229, 184])
                            (.absurd 230)))))))
    (.absurd 231)

private theorem treePart24_check_chunked :
    treePart24.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart24_check :
    treePart24.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart24_check_chunked

/-- Subtree splitting on `- length[4] + length[10]` in the row-14 length cone, with leaves
selecting cell 66 and Farkas receipts excluding inconsistent sign branches. -/
def treePart25 : CompactCellTree :=
  .split 32
    (.split 20
        (.cell 66 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 84, 219, 81, 83, 82, 195, 80,
          232, 78])
        (.absurd 233))
    (.absurd 234)

private theorem treePart25_check_chunked :
    treePart25.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0,
      0])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart25_check :
    treePart25.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0,
      0])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart25_check_chunked

/-- Subtree splitting on `- length[4] + length[10]` in the row-14 length cone, with leaves
selecting cell 67 and Farkas receipts excluding inconsistent sign branches. -/
def treePart26 : CompactCellTree :=
  .split 32
    (.split 20
        (.cell 67 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 197, 221, 103, 108, 106, 102,
          199, 235])
        (.absurd 236))
    (.absurd 237)

private theorem treePart26_check_chunked :
    treePart26.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++ [aff [0,
      -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart26_check :
    treePart26.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++ [aff [0,
      -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart26_check_chunked

/-- Subtree splitting on `- length[4] + length[10]` in the row-14 length cone, with leaves
selecting cell 68 and Farkas receipts excluding inconsistent sign branches. -/
def treePart27 : CompactCellTree :=
  .split 32
    (.split 20
        (.cell 68 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 128, 238, 124, 129,
          127, 123, 133])
        (.absurd 239))
    (.absurd 240)

private theorem treePart27_check_chunked :
    treePart27.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart27_check :
    treePart27.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart27_check_chunked

/-- Subtree splitting on `length[0] - length[1] - length[3] - length[6]` in the row-14 length
cone, with leaves selecting cells 69, 70, 71 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart28 : CompactCellTree :=
  .split 14
    (.split 8
        (.split 32
            (.split 20
                (.cell 69 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 185, 225,
                  181, 186, 184, 228, 183, 241, 182])
                (.absurd 242))
            (.absurd 243))
        (.split 28
            (.split 32
                (.split 20
                    (.cell 70 [244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256,
                      257, 259, 258, 260, 261, 262, 263, 264])
                    (.absurd 265))
                (.absurd 266))
            (.absurd 156)))
    (.split 29
        (.split 32
            (.split 20
                (.cell 71 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 185, 225,
                  181, 186, 184, 228, 182, 180, 183])
                (.absurd 242))
            (.absurd 243))
        (.split 25
            (.split 32
                (.split 20
                    (.cell 70 [244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256,
                      257, 259, 258, 260, 261, 264, 263, 262])
                    (.absurd 265))
                (.absurd 266))
            (.absurd 156)))

private theorem treePart28_check_chunked :
    treePart28.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart28_check :
    treePart28.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart28_check_chunked

/-- Subtree splitting on `length[1] - length[6]` in the row-14 length cone, with leaves
selecting cells 27, 41, 73, 80 and Farkas receipts excluding inconsistent sign branches. -/
def treePart29 : CompactCellTree :=
  .split 30
    (.split 15
        (.split 20
            (.cell 80 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 56, 267, 59, 61, 58, 64, 57,
              60])
            (.absurd 268))
        (.split 32
            (.split 20
                (.cell 73 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 81, 269, 80, 83, 82,
                  195, 84, 220])
                (.absurd 233))
            (.absurd 270)))
    (.split 15
        (.split 20
            (.cell 27 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 56, 271, 59, 61, 58, 64, 57,
              60])
            (.absurd 268))
        (.split 32
            (.split 20
                (.cell 41 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 81, 272, 80, 83, 82,
                  195, 84, 220])
                (.absurd 233))
            (.absurd 270)))

private theorem treePart29_check_chunked :
    treePart29.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart29_check :
    treePart29.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart29_check_chunked

/-- Subtree splitting on `- length[8] + length[9]` in the row-14 length cone, with leaves
selecting cells 62, 63, 64, 65, 81 and Farkas receipts excluding inconsistent sign branches. -/
def treePart30 : CompactCellTree :=
  .split 20
    (.split 11
        (.cell 81 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 57, 55, 61, 56, 59, 64, 58])
        (.split 12
            (.cell 62 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 84, 79, 194, 81, 80, 195,
              82])
            (.split 14
                (.split 8
                    (.cell 63 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 128,
                      122, 273, 124, 125, 123, 129, 213, 127])
                    (.split 28
                        (.cell 64 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 162,
                          148, 223, 150, 152, 149, 153, 215, 155])
                        (.absurd 156)))
                (.split 29
                    (.cell 65 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 128,
                      122, 273, 124, 125, 123, 127, 133, 129])
                    (.split 25
                        (.cell 64 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 162,
                          148, 223, 150, 152, 149, 155, 215, 153])
                        (.absurd 156))))))
    (.absurd 231)

private theorem treePart30_check_chunked :
    treePart30.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) = true := by
  decide +kernel

theorem treePart30_check :
    treePart30.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart30_check_chunked

/-- Subtree splitting on `length[4] - length[5]` in the row-14 length cone, with leaves
selecting cell 82 and Farkas receipts excluding inconsistent sign branches. -/
def treePart31 : CompactCellTree :=
  .split 15
    (.split 20
        (.cell 82 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 84, 79, 83, 81, 82, 195, 80])
        (.absurd 233))
    (.absurd 234)

private theorem treePart31_check_chunked :
    treePart31.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++
      [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart31_check :
    treePart31.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++
      [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart31_check_chunked

/-- Subtree splitting on `length[4] - length[5]` in the row-14 length cone, with leaves
selecting cell 76 and Farkas receipts excluding inconsistent sign branches. -/
def treePart32 : CompactCellTree :=
  .split 15
    (.split 20
        (.cell 76 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 197, 101, 108, 103, 106, 102,
          199])
        (.absurd 236))
    (.absurd 237)

private theorem treePart32_check_chunked :
    treePart32.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart32_check :
    treePart32.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart32_check_chunked

/-- Subtree splitting on `length[0] - length[1] - length[3] - length[6]` in the row-14 length
cone, with leaves selecting cells 77, 78, 79 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart33 : CompactCellTree :=
  .split 14
    (.split 8
        (.split 15
            (.split 20
                (.cell 77 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 162, 148,
                  155, 150, 153, 149, 151, 224, 160])
                (.absurd 274))
            (.absurd 275))
        (.split 28
            (.split 15
                (.split 20
                    (.cell 78 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 185,
                      179, 186, 181, 184, 228, 182, 229, 183])
                    (.absurd 242))
                (.absurd 243))
            (.absurd 130)))
    (.split 29
        (.split 15
            (.split 20
                (.cell 79 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 162, 148,
                  155, 150, 153, 149, 160, 165, 151])
                (.absurd 274))
            (.absurd 275))
        (.split 25
            (.split 15
                (.split 20
                    (.cell 78 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 185,
                      179, 186, 181, 184, 228, 183, 229, 182])
                    (.absurd 242))
                (.absurd 243))
            (.absurd 130)))

private theorem treePart33_check_chunked :
    treePart33.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart33_check :
    treePart33.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart33_check_chunked

/-- Subtree splitting on `length[1] - length[6]` in the row-14 length cone, with leaves
selecting cells 25, 27, 83, 84 and Farkas receipts excluding inconsistent sign branches. -/
def treePart34 : CompactCellTree :=
  .split 30
    (.split 6
        (.split 20
            (.cell 83 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 56, 55, 61, 59, 58, 64, 276,
              57])
            (.absurd 268))
        (.split 15
            (.split 20
                (.cell 84 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 81, 79, 83, 80, 82, 195,
                  277, 84])
                (.absurd 233))
            (.absurd 270)))
    (.split 31
        (.split 4
            (.split 6
                (.split 20
                    (.cell 25 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 103, 104, 198, 108,
                      106, 102, 197, 199])
                    (.absurd 236))
                (.split 15
                    (.split 20
                        (.cell 27 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 124,
                          125, 129, 133, 127, 123, 128, 159])
                        (.absurd 239))
                    (.absurd 278)))
            (.absurd 279))
        (.absurd 280))

private theorem treePart34_check_chunked :
    treePart34.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart34_check :
    treePart34.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart34_check_chunked

/-- Subtree splitting on `- length[8] + length[9]` in the row-14 length cone, with leaves
selecting cells 68, 69, 70, 71, 85 and Farkas receipts excluding inconsistent sign branches. -/
def treePart35 : CompactCellTree :=
  .split 20
    (.split 11
        (.cell 85 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 57, 55, 56, 61, 59, 64, 58])
        (.split 12
            (.cell 68 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 84, 79, 81, 194, 80, 195,
              82])
            (.split 14
                (.split 8
                    (.cell 69 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 128,
                      122, 124, 273, 125, 123, 129, 213, 127])
                    (.split 28
                        (.cell 70 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 162,
                          148, 150, 223, 152, 149, 153, 215, 155])
                        (.absurd 156)))
                (.split 29
                    (.cell 71 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 128,
                      122, 124, 273, 125, 123, 127, 133, 129])
                    (.split 25
                        (.cell 70 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 162,
                          148, 150, 223, 152, 149, 155, 215, 153])
                        (.absurd 156))))))
    (.absurd 231)

private theorem treePart35_check_chunked :
    treePart35.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0]]) = true
      := by
  decide +kernel

theorem treePart35_check :
    treePart35.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0]]) = true
      := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart35_check_chunked

/-- Subtree splitting on `- length[5] + length[10]` in the row-14 length cone, with leaves
selecting cell 82 and Farkas receipts excluding inconsistent sign branches. -/
def treePart36 : CompactCellTree :=
  .split 19
    (.split 20
        (.cell 82 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 84, 79, 81, 83, 82, 195, 80])
        (.absurd 233))
    (.absurd 234)

private theorem treePart36_check_chunked :
    treePart36.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 1, 0, 0,
      0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart36_check :
    treePart36.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 1, 0, 0,
      0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart36_check_chunked

/-- Subtree splitting on `- length[5] + length[10]` in the row-14 length cone, with leaves
selecting cell 76 and Farkas receipts excluding inconsistent sign branches. -/
def treePart37 : CompactCellTree :=
  .split 19
    (.split 20
        (.cell 76 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 197, 101, 103, 108, 106, 102,
          199])
        (.absurd 236))
    (.absurd 237)

private theorem treePart37_check_chunked :
    treePart37.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 1, 0, 0,
      0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++
      [aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart37_check :
    treePart37.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 1, 0, 0,
      0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++
      [aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart37_check_chunked

/-- Subtree splitting on `length[0] - length[1] - length[3] - length[6]` in the row-14 length
cone, with leaves selecting cells 77, 78, 79 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart38 : CompactCellTree :=
  .split 14
    (.split 8
        (.split 19
            (.split 20
                (.cell 77 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 162, 148,
                  150, 155, 153, 149, 151, 224, 160])
                (.absurd 274))
            (.absurd 275))
        (.split 28
            (.split 19
                (.split 20
                    (.cell 78 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 185,
                      179, 181, 186, 184, 228, 182, 229, 183])
                    (.absurd 242))
                (.absurd 243))
            (.absurd 130)))
    (.split 29
        (.split 19
            (.split 20
                (.cell 79 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 162, 148,
                  150, 155, 153, 149, 160, 165, 151])
                (.absurd 274))
            (.absurd 275))
        (.split 25
            (.split 19
                (.split 20
                    (.cell 78 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 185,
                      179, 181, 186, 184, 228, 183, 229, 182])
                    (.absurd 242))
                (.absurd 243))
            (.absurd 130)))

private theorem treePart38_check_chunked :
    treePart38.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 1, 0, 0,
      0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart38_check :
    treePart38.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 1, 0, 0,
      0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart38_check_chunked

/-- Subtree splitting on `length[1] - length[6]` in the row-14 length cone, with leaves
selecting cells 27, 41, 84, 86 and Farkas receipts excluding inconsistent sign branches. -/
def treePart39 : CompactCellTree :=
  .split 30
    (.split 16
        (.split 20
            (.cell 86 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 56, 55, 59, 61, 58, 64, 276,
              57])
            (.absurd 268))
        (.split 19
            (.split 20
                (.cell 84 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 81, 79, 80, 83, 82, 195,
                  277, 84])
                (.absurd 233))
            (.absurd 270)))
    (.split 31
        (.split 4
            (.split 16
                (.split 20
                    (.cell 41 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 103, 104, 108, 198,
                      106, 102, 197, 199])
                    (.absurd 236))
                (.split 19
                    (.split 20
                        (.cell 27 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 124,
                          125, 133, 129, 127, 123, 128, 159])
                        (.absurd 239))
                    (.absurd 278)))
            (.absurd 279))
        (.absurd 280))

private theorem treePart39_check_chunked :
    treePart39.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart39_check :
    treePart39.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart39_check_chunked

/-- Subtree splitting on `length[0] - length[7]` in the row-14 length cone, with leaves
selecting cells 87, 88, 89, 90, 91, 92, 93 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart40 : CompactCellTree :=
  .split 3
    (.split 4
        (.cell 87 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 15, 13, 12, 14, 19, 17, 281, 16])
        (.split 5
            (.cell 88 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 35, 33, 32, 34, 39, 41, 36])
            (.split 7
                (.cell 87 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 57, 55, 54, 64, 61, 65,
                  282, 87])
                (.split 8
                    (.split 21
                        (.cell 89 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 197, 101, 100,
                          102, 198, 105, 106, 107, 108])
                        (.split 22
                            (.cell 90 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120,
                              128, 122, 121, 123, 273, 126, 127, 125, 129])
                            (.absurd 130)))
                    (.split 23
                        (.cell 91 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 197, 101, 100,
                          102, 198, 105, 106, 131, 108])
                        (.split 24
                            (.cell 90 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120,
                              128, 122, 121, 123, 273, 126, 129, 125, 127])
                            (.absurd 130)))))))
    (.split 26
        (.cell 92 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 16, 13, 12, 14, 19, 17, 283, 15])
        (.split 27
            (.split 11
                (.cell 93 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 59, 56, 54, 64, 61, 65,
                  58, 57])
                (.absurd 279))
            (.absurd 280)))

private theorem treePart40_check_chunked :
    treePart40.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]])
      ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0, 0]]) = true := by
  decide +kernel

theorem treePart40_check :
    treePart40.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]])
      ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart40_check_chunked

/-- Subtree splitting on `length[0] - length[7]` in the row-14 length cone, with leaves
selecting cells 1, 5, 11, 12, 13, 21, 25 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart41 : CompactCellTree :=
  .split 3
    (.split 18
        (.split 4
            (.cell 1 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 35, 33, 32, 34, 39, 37, 284,
              36])
            (.split 5
                (.cell 5 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 57, 55, 54, 64, 61, 56,
                  58])
                (.split 7
                    (.cell 1 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 84, 79, 78, 195, 194,
                      81, 285, 286])
                    (.split 8
                        (.split 21
                            (.cell 11 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120,
                              128, 122, 121, 123, 273, 124, 127, 134, 129])
                            (.split 22
                                (.cell 13 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145,
                                  146, 162, 148, 147, 149, 223, 150, 153, 165, 155])
                                (.absurd 156)))
                        (.split 23
                            (.cell 12 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120,
                              128, 122, 121, 123, 273, 124, 127, 190, 129])
                            (.split 24
                                (.cell 13 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145,
                                  146, 162, 148, 147, 149, 223, 150, 155, 165, 153])
                                (.absurd 156)))))))
        (.absurd 287))
    (.split 26
        (.split 18
            (.cell 21 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 37, 33, 32, 34, 39, 36, 288,
              35])
            (.absurd 289))
        (.split 27
            (.split 11
                (.split 18
                    (.cell 25 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 80, 81, 78, 195,
                      194, 82, 83, 84])
                    (.absurd 290))
                (.absurd 279))
            (.absurd 280)))

private theorem treePart41_check_chunked :
    treePart41.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]])
      ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, -1, 0, 0])]) = true := by
  decide +kernel

theorem treePart41_check :
    treePart41.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]])
      ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, -1, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart41_check_chunked

/-- Subtree splitting on `- length[4] + length[5]` in the row-14 length cone, with leaves
selecting cells 29, 94 and Farkas receipts excluding inconsistent sign branches. -/
def treePart42 : CompactCellTree :=
  .split 16
    (.split 17
        (.cell 94 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 39, 33, 37, 32, 36, 41, 132, 35])
        (.split 18
            (.cell 29 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 61, 55, 56, 54, 59, 58, 291,
              57])
            (.absurd 62)))
    (.absurd 292)

private theorem treePart42_check_chunked :
    treePart42.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart42_check :
    treePart42.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart42_check_chunked

/-- Subtree splitting on `- length[0] + length[1] + length[7]` in the row-14 length cone, with
leaves selecting cells 94, 95, 96, 97, 98 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart43 : CompactCellTree :=
  .split 5
    (.cell 95 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 61, 55, 56, 54, 59, 65, 58])
    (.split 7
        (.cell 94 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 194, 79, 81, 78, 80, 196, 293,
          286])
        (.split 8
            (.split 21
                (.cell 96 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 273, 122,
                  124, 121, 125, 126, 127, 134, 129])
                (.split 22
                    (.cell 97 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 223,
                      148, 150, 147, 152, 161, 153, 165, 155])
                    (.absurd 156)))
            (.split 23
                (.cell 98 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 273, 122,
                  124, 121, 125, 126, 127, 190, 129])
                (.split 24
                    (.cell 97 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 223,
                      148, 150, 147, 152, 161, 155, 165, 153])
                    (.absurd 156)))))

private theorem treePart43_check_chunked :
    treePart43.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0])]) ++ [aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, -1, 0, 0]]) = true := by
  decide +kernel

theorem treePart43_check :
    treePart43.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0])]) ++ [aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, -1, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart43_check_chunked

/-- Subtree splitting on `- length[8] + length[11]` in the row-14 length cone, with leaves
selecting cells 29, 31, 34, 35, 37 and Farkas receipts excluding inconsistent sign branches. -/
def treePart44 : CompactCellTree :=
  .split 18
    (.split 5
        (.cell 31 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 194, 79, 81, 78, 80, 83, 82])
        (.split 7
            (.cell 29 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 198, 101, 103, 100, 104,
              199, 294, 295])
            (.split 8
                (.split 21
                    (.cell 34 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 223,
                      148, 150, 147, 152, 165, 153, 164, 155])
                    (.split 22
                        (.cell 35 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 226,
                          179, 181, 178, 227, 207, 184, 180, 186])
                        (.absurd 230)))
                (.split 23
                    (.cell 37 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 223,
                      148, 150, 147, 152, 165, 153, 154, 155])
                    (.split 24
                        (.cell 35 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 226,
                          179, 181, 178, 227, 207, 186, 180, 184])
                        (.absurd 230))))))
    (.absurd 62)

private theorem treePart44_check_chunked :
    treePart44.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0])]) ++ [aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) = true := by
  decide +kernel

theorem treePart44_check :
    treePart44.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0])]) ++ [aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart44_check_chunked

/-- Contradiction leaf using Farkas receipt 292 to exclude the accumulated affine constraints in
this row-14 branch. -/
def treePart45 : CompactCellTree :=
  .absurd 292

private theorem treePart45_check_chunked :
    treePart45.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0])]) = true :=
      by
  decide +kernel

theorem treePart45_check :
    treePart45.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0])]) = true :=
      by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart45_check_chunked

/-- Subtree splitting on `- length[0] + length[6]` in the row-14 length cone, with leaves
selecting cells 41, 99, 100, 101 and Farkas receipts excluding inconsistent sign branches. -/
def treePart46 : CompactCellTree :=
  .split 11
    (.split 16
        (.split 17
            (.split 26
                (.cell 99 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 58, 55, 56, 54, 59, 65,
                  57, 61])
                (.split 27
                    (.cell 100 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 82, 83, 81, 78, 80,
                      196, 84, 194])
                    (.absurd 296)))
            (.split 26
                (.split 18
                    (.cell 101 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 83, 79, 81, 78, 80,
                      82, 84, 194])
                    (.absurd 157))
                (.split 27
                    (.split 18
                        (.cell 41 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 108, 199, 103,
                          100, 104, 106, 197, 198])
                        (.absurd 297))
                    (.absurd 296))))
        (.absurd 292))
    (.absurd 203)

private theorem treePart46_check_chunked :
    treePart46.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart46_check :
    treePart46.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart46_check_chunked

/-- Subtree splitting on `- length[0] + length[7]` in the row-14 length cone, with leaves
selecting cells 102, 103, 104, 105, 106 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart47 : CompactCellTree :=
  .split 4
    (.cell 102 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 14, 19, 17, 18, 16])
    (.split 5
        (.cell 103 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 35, 34, 39, 41, 36])
        (.split 7
            (.cell 102 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 57, 64, 61, 65, 60,
              87])
            (.split 8
                (.split 21
                    (.cell 104 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 197, 102,
                      198, 105, 106, 107, 108])
                    (.split 22
                        (.cell 105 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120,
                          121, 122, 128, 123, 273, 126, 127, 125, 129])
                        (.absurd 130)))
                (.split 23
                    (.cell 106 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 197, 102,
                      198, 105, 106, 131, 108])
                    (.split 24
                        (.cell 105 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120,
                          121, 122, 128, 123, 273, 126, 129, 125, 127])
                        (.absurd 130))))))

private theorem treePart47_check_chunked :
    treePart47.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart47_check :
    treePart47.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart47_check_chunked

/-- Subtree splitting on `- length[4] + length[10]` in the row-14 length cone, with leaves
selecting cells 94, 95, 96, 97, 98 and Farkas receipts excluding inconsistent sign branches. -/
def treePart48 : CompactCellTree :=
  .split 32
    (.split 4
        (.cell 94 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 35, 37, 39, 41, 38, 36])
        (.split 5
            (.cell 95 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 57, 56, 61, 65, 58])
            (.split 7
                (.cell 94 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 84, 81, 194,
                  196, 220, 286])
                (.split 8
                    (.split 21
                        (.cell 96 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121,
                          122, 128, 124, 273, 126, 127, 134, 129])
                        (.split 22
                            (.cell 97 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                              147, 148, 162, 150, 223, 161, 153, 165, 155])
                            (.absurd 156)))
                    (.split 23
                        (.cell 98 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121,
                          122, 128, 124, 273, 126, 127, 190, 129])
                        (.split 24
                            (.cell 97 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                              147, 148, 162, 150, 223, 161, 155, 165, 153])
                            (.absurd 156)))))))
    (.absurd 63)

private theorem treePart48_check_chunked :
    treePart48.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0,
      0, 0])]) = true := by
  decide +kernel

theorem treePart48_check :
    treePart48.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0,
      0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart48_check_chunked

/-- Subtree splitting on `length[4] - length[5]` in the row-14 length cone, with leaves
selecting cells 3, 29 and Farkas receipts excluding inconsistent sign branches. -/
def treePart49 : CompactCellTree :=
  .split 15
    (.cell 3 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 36, 34, 39, 35, 38, 37])
    (.split 32
        (.cell 29 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 59, 58, 61, 57, 60, 56])
        (.absurd 201))

private theorem treePart49_check_chunked :
    treePart49.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 1]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart49_check :
    treePart49.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 1]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart49_check_chunked

/-- Subtree splitting on `length[4] - length[5]` in the row-14 length cone, with leaves
selecting cells 7, 31 and Farkas receipts excluding inconsistent sign branches. -/
def treePart50 : CompactCellTree :=
  .split 15
    (.cell 7 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 58, 64, 61, 57, 59])
    (.split 32
        (.cell 31 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 83, 82, 194, 84, 80])
        (.absurd 209))

private theorem treePart50_check_chunked :
    treePart50.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart50_check :
    treePart50.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart50_check_chunked

/-- Subtree splitting on `- length[0] - length[1] + length[7]` in the row-14 length cone, with
leaves selecting cells 16, 17, 19, 34, 35, 37 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart51 : CompactCellTree :=
  .split 7
    (.absurd 298)
    (.split 8
        (.split 15
            (.split 21
                (.cell 16 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
                  129, 123, 273, 128, 127, 134, 133])
                (.split 22
                    (.cell 17 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                      148, 160, 149, 223, 162, 153, 152, 155])
                    (.absurd 299)))
            (.split 32
                (.split 21
                    (.cell 34 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                      148, 160, 155, 223, 162, 153, 164, 151])
                    (.split 22
                        (.cell 35 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178,
                          179, 183, 182, 226, 185, 184, 227, 186])
                        (.absurd 300)))
                (.absurd 301)))
        (.split 15
            (.split 23
                (.cell 19 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
                  129, 123, 273, 128, 127, 190, 133])
                (.split 24
                    (.cell 17 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                      148, 160, 149, 223, 162, 155, 152, 153])
                    (.absurd 299)))
            (.split 32
                (.split 23
                    (.cell 37 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                      148, 160, 155, 223, 162, 153, 154, 151])
                    (.split 24
                        (.cell 35 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178,
                          179, 183, 182, 226, 185, 186, 227, 184])
                        (.absurd 300)))
                (.absurd 301))))

private theorem treePart51_check_chunked :
    treePart51.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart51_check :
    treePart51.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart51_check_chunked

/-- Contradiction leaf using Farkas receipt 302 to exclude the accumulated affine constraints in
this row-14 branch. -/
def treePart52 : CompactCellTree :=
  .absurd 302

private theorem treePart52_check_chunked :
    treePart52.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1])]) = true := by
  decide +kernel

theorem treePart52_check :
    treePart52.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart52_check_chunked

/-- Subtree splitting on `length[1] - length[7]` in the row-14 length cone, with leaves
selecting cells 100, 107, 108, 109 and Farkas receipts excluding inconsistent sign branches. -/
def treePart53 : CompactCellTree :=
  .split 26
    (.split 15
        (.cell 107 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 15, 13, 16, 14, 19, 17, 303, 12])
        (.split 32
            (.cell 108 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 35, 33, 37, 36, 39, 41,
              304, 32])
            (.absurd 86)))
    (.split 27
        (.split 11
            (.split 15
                (.cell 109 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 56, 57, 58, 64, 61, 65,
                  59, 54])
                (.split 32
                    (.cell 100 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 81, 84, 83, 82,
                      194, 196, 80, 78])
                    (.absurd 209)))
            (.absurd 305))
        (.absurd 306))

private theorem treePart53_check_chunked :
    treePart53.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, -1, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) = true := by
  decide +kernel

theorem treePart53_check :
    treePart53.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, -1, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart53_check_chunked

/-- Subtree splitting on `- length[0] + length[6]` in the row-14 length cone, with leaves
selecting cells 27, 41, 101, 110 and Farkas receipts excluding inconsistent sign branches. -/
def treePart54 : CompactCellTree :=
  .split 11
    (.split 15
        (.split 18
            (.split 26
                (.cell 110 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 58, 55, 56, 64, 61, 59,
                  57, 54])
                (.split 27
                    (.cell 27 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 82, 83, 81, 195,
                      194, 80, 84, 78])
                    (.absurd 296)))
            (.absurd 289))
        (.split 26
            (.split 32
                (.split 18
                    (.cell 101 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 80, 79, 81, 83,
                      194, 82, 84, 78])
                    (.absurd 290))
                (.absurd 307))
            (.split 27
                (.split 32
                    (.split 18
                        (.cell 41 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 199, 104, 103,
                          108, 198, 106, 197, 100])
                        (.absurd 308))
                    (.absurd 189))
                (.absurd 309))))
    (.absurd 310)

private theorem treePart54_check_chunked :
    treePart54.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, -1, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) = true := by
  decide +kernel

theorem treePart54_check :
    treePart54.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, -1, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart54_check_chunked

/-- Subtree splitting on `length[0] - length[6]` in the row-14 length cone, with leaves
selecting cells 93, 111, 112, 113, 114, 115, 116, 117 and Farkas receipts excluding inconsistent
sign branches. -/
def treePart55 : CompactCellTree :=
  .split 10
    (.split 13
        (.cell 111 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 37, 311, 34, 39, 32, 41, 36,
          312, 35])
        (.split 11
            (.cell 112 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 56, 313, 64, 61, 54, 65,
              58, 282])
            (.split 12
                (.cell 113 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 81, 314, 195, 194, 78,
                  196, 82])
                (.split 14
                    (.split 8
                        (.cell 114 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120,
                          124, 315, 123, 273, 121, 126, 129, 213, 127])
                        (.split 28
                            (.cell 115 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                              150, 316, 149, 223, 147, 161, 153, 215, 155])
                            (.absurd 156)))
                    (.split 29
                        (.cell 116 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120,
                          124, 315, 123, 273, 121, 126, 127, 133, 129])
                        (.split 25
                            (.cell 115 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                              150, 316, 149, 223, 147, 161, 155, 215, 153])
                            (.absurd 156)))))))
    (.split 30
        (.cell 117 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 36, 317, 34, 39, 32, 41, 37,
          284])
        (.cell 93 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 36, 304, 34, 39, 32, 41, 37,
          284]))

private theorem treePart55_check_chunked :
    treePart55.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) = true
      := by
  decide +kernel

theorem treePart55_check :
    treePart55.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) = true
      := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart55_check_chunked

/-- Subtree splitting on `length[0] - length[6]` in the row-14 length cone, with leaves
selecting cells 93, 112, 113, 114, 115, 116, 117 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart56 : CompactCellTree :=
  .split 10
    (.split 11
        (.cell 112 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 59, 318, 64, 61, 54, 65, 58,
          56])
        (.split 12
            (.cell 113 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 80, 319, 195, 194, 78, 196,
              82])
            (.split 14
                (.split 8
                    (.cell 114 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 125,
                      320, 123, 273, 121, 126, 129, 213, 127])
                    (.split 28
                        (.cell 115 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                          152, 321, 149, 223, 147, 161, 153, 215, 155])
                        (.absurd 156)))
                (.split 29
                    (.cell 116 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 125,
                      320, 123, 273, 121, 126, 127, 133, 129])
                    (.split 25
                        (.cell 115 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                          152, 321, 149, 223, 147, 161, 155, 215, 153])
                        (.absurd 156))))))
    (.split 30
        (.cell 117 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 58, 55, 64, 61, 54, 65, 59, 56])
        (.split 31
            (.cell 93 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 83, 82, 195, 194, 78, 196,
              80, 81])
            (.absurd 296)))

private theorem treePart56_check_chunked :
    treePart56.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0,
      1, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart56_check :
    treePart56.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0,
      1, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart56_check_chunked

/-- Subtree splitting on `length[0] - length[6]` in the row-14 length cone, with leaves
selecting cells 113, 114, 115, 116, 118 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart57 : CompactCellTree :=
  .split 10
    (.split 11
        (.cell 118 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 59, 55, 64, 61, 54, 65, 58])
        (.split 12
            (.cell 113 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 80, 79, 195, 194, 78, 196,
              82])
            (.split 14
                (.split 8
                    (.cell 114 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 125,
                      122, 123, 273, 121, 126, 129, 213, 127])
                    (.split 28
                        (.cell 115 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                          152, 148, 149, 223, 147, 161, 153, 215, 155])
                        (.absurd 156)))
                (.split 29
                    (.cell 116 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 125,
                      122, 123, 273, 121, 126, 127, 133, 129])
                    (.split 25
                        (.cell 115 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                          152, 148, 149, 223, 147, 161, 155, 215, 153])
                        (.absurd 156))))))
    (.absurd 280)

private theorem treePart57_check_chunked :
    treePart57.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0,
      1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])]) =
      true := by
  decide +kernel

theorem treePart57_check :
    treePart57.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, -1, 0, 0, 0, 0, 0,
      1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])]) =
      true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart57_check_chunked

/-- Subtree splitting on `- length[0] + length[6]` in the row-14 length cone, with leaves
selecting cells 119, 120, 121, 122, 123 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart58 : CompactCellTree :=
  .split 11
    (.split 15
        (.cell 119 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 35, 33, 36, 39, 32, 41, 37])
        (.absurd 322))
    (.split 12
        (.split 15
            (.cell 120 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 57, 55, 58, 61, 54, 65, 59])
            (.absurd 323))
        (.split 13
            (.absurd 298)
            (.split 14
                (.split 8
                    (.split 15
                        (.cell 121 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120,
                          128, 122, 127, 273, 121, 126, 133, 213, 129])
                        (.absurd 324))
                    (.split 28
                        (.split 15
                            (.cell 122 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                              162, 148, 153, 223, 147, 161, 155, 215, 160])
                            (.absurd 325))
                        (.absurd 130)))
                (.split 29
                    (.split 15
                        (.cell 123 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120,
                          128, 122, 127, 273, 121, 126, 129, 125, 133])
                        (.absurd 324))
                    (.split 25
                        (.split 15
                            (.cell 122 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                              162, 148, 153, 223, 147, 161, 160, 215, 155])
                            (.absurd 325))
                        (.absurd 130))))))

private theorem treePart58_check_chunked :
    treePart58.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart58_check :
    treePart58.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart58_check_chunked

/-- Subtree splitting on `length[1] - length[6]` in the row-14 length cone, with leaves
selecting cells 109, 124 and Farkas receipts excluding inconsistent sign branches. -/
def treePart59 : CompactCellTree :=
  .split 30
    (.split 15
        (.cell 124 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 37, 33, 36, 39, 32, 41, 288,
          35])
        (.absurd 322))
    (.split 31
        (.split 4
            (.split 15
                (.cell 109 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 81, 80, 82, 194, 78,
                  196, 84, 83])
                (.absurd 326))
            (.absurd 279))
        (.absurd 280))

private theorem treePart59_check_chunked :
    treePart59.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart59_check :
    treePart59.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart59_check_chunked

/-- Subtree splitting on `length[0] - length[6]` in the row-14 length cone, with leaves
selecting cells 25, 60, 61, 62, 63, 64, 65, 72 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart60 : CompactCellTree :=
  .split 10
    (.split 18
        (.split 13
            (.cell 60 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 56, 313, 64, 61, 54, 59, 58,
              218, 57])
            (.split 11
                (.cell 61 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 81, 314, 195, 194, 78,
                  80, 82, 285])
                (.split 12
                    (.cell 62 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 103, 327, 102, 198,
                      100, 104, 106])
                    (.split 14
                        (.split 8
                            (.cell 63 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                              150, 316, 149, 223, 147, 152, 155, 224, 153])
                            (.split 28
                                (.cell 64 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176,
                                  177, 181, 328, 228, 226, 178, 227, 184, 229, 186])
                                (.absurd 230)))
                        (.split 29
                            (.cell 65 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                              150, 316, 149, 223, 147, 152, 153, 160, 155])
                            (.split 25
                                (.cell 64 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176,
                                  177, 181, 328, 228, 226, 178, 227, 186, 229, 184])
                                (.absurd 230)))))))
        (.absurd 329))
    (.split 30
        (.split 18
            (.cell 72 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 59, 330, 64, 61, 54, 58, 56,
              282])
            (.absurd 331))
        (.split 18
            (.cell 25 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 59, 332, 64, 61, 54, 58, 56,
              282])
            (.absurd 331)))

private theorem treePart60_check_chunked :
    treePart60.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart60_check :
    treePart60.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [aff [0, -1, -1, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart60_check_chunked

/-- Subtree splitting on `length[0] - length[6]` in the row-14 length cone, with leaves
selecting cells 25, 62, 63, 64, 65, 81, 83 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart61 : CompactCellTree :=
  .split 10
    (.split 18
        (.split 11
            (.cell 81 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 56, 55, 64, 61, 54, 59, 58])
            (.split 12
                (.cell 62 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 81, 79, 195, 194, 78,
                  80, 82])
                (.split 14
                    (.split 8
                        (.cell 63 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 124,
                          122, 123, 273, 121, 125, 129, 213, 127])
                        (.split 28
                            (.cell 64 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                              150, 148, 149, 223, 147, 152, 153, 215, 155])
                            (.absurd 156)))
                    (.split 29
                        (.cell 65 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 124,
                          122, 123, 273, 121, 125, 127, 133, 129])
                        (.split 25
                            (.cell 64 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                              150, 148, 149, 223, 147, 152, 155, 215, 153])
                            (.absurd 156))))))
        (.absurd 329))
    (.split 30
        (.split 18
            (.cell 83 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 59, 55, 64, 61, 54, 58, 333,
              56])
            (.absurd 331))
        (.split 31
            (.split 4
                (.split 18
                    (.cell 25 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 104, 199, 102, 198,
                      100, 106, 103, 108])
                    (.absurd 334))
                (.absurd 335))
            (.absurd 309)))

private theorem treePart61_check_chunked :
    treePart61.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation (aff [0, -1,
      -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart61_check :
    treePart61.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation (aff [0, -1,
      -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart61_check_chunked

/-- Subtree splitting on `length[4] - length[5]` in the row-14 length cone, with leaves
selecting cells 76, 77, 78, 79, 82 and Farkas receipts excluding inconsistent sign branches. -/
def treePart62 : CompactCellTree :=
  .split 15
    (.split 18
        (.split 11
            (.cell 82 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 57, 55, 56, 61, 54, 59, 58])
            (.split 12
                (.cell 76 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 84, 79, 81, 194, 78, 80,
                  82])
                (.split 13
                    (.cell 82 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 197, 101, 103, 198,
                      100, 104, 295])
                    (.split 14
                        (.split 8
                            (.cell 77 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                              162, 148, 150, 223, 147, 152, 155, 224, 153])
                            (.split 28
                                (.cell 78 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176,
                                  177, 185, 179, 181, 226, 178, 227, 184, 229, 186])
                                (.absurd 230)))
                        (.split 29
                            (.cell 79 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                              162, 148, 150, 223, 147, 152, 153, 151, 155])
                            (.split 25
                                (.cell 78 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176,
                                  177, 185, 179, 181, 226, 178, 227, 186, 229, 184])
                                (.absurd 230)))))))
        (.absurd 329))
    (.absurd 336)

private theorem treePart62_check_chunked :
    treePart62.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart62_check :
    treePart62.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart62_check_chunked

/-- Subtree splitting on `length[1] - length[6]` in the row-14 length cone, with leaves
selecting cells 27, 84 and Farkas receipts excluding inconsistent sign branches. -/
def treePart63 : CompactCellTree :=
  .split 30
    (.split 15
        (.split 18
            (.cell 84 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 56, 55, 59, 61, 54, 58, 276,
              57])
            (.absurd 331))
        (.absurd 322))
    (.split 31
        (.split 4
            (.split 15
                (.split 18
                    (.cell 27 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 103, 104, 108, 198,
                      100, 106, 197, 199])
                    (.absurd 334))
                (.absurd 326))
            (.absurd 279))
        (.absurd 280))

private theorem treePart63_check_chunked :
    treePart63.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart63_check :
    treePart63.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart63_check_chunked

/-- Subtree splitting on `- length[0] + length[6]` in the row-14 length cone, with leaves
selecting cells 125, 126, 127, 128, 129 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart64 : CompactCellTree :=
  .split 11
    (.cell 125 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 19, 14, 15, 17, 16])
    (.split 12
        (.cell 126 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 39, 34, 35, 41, 36])
        (.split 13
            (.cell 125 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 61, 64, 57, 65, 87])
            (.split 14
                (.split 8
                    (.cell 127 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 198, 102,
                      197, 105, 108, 212, 106])
                    (.split 28
                        (.cell 128 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120,
                          121, 122, 273, 123, 128, 126, 127, 214, 129])
                        (.absurd 130)))
                (.split 29
                    (.cell 129 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 198, 102,
                      197, 105, 106, 104, 108])
                    (.split 25
                        (.cell 128 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120,
                          121, 122, 273, 123, 128, 126, 129, 214, 127])
                        (.absurd 130))))))

private theorem treePart64_check_chunked :
    treePart64.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) = true := by
  decide +kernel

theorem treePart64_check :
    treePart64.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart64_check_chunked

/-- Subtree splitting on `- length[0] + length[6]` in the row-14 length cone, with leaves
selecting cells 68, 69, 70, 71, 85 and Farkas receipts excluding inconsistent sign branches. -/
def treePart65 : CompactCellTree :=
  .split 11
    (.split 18
        (.cell 85 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 39, 34, 35, 36, 37])
        (.absurd 337))
    (.split 12
        (.split 18
            (.cell 68 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 61, 64, 57, 58, 59])
            (.absurd 338))
        (.split 13
            (.absurd 298)
            (.split 14
                (.split 8
                    (.split 18
                        (.cell 69 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121,
                          122, 273, 123, 128, 127, 133, 213, 129])
                        (.absurd 339))
                    (.split 28
                        (.split 18
                            (.cell 70 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                              147, 148, 223, 149, 162, 153, 155, 215, 160])
                            (.absurd 340))
                        (.absurd 130)))
                (.split 29
                    (.split 18
                        (.cell 71 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121,
                          122, 273, 123, 128, 127, 129, 125, 133])
                        (.absurd 339))
                    (.split 25
                        (.split 18
                            (.cell 70 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                              147, 148, 223, 149, 162, 153, 160, 215, 155])
                            (.absurd 340))
                        (.absurd 130))))))

private theorem treePart65_check_chunked :
    treePart65.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) = true := by
  decide +kernel

theorem treePart65_check :
    treePart65.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart65_check_chunked

/-- Subtree splitting on `- length[0] + length[6]` in the row-14 length cone, with leaves
selecting cells 119, 120, 121, 122, 123 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart66 : CompactCellTree :=
  .split 11
    (.cell 119 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 39, 35, 37, 41, 36])
    (.split 12
        (.cell 120 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 61, 57, 56, 65, 58])
        (.split 13
            (.cell 119 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 194, 84, 81, 196,
              286])
            (.split 8
                (.split 14
                    (.cell 121 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121,
                      122, 273, 128, 124, 126, 127, 213, 129])
                    (.split 29
                        (.cell 123 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                          147, 148, 223, 162, 150, 161, 153, 165, 155])
                        (.absurd 156)))
                (.split 28
                    (.cell 122 [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121,
                      122, 273, 128, 124, 126, 127, 214, 129])
                    (.split 33
                        (.cell 123 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                          147, 148, 223, 162, 150, 161, 155, 165, 153])
                        (.absurd 156))))))

private theorem treePart66_check_chunked :
    treePart66.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, -1, 0, 0]]) = true := by
  decide +kernel

theorem treePart66_check :
    treePart66.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, -1, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart66_check_chunked

/-- Subtree splitting on `- length[0] + length[6]` in the row-14 length cone, with leaves
selecting cells 76, 77, 78, 79, 82 and Farkas receipts excluding inconsistent sign branches. -/
def treePart67 : CompactCellTree :=
  .split 11
    (.split 18
        (.cell 82 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 61, 57, 56, 58, 59])
        (.absurd 341))
    (.split 12
        (.split 18
            (.cell 76 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 194, 84, 81, 82, 83])
            (.absurd 342))
        (.split 13
            (.absurd 343)
            (.split 14
                (.split 8
                    (.split 18
                        (.cell 77 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                          148, 223, 162, 150, 153, 160, 224, 155])
                        (.absurd 344))
                    (.split 28
                        (.split 18
                            (.cell 78 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177,
                              178, 179, 226, 185, 181, 184, 186, 229, 182])
                            (.absurd 345))
                        (.absurd 156)))
                (.split 29
                    (.split 18
                        (.cell 79 [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
                          148, 223, 162, 150, 153, 155, 165, 160])
                        (.absurd 344))
                    (.split 25
                        (.split 18
                            (.cell 78 [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177,
                              178, 179, 226, 185, 181, 184, 182, 229, 186])
                            (.absurd 345))
                        (.absurd 156))))))

private theorem treePart67_check_chunked :
    treePart67.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) = true := by
  decide +kernel

theorem treePart67_check :
    treePart67.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart67_check_chunked

/-- Contradiction leaf using Farkas receipt 346 to exclude the accumulated affine constraints in
this row-14 branch. -/
def treePart68 : CompactCellTree :=
  .absurd 346

private theorem treePart68_check_chunked :
    treePart68.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0])]) = true := by
  decide +kernel

theorem treePart68_check :
    treePart68.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart68_check_chunked

/-- Subtree splitting on `length[1] - length[6]` in the row-14 length cone, with leaves
selecting cells 27, 41, 84, 86, 100, 109, 124, 130 and Farkas receipts excluding inconsistent
sign branches. -/
def treePart69 : CompactCellTree :=
  .split 30
    (.split 16
        (.split 17
            (.cell 130 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 19, 13, 15, 14, 16, 17, 191, 12])
            (.split 18
                (.cell 86 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 39, 33, 35, 34, 37, 36,
                  192, 32])
                (.absurd 40)))
        (.split 19
            (.split 17
                (.cell 124 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 39, 33, 35, 37, 36, 41,
                  192, 32])
                (.split 18
                    (.cell 84 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 61, 55, 57, 56, 59,
                      58, 193, 54])
                    (.absurd 62)))
            (.absurd 63)))
    (.split 31
        (.split 4
            (.split 16
                (.split 17
                    (.cell 100 [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 61, 57, 59, 64, 58,
                      65, 54, 56])
                    (.split 18
                        (.cell 41 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 194, 84, 80,
                          195, 83, 82, 78, 81])
                        (.absurd 85)))
                (.split 19
                    (.split 17
                        (.cell 109 [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 194, 84, 80,
                          83, 82, 196, 78, 81])
                        (.split 18
                            (.cell 27 [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 198, 197,
                              104, 199, 108, 106, 100, 103])
                            (.absurd 200)))
                    (.absurd 201)))
            (.absurd 202))
        (.absurd 203))

private theorem treePart69_check_chunked :
    treePart69.checkLookup splitForms farkasReceiptLookup cells
      ((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart69_check :
    treePart69.check splitForms farkasReceipts cells
      ((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart69_check_chunked

/-- The complete compact decision tree for row 14 on the length cone, assembling 70 subtrees
whose cell and Farkas certificates are replayed by the cover checker. -/
def tree : CompactCellTree :=
  .split 0
    (.split 1
        (.split 2
            (.split 3
                (.split 4
                    (treePart0)
                    (.split 5
                        (treePart1)
                        (.split 6
                            (treePart2)
                            (.split 7
                                (treePart3)
                                (treePart4)))))
                (treePart5))
            (.split 3
                (.split 4
                    (treePart6)
                    (.split 5
                        (treePart7)
                        (.split 7
                            (treePart8)
                            (.split 8
                                (treePart9)
                                (treePart10)))))
                (treePart11)))
        (.split 9
            (.split 10
                (.split 11
                    (treePart12)
                    (.split 12
                        (treePart13)
                        (.split 13
                            (treePart14)
                            (.split 14
                                (treePart15)
                                (treePart16)))))
                (treePart17))
            (.split 7
                (.split 6
                    (.split 10
                        (.split 2
                            (treePart18)
                            (.split 13
                                (treePart19)
                                (.split 11
                                    (treePart20)
                                    (.split 12
                                        (treePart21)
                                        (treePart22)))))
                        (treePart23))
                    (.split 10
                        (.split 15
                            (treePart24)
                            (.split 13
                                (treePart25)
                                (.split 11
                                    (treePart26)
                                    (.split 12
                                        (treePart27)
                                        (treePart28)))))
                        (treePart29)))
                (.split 2
                    (.split 10
                        (.split 6
                            (treePart30)
                            (.split 11
                                (treePart31)
                                (.split 12
                                    (treePart32)
                                    (treePart33))))
                        (treePart34))
                    (.split 10
                        (.split 16
                            (treePart35)
                            (.split 11
                                (treePart36)
                                (.split 12
                                    (treePart37)
                                    (treePart38))))
                        (treePart39))))))
    (.split 1
        (.split 6
            (.split 2
                (.split 17
                    (treePart40)
                    (treePart41))
                (.split 3
                    (.split 4
                        (treePart42)
                        (.split 16
                            (.split 17
                                (treePart43)
                                (treePart44))
                            (treePart45)))
                    (treePart46)))
            (.split 3
                (.split 17
                    (.split 15
                        (treePart47)
                        (treePart48))
                    (.split 18
                        (.split 4
                            (treePart49)
                            (.split 5
                                (treePart50)
                                (treePart51)))
                        (treePart52)))
                (.split 17
                    (treePart53)
                    (treePart54))))
        (.split 2
            (.split 17
                (.split 6
                    (.split 7
                        (treePart55)
                        (.split 4
                            (treePart56)
                            (treePart57)))
                    (.split 10
                        (treePart58)
                        (treePart59)))
                (.split 6
                    (.split 7
                        (treePart60)
                        (treePart61))
                    (.split 10
                        (treePart62)
                        (treePart63))))
            (.split 10
                (.split 16
                    (.split 17
                        (treePart64)
                        (treePart65))
                    (.split 19
                        (.split 17
                            (treePart66)
                            (treePart67))
                        (treePart68)))
                (treePart69))))

theorem cells_check :
    cells.all (fun cell => cell.certificate.checkClosed 4) = true := by
  simp [cells, cell0_check, cell1_check, cell2_check, cell3_check, cell4_check, cell5_check,
    cell6_check, cell7_check, cell8_check, cell9_check, cell10_check, cell11_check, cell12_check,
    cell13_check, cell14_check, cell15_check, cell16_check, cell17_check, cell18_check,
    cell19_check, cell20_check, cell21_check, cell22_check, cell23_check, cell24_check,
    cell25_check, cell26_check, cell27_check, cell28_check, cell29_check, cell30_check,
    cell31_check, cell32_check, cell33_check, cell34_check, cell35_check, cell36_check,
    cell37_check, cell38_check, cell39_check, cell40_check, cell41_check, cell42_check,
    cell43_check, cell44_check, cell45_check, cell46_check, cell47_check, cell48_check,
    cell49_check, cell50_check, cell51_check, cell52_check, cell53_check, cell54_check,
    cell55_check, cell56_check, cell57_check, cell58_check, cell59_check, cell60_check,
    cell61_check, cell62_check, cell63_check, cell64_check, cell65_check, cell66_check,
    cell67_check, cell68_check, cell69_check, cell70_check, cell71_check, cell72_check,
    cell73_check, cell74_check, cell75_check, cell76_check, cell77_check, cell78_check,
    cell79_check, cell80_check, cell81_check, cell82_check, cell83_check, cell84_check,
    cell85_check, cell86_check, cell87_check, cell88_check, cell89_check, cell90_check,
    cell91_check, cell92_check, cell93_check, cell94_check, cell95_check, cell96_check,
    cell97_check, cell98_check, cell99_check, cell100_check, cell101_check, cell102_check,
    cell103_check, cell104_check, cell105_check, cell106_check, cell107_check, cell108_check,
    cell109_check, cell110_check, cell111_check, cell112_check, cell113_check, cell114_check,
    cell115_check, cell116_check, cell117_check, cell118_check, cell119_check, cell120_check,
    cell121_check, cell122_check, cell123_check, cell124_check, cell125_check, cell126_check,
    cell127_check, cell128_check, cell129_check, cell130_check]

theorem cells_valid : ∀ cell ∈ cells, cell.certificate.ValidClosed 4 := by
  intro cell hCell
  have hChecks := (List.all_eq_true.mp cells_check) cell hCell
  exact (ExplicitPotential.CertificateData.checkClosed_eq_true_iff _ _).mp hChecks

theorem tree_check :
    tree.check splitForms farkasReceipts cells base = true := by
  simp only [tree, CompactCellTree.check_split, Bool.and_true, splitForm0, splitForm1, splitForm2,
    splitForm3, splitForm4, splitForm5, splitForm6, splitForm7, splitForm8, splitForm9, splitForm10,
    splitForm11, splitForm12, splitForm13, splitForm14, splitForm15, splitForm16, splitForm17,
    splitForm18, splitForm19, treePart0_check, treePart1_check, treePart2_check, treePart3_check,
    treePart4_check, treePart5_check, treePart6_check, treePart7_check, treePart8_check,
    treePart9_check, treePart10_check, treePart11_check, treePart12_check, treePart13_check,
    treePart14_check, treePart15_check, treePart16_check, treePart17_check, treePart18_check,
    treePart19_check, treePart20_check, treePart21_check, treePart22_check, treePart23_check,
    treePart24_check, treePart25_check, treePart26_check, treePart27_check, treePart28_check,
    treePart29_check, treePart30_check, treePart31_check, treePart32_check, treePart33_check,
    treePart34_check, treePart35_check, treePart36_check, treePart37_check, treePart38_check,
    treePart39_check, treePart40_check, treePart41_check, treePart42_check, treePart43_check,
    treePart44_check, treePart45_check, treePart46_check, treePart47_check, treePart48_check,
    treePart49_check, treePart50_check, treePart51_check, treePart52_check, treePart53_check,
    treePart54_check, treePart55_check, treePart56_check, treePart57_check, treePart58_check,
    treePart59_check, treePart60_check, treePart61_check, treePart62_check, treePart63_check,
    treePart64_check, treePart65_check, treePart66_check, treePart67_check, treePart68_check,
    treePart69_check]

theorem base_holds (length : Fin 12 → ℕ) :
    ExplicitPotential.FormsHold base (lengthPoint length) := by
  intro form hForm
  simp only [base, List.mem_cons, List.not_mem_nil, or_false] at hForm
  rcases hForm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals simp [aff,
    _root_.Utilities.Certificate.AffineCover.AffineForm.Holds,
    _root_.Utilities.Certificate.AffineCover.AffineForm.eval,
    lengthPoint, Fin.sum_univ_succ]

theorem closedConstruction :
    ClosedSubdivisionDharConstruction row14Core (by norm_num) :=
  closedConstruction_of_compactCellTree (by norm_num) row14_connected
    cells base splitForms farkasReceipts tree base_holds cells_valid tree_check

end AtanasovRanganathan.GenusFiveRow14FixedCover
