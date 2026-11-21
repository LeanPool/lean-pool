/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# Rotation systems and plane graphs

A rotation system cycles the darts with the same initial vertex. Its faces are the cycles of
the permutation that reverses a dart and moves to its successor at the next vertex. A connected
rotation system is plane when its vertex, edge, and face counts satisfy Euler's formula.
-/

@[expose] public section

namespace Kasteleyn

open Finset SimpleGraph

/-! ### Rotation systems and faces -/

section Map

variable {V : Type*} {G : SimpleGraph V}

/-- A rotation system on a simple graph `G`: a permutation `rot` of the darts of `G` which,
for every vertex `v`, permutes the darts leaving `v` in a single cycle. -/
structure RotationSystem (G : SimpleGraph V) where
  /-- The successor of a dart in the cyclic order of the darts leaving its initial vertex. -/
  rot : Equiv.Perm G.Dart
  fst_rot : ∀ d, (rot d).fst = d.fst
  sameCycle_of_fst_eq : ∀ d d' : G.Dart, d.fst = d'.fst → rot.SameCycle d d'

/-- The reversal of darts as a permutation. -/
def dartRev (G : SimpleGraph V) : Equiv.Perm G.Dart :=
  Function.Involutive.toPerm _ Dart.symm_involutive

namespace RotationSystem

variable (M : RotationSystem G)

/-- The face permutation: the boundary walk of a face continues a dart `d` by the successor of
`d.symm` in the rotation at the head of `d`. -/
def faceNext : Equiv.Perm G.Dart := (dartRev G).trans M.rot

/-- The faces: the cycles of the face permutation. -/
def Face : Type _ := Quotient (Equiv.Perm.SameCycle.setoid M.faceNext)

/-- The face of a dart: the face whose boundary walk traverses the dart. -/
def face (d : G.Dart) : M.Face := Quotient.mk _ d

section Fintype

variable [Fintype V] [DecidableRel G.Adj]

variable [DecidableEq V]

instance : DecidableEq M.Face :=
  @Quotient.decidableEq _ _ (Equiv.Perm.instDecidableRelSameCycle M.faceNext)

instance : Fintype M.Face :=
  @Quotient.fintype _ _ _ (Equiv.Perm.instDecidableRelSameCycle M.faceNext)

/-- A rotation system is *plane* (of genus zero) if the graph is connected and Euler's formula
`V - E + F = 2` holds.

Faces are the cycles of the face permutation on the darts, so a graph without edges has no
faces here. A connected graph without edges is a single vertex; it is not plane in this sense
(`1 + 0 ≠ 0 + 2`), so statements assuming `IsPlane` leave it out. -/
structure IsPlane : Prop where
  connected : G.Connected
  euler : Fintype.card V + Fintype.card M.Face = #G.edgeFinset + 2

end Fintype

end RotationSystem

end Map

end Kasteleyn

end
