/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PeriodicSubtileIndex

/-!
# Canonical subtile row indices

Shared selectors adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace SubtileRowIndices

/-- Source occurrence for a parent slot and quarter turn. -/
abbrev source (parentSlot : Fin 3) (quarterTurn : Fin 4) :
    PeriodicSubtileIndex :=
  if parentSlot = 0 then
    if quarterTurn = 0 then ⟨.A, 0, -1⟩
    else if quarterTurn = 1 then ⟨.B, 1, 1⟩
    else if quarterTurn = 2 then ⟨.B, 0, 1⟩
    else ⟨.A, -1, -1⟩
  else if parentSlot = 1 then
    if quarterTurn = 0 then ⟨.C, 1, 1⟩
    else if quarterTurn = 1 then ⟨.D, -1, 0⟩
    else if quarterTurn = 2 then ⟨.D, -1, -1⟩
    else ⟨.C, 1, 0⟩
  else if quarterTurn = 0 then ⟨.E, -1, 0⟩
  else if quarterTurn = 1 then ⟨.F, 0, -1⟩
  else if quarterTurn = 2 then ⟨.F, 1, 0⟩
  else ⟨.E, 0, 1⟩

/-- Target occurrence for a parent slot and quarter turn. -/
abbrev target (parentSlot : Fin 3) (quarterTurn : Fin 4) :
    PeriodicSubtileIndex :=
  if parentSlot = 0 then
    if quarterTurn = 0 then ⟨.C, 1, 0⟩
    else if quarterTurn = 1 then ⟨.F, 1, 0⟩
    else if quarterTurn = 2 then ⟨.D, -1, 0⟩
    else ⟨.E, -1, 0⟩
  else if parentSlot = 1 then
    if quarterTurn = 0 then ⟨.E, 0, 1⟩
    else if quarterTurn = 1 then ⟨.B, 0, 1⟩
    else if quarterTurn = 2 then ⟨.F, 0, -1⟩
    else ⟨.A, 0, -1⟩
  else if quarterTurn = 0 then ⟨.A, -1, -1⟩
  else if quarterTurn = 1 then ⟨.D, -1, -1⟩
  else if quarterTurn = 2 then ⟨.B, 1, 1⟩
  else ⟨.C, 1, 1⟩

/-- Partner of the source occurrence in the same canonical row. -/
abbrev sourcePartner (parentSlot : Fin 3) (quarterTurn : Fin 4) :
    PeriodicSubtileIndex :=
  if parentSlot = 0 then
    if quarterTurn = 0 then ⟨.B, 1, 1⟩
    else if quarterTurn = 1 then ⟨.B, 0, 1⟩
    else if quarterTurn = 2 then ⟨.A, -1, -1⟩
    else ⟨.A, 0, -1⟩
  else if parentSlot = 1 then
    if quarterTurn = 0 then ⟨.D, -1, 0⟩
    else if quarterTurn = 1 then ⟨.D, -1, -1⟩
    else if quarterTurn = 2 then ⟨.C, 1, 0⟩
    else ⟨.C, 1, 1⟩
  else if quarterTurn = 0 then ⟨.F, 0, -1⟩
  else if quarterTurn = 1 then ⟨.F, 1, 0⟩
  else if quarterTurn = 2 then ⟨.E, 0, 1⟩
  else ⟨.E, -1, 0⟩

/-- Partner of the target occurrence in the same canonical row. -/
abbrev targetPartner (parentSlot : Fin 3) (quarterTurn : Fin 4) :
    PeriodicSubtileIndex :=
  if parentSlot = 0 then
    if quarterTurn = 0 then ⟨.C, 1, 1⟩
    else if quarterTurn = 1 then ⟨.E, 0, 1⟩
    else if quarterTurn = 2 then ⟨.D, -1, -1⟩
    else ⟨.F, 0, -1⟩
  else if parentSlot = 1 then
    if quarterTurn = 0 then ⟨.E, -1, 0⟩
    else if quarterTurn = 1 then ⟨.A, -1, -1⟩
    else if quarterTurn = 2 then ⟨.F, 1, 0⟩
    else ⟨.B, 1, 1⟩
  else if quarterTurn = 0 then ⟨.A, 0, -1⟩
  else if quarterTurn = 1 then ⟨.C, 1, 0⟩
  else if quarterTurn = 2 then ⟨.B, 0, 1⟩
  else ⟨.D, -1, 0⟩

/-- Piece slot and sign corresponding to a six-subtile label. -/
abbrev labelSlot : SixSubtileLabel → Fin 3 × Bool :=
  fun label => match label with
    | .A => (0, true)
    | .B => (0, false)
    | .C => (1, true)
    | .D => (1, false)
    | .E => (2, true)
    | .F => (2, false)

/-- Lattice-block offset of the complementary tile in a canonical row. -/
abbrev blockOffset (parentSlot : Fin 3) (quarterTurn : Fin 4) : Int × Int :=
  if parentSlot = 0 then
    if quarterTurn = 0 ∨ quarterTurn = 3 then (1, 0) else (-1, 0)
  else if parentSlot = 1 then
    if quarterTurn = 0 ∨ quarterTurn = 3 then (0, 1) else (0, -1)
  else if quarterTurn = 0 ∨ quarterTurn = 3 then (-1, -1) else (1, 1)

end SubtileRowIndices
end ApollonianSuperharmonic

end
