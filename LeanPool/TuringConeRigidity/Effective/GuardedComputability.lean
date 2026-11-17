/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/GuardedComputability.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.GuardedScan

public import LeanPool.TuringConeRigidity.Effective.StageEngineComputability

/-!
# Guarded Computability
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.GuardedComputability
open Encodable UniformOracle EncodedForcing CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Decode a guarded-stage state from its condition, completed priorities, and visited
priorities. -/
def state (v : ℕ) : GuardedStage.State:=
  StageEngineComputability.state GuardedStage.stateInterface v

/-- Compute the guarded generic extension for the least unvisited requirement. -/
def generic (A : Oracle) (v : ℕ) : ℕ:=
  StageEngineComputability.generic (GuardedStage.procedures A) v

theorem open_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun v => Part.some
      (GuardedStage.openProcedure A v)) :=
  (Classical.choose_spec (EffectiveForcing.uniform_open_decision A A (reduces_refl A))).1

/-- Canonicalize a condition code at its currently active level. -/
def canonical (p : ℕ) : ℕ:=
  StageEngineComputability.canonical p

theorem canonical_eq (p : ℕ) : canonical p = code (condition p):=
  StageEngineComputability.canonical_eq p

/-- Compute the generic extension using the canonicalized condition code. -/
def genericCanonical (A : Oracle) (v : ℕ) : ℕ:=
  StageEngineComputability.genericCanonical (GuardedStage.procedures A) v

theorem generic_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun v => Part.some (genericCanonical A
      v)):=
  StageEngineComputability.generic_recursive (GuardedStage.procedures A) (open_recursive A)

@[simp] theorem generic_eq (A : Oracle) (v : ℕ) :
    condition (genericCanonical A v) = GuardedStage.generic A (state v):=
  StageEngineComputability.generic_eq GuardedStage.stateInterface (GuardedStage.procedures A) v

/-- Scan for an eligible guarded action at the given stage. -/
def stageAction (A : Oracle) (s v : ℕ) : ℕ:=
  scan A (genericCanonical A v) (Nat.unpair (Nat.unpair v).2).1 s

theorem stageAction_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun z =>
      Part.some (stageAction A (Nat.unpair z).1 (Nat.unpair z).2)):=
  StageEngineComputability.stageAction_recursive (GuardedStage.procedures A)
    (GuardedStage.pairProcedure_recursive A) (open_recursive A)

@[simp] theorem stageAction_eq (A : Oracle) (s v : ℕ) :
    action (stageAction A s v) = GuardedStage.stageAction A s (state v):=
  StageEngineComputability.stageAction_eq GuardedStage.stateInterface (GuardedStage.procedures
    A) s v

/-- Select either the generic condition or the candidate indicated by the stage action. -/
def stageWord (A : Oracle) (z : ℕ) : ℕ:=
  StageEngineComputability.stageWord (GuardedStage.procedures A) z

theorem stageWord_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun z => Part.some (stageWord A z)):=
  StageEngineComputability.stageWord_recursive (GuardedStage.procedures A)
    (GuardedStage.pairProcedure_recursive A) (open_recursive A)

theorem stageWord_eq (A : Oracle) (s v : ℕ) :
    condition (stageWord A (Nat.pair s v)) = GuardedStage.stageWord A s (state v):=
  StageEngineComputability.stageWord_eq GuardedStage.stateInterface (GuardedStage.procedures A) s v

/-- Append one false bit to both words and set the next active stage. -/
def grow (p s : ℕ) : ℕ:=
  StageEngineComputability.grow p s

theorem grow_primrec : Primrec₂ grow:=
  StageEngineComputability.grow_primrec

@[simp] theorem condition_grow (p s : ℕ) :
    condition (grow p s) = atLevel (append (condition p) [false]) (s+1):=
  StageEngineComputability.condition_grow p s

/-- Advance the coded guarded state, updating its condition and priority records. -/
def advance (A : Oracle) (z : ℕ) : ℕ:=
  StageEngineComputability.advance (GuardedStage.procedures A) z

theorem advance_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun z => Part.some (advance A z)):=
  StageEngineComputability.advance_recursive (GuardedStage.procedures A)
    (GuardedStage.pairProcedure_recursive A) (open_recursive A)

theorem advance_eq (A : Oracle) (s v : ℕ) :
    state (advance A (Nat.pair s v)) = GuardedStage.advance A s (state v):=
  StageEngineComputability.advance_eq GuardedStage.stateInterface (GuardedStage.procedures A) s v

/-- The coded empty initial guarded state. -/
def initial : ℕ:=
  StageEngineComputability.initial

/-- The coded guarded-state sequence, obtained by iterating the transition from the empty
initial state. -/
def construction (A : Oracle) : ℕ → ℕ:=
  StageEngineComputability.construction (GuardedStage.procedures A)

theorem construction_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun s => Part.some (construction A s)):=
  StageEngineComputability.construction_recursive (GuardedStage.procedures A)
    (GuardedStage.pairProcedure_recursive A) (open_recursive A)

theorem construction_eq (A : Oracle) (s : ℕ) :
    state (construction A s) = GuardedStage.construction A s:=
  StageEngineComputability.construction_eq GuardedStage.stateInterface (GuardedStage.procedures A) s

theorem conditions_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)}
      (fun s => Part.some (code (GuardedStage.conditions A s))):=
  StageEngineComputability.conditions_recursive GuardedStage.stateInterface
    (GuardedStage.procedures A)
    (GuardedStage.pairProcedure_recursive A) (open_recursive A)

theorem limits_recursive (A : Oracle) :
    Reduces (join (leftLimit (GuardedStage.conditions A)) (rightLimit (GuardedStage.conditions A)))
      (OracleJump.jump A):=
  StageEngineComputability.limits_recursive GuardedStage.stateInterface (GuardedStage.procedures A)
    (GuardedStage.pairProcedure_recursive A) (open_recursive A)

end
end TuringRigidity.GuardedComputability

end OAI
