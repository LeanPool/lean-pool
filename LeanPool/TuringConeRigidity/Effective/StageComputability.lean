/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/StageComputability.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.StageScan

public import LeanPool.TuringConeRigidity.Effective.StageEngineComputability

/-!
# Stage Computability
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.StageComputability
open Encodable UniformOracle EncodedForcing CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Decode a priority state from its condition and finite priority records. -/
def state (v : ℕ) : PriorityStage.State:=
  StageEngineComputability.state PriorityStage.stateInterface v

/-- Compute the generic extension for the next unvisited requirement in the coded state. -/
def generic (A : Oracle) (v : ℕ) : ℕ:=
  StageEngineComputability.generic (PriorityStage.procedures A) v

theorem open_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun v => Part.some
      (PriorityStage.openProcedure A v)) :=
  (Classical.choose_spec (EffectiveForcing.uniform_open_decision A A (reduces_refl A))).1

/-- Canonicalize the condition code at its current active level. -/
def canonical (p : ℕ) : ℕ:=
  StageEngineComputability.canonical p

theorem canonical_eq (p : ℕ) : canonical p = code (condition p):=
  StageEngineComputability.canonical_eq p

/-- Compute the generic extension after canonicalizing the coded condition. -/
def genericCanonical (A : Oracle) (v : ℕ) : ℕ:=
  StageEngineComputability.genericCanonical (PriorityStage.procedures A) v

theorem generic_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun v => Part.some (genericCanonical A
      v)):=
  StageEngineComputability.generic_recursive (PriorityStage.procedures A) (open_recursive A)

@[simp] theorem generic_eq (A : Oracle) (v : ℕ) :
    condition (genericCanonical A v) = PriorityStage.generic A (state v):=
  StageEngineComputability.generic_eq PriorityStage.stateInterface (PriorityStage.procedures A) v

/-- Scan the coded priority state for an action at the given stage. -/
def stageAction (A : Oracle) (s v : ℕ) : ℕ:=
  scan A (genericCanonical A v) (Nat.unpair (Nat.unpair v).2).1 s

theorem stageAction_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun z =>
      Part.some (stageAction A (Nat.unpair z).1 (Nat.unpair z).2)):=
  StageEngineComputability.stageAction_recursive (PriorityStage.procedures A)
    (PriorityStage.pairProcedure_recursive A) (open_recursive A)

@[simp] theorem stageAction_eq (A : Oracle) (s v : ℕ) :
    action (stageAction A s v) = PriorityStage.stageAction A s (state v):=
  StageEngineComputability.stageAction_eq PriorityStage.stateInterface
    (PriorityStage.procedures A) s v

/-- Select either the generic coded condition or its chosen priority candidate. -/
def stageWord (A : Oracle) (z : ℕ) : ℕ:=
  StageEngineComputability.stageWord (PriorityStage.procedures A) z

theorem stageWord_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun z => Part.some (stageWord A z)):=
  StageEngineComputability.stageWord_recursive (PriorityStage.procedures A)
    (PriorityStage.pairProcedure_recursive A) (open_recursive A)

theorem stageWord_eq (A : Oracle) (s v : ℕ) :
    condition (stageWord A (Nat.pair s v)) = PriorityStage.stageWord A s (state v):=
  StageEngineComputability.stageWord_eq PriorityStage.stateInterface (PriorityStage.procedures
    A) s v

/-- Append false to both words and set the next active stage. -/
def grow (p s : ℕ) : ℕ:=
  StageEngineComputability.grow p s

theorem grow_primrec : Primrec₂ grow:=
  StageEngineComputability.grow_primrec

@[simp] theorem condition_grow (p s : ℕ) :
    condition (grow p s) = atLevel (append (condition p) [false]) (s+1):=
  StageEngineComputability.condition_grow p s

/-- Advance the coded priority state and update its completed and visited records. -/
def advance (A : Oracle) (z : ℕ) : ℕ:=
  StageEngineComputability.advance (PriorityStage.procedures A) z

theorem advance_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun z => Part.some (advance A z)):=
  StageEngineComputability.advance_recursive (PriorityStage.procedures A)
    (PriorityStage.pairProcedure_recursive A) (open_recursive A)

theorem advance_eq (A : Oracle) (s v : ℕ) :
    state (advance A (Nat.pair s v)) = PriorityStage.advance A s (state v):=
  StageEngineComputability.advance_eq PriorityStage.stateInterface (PriorityStage.procedures A) s v

/-- The coded empty priority state. -/
def initial : ℕ:=
  StageEngineComputability.initial

/-- Iterate the coded priority-state transition from the empty state. -/
def construction (A : Oracle) : ℕ → ℕ:=
  StageEngineComputability.construction (PriorityStage.procedures A)

theorem construction_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun s => Part.some (construction A s)):=
  StageEngineComputability.construction_recursive (PriorityStage.procedures A)
    (PriorityStage.pairProcedure_recursive A) (open_recursive A)

theorem construction_eq (A : Oracle) (s : ℕ) :
    state (construction A s) = PriorityStage.construction A s:=
  StageEngineComputability.construction_eq PriorityStage.stateInterface
    (PriorityStage.procedures A) s

theorem conditions_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)}
      (fun s => Part.some (code (PriorityStage.conditions A s))):=
  StageEngineComputability.conditions_recursive PriorityStage.stateInterface
    (PriorityStage.procedures A)
    (PriorityStage.pairProcedure_recursive A) (open_recursive A)

theorem limits_recursive (A : Oracle) :
    Reduces (join (leftLimit (PriorityStage.conditions A)) (rightLimit (PriorityStage.conditions
      A)))
      (OracleJump.jump A):=
  StageEngineComputability.limits_recursive PriorityStage.stateInterface
    (PriorityStage.procedures A)
    (PriorityStage.pairProcedure_recursive A) (open_recursive A)

end
end TuringRigidity.StageComputability

end OAI
