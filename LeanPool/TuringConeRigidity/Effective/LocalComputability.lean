/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/LocalComputability.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.LocalScan

public import LeanPool.TuringConeRigidity.Effective.StageEngineComputability

/-!
# Local Computability
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.LocalComputability
open Encodable UniformOracle EncodedForcing CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Decode a local-stage state from its condition and two finite priority records. -/
def state (v : ℕ) : LocalStage.State:=
  StageEngineComputability.state LocalStage.stateInterface v

/-- Compute the local generic extension for the next unvisited requirement. -/
def generic (D : LocalInputs.Data) (v : ℕ) : ℕ:=
  StageEngineComputability.generic (LocalStage.procedures D) v

theorem open_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun v => Part.some (LocalStage.openProcedure D v))
      :=
  D.open_recursive

/-- Canonicalize a local condition code at its current active level. -/
def canonical (p : ℕ) : ℕ:=
  StageEngineComputability.canonical p

theorem canonical_eq (p : ℕ) : canonical p = code (condition p):=
  StageEngineComputability.canonical_eq p

/-- Compute the local open extension from the canonical condition and next unvisited
requirement. -/
def genericCanonical (D : LocalInputs.Data) (v : ℕ) : ℕ:=
  StageEngineComputability.genericCanonical (LocalStage.procedures D) v

theorem generic_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun v => Part.some (genericCanonical D v)):=
  StageEngineComputability.generic_recursive (LocalStage.procedures D) (open_recursive D)

@[simp] theorem generic_eq (D : LocalInputs.Data) (v : ℕ) :
    condition (genericCanonical D v) = LocalStage.generic D (state v):=
  StageEngineComputability.generic_eq LocalStage.stateInterface (LocalStage.procedures D) v

/-- Scan the coded local state for an eligible action at the given stage. -/
def stageAction (D : LocalInputs.Data) (s v : ℕ) : ℕ:=
  scan D (genericCanonical D v) (Nat.unpair (Nat.unpair v).2).1 s

theorem stageAction_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun z =>
      Part.some (stageAction D (Nat.unpair z).1 (Nat.unpair z).2)):=
  StageEngineComputability.stageAction_recursive (LocalStage.procedures D)
    (LocalStage.pairProcedure_recursive D) (open_recursive D)

@[simp] theorem stageAction_eq (D : LocalInputs.Data) (s v : ℕ) :
    action (stageAction D s v) = LocalStage.stageAction D s (state v):=
  StageEngineComputability.stageAction_eq LocalStage.stateInterface (LocalStage.procedures D) s v

/-- Select the generic condition or the local candidate named by the stage action. -/
def stageWord (D : LocalInputs.Data) (z : ℕ) : ℕ:=
  StageEngineComputability.stageWord (LocalStage.procedures D) z

theorem stageWord_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun z => Part.some (stageWord D z)):=
  StageEngineComputability.stageWord_recursive (LocalStage.procedures D)
    (LocalStage.pairProcedure_recursive D) (open_recursive D)

theorem stageWord_eq (D : LocalInputs.Data) (s v : ℕ) :
    condition (stageWord D (Nat.pair s v)) = LocalStage.stageWord D s (state v):=
  StageEngineComputability.stageWord_eq LocalStage.stateInterface (LocalStage.procedures D) s v

/-- Append one false bit to both local words and set the next active stage. -/
def grow (p s : ℕ) : ℕ:=
  StageEngineComputability.grow p s

theorem grow_primrec : Primrec₂ grow:=
  StageEngineComputability.grow_primrec

@[simp] theorem condition_grow (p s : ℕ) :
    condition (grow p s) = atLevel (append (condition p) [false]) (s+1):=
  StageEngineComputability.condition_grow p s

/-- Advance the coded local state and update its completed and visited priority records. -/
def advance (D : LocalInputs.Data) (z : ℕ) : ℕ:=
  StageEngineComputability.advance (LocalStage.procedures D) z

theorem advance_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun z => Part.some (advance D z)):=
  StageEngineComputability.advance_recursive (LocalStage.procedures D)
    (LocalStage.pairProcedure_recursive D) (open_recursive D)

theorem advance_eq (D : LocalInputs.Data) (s v : ℕ) :
    state (advance D (Nat.pair s v)) = LocalStage.advance D s (state v):=
  StageEngineComputability.advance_eq LocalStage.stateInterface (LocalStage.procedures D) s v

/-- The coded empty local state. -/
def initial : ℕ:=
  StageEngineComputability.initial

/-- Iterate the coded local-state transition from the empty initial state. -/
def construction (D : LocalInputs.Data) : ℕ → ℕ:=
  StageEngineComputability.construction (LocalStage.procedures D)

theorem construction_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun s => Part.some (construction D s)):=
  StageEngineComputability.construction_recursive (LocalStage.procedures D)
    (LocalStage.pairProcedure_recursive D) (open_recursive D)

theorem construction_eq (D : LocalInputs.Data) (s : ℕ) :
    state (construction D s) = LocalStage.construction D s:=
  StageEngineComputability.construction_eq LocalStage.stateInterface (LocalStage.procedures D) s

theorem conditions_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)}
      (fun s => Part.some (code (LocalStage.conditions D s))):=
  StageEngineComputability.conditions_recursive LocalStage.stateInterface (LocalStage.procedures D)
    (LocalStage.pairProcedure_recursive D) (open_recursive D)

theorem limits_recursive (D : LocalInputs.Data) :
    Reduces (join (leftLimit (LocalStage.conditions D)) (rightLimit (LocalStage.conditions D)))
      (D.bound):=
  StageEngineComputability.limits_recursive LocalStage.stateInterface (LocalStage.procedures D)
    (LocalStage.pairProcedure_recursive D) (open_recursive D)

end
end TuringRigidity.LocalComputability

end OAI
