/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/StageScan.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.PriorityStage

public import LeanPool.TuringConeRigidity.Effective.StageEngineScan

/-!
# Stage Scan
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.StageComputability
open Encodable UniformOracle EncodedForcing CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Primitive-recursive first projection of a natural-number pair code. -/
abbrev f:=
  StageEngineScan.f

/-- Primitive-recursive second projection of a natural-number pair code. -/
abbrev r:=
  StageEngineScan.r

/-- Re-encode the condition words with the specified active level. -/
def levelCode (p t : ℕ) : ℕ:=
  StageEngineScan.levelCode p t

theorem levelCode_primrec : Primrec₂ levelCode:=
  StageEngineScan.levelCode_primrec

theorem levelCode_eq (p t : ℕ) : levelCode p t = code (atLevel (condition p) t):=
  StageEngineScan.levelCode_eq p t

@[simp] theorem condition_levelCode (p t : ℕ) : condition (levelCode p t) = atLevel (condition p)
  t:=
  StageEngineScan.condition_levelCode p t

/-- Compute and normalize the priority candidate encoded by the request. -/
def candidate (A : Oracle) (v : ℕ) : ℕ:=
  StageEngineScan.candidate (PriorityStage.procedures A) v

theorem candidate_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun v => Part.some (candidate A v)):=
  StageEngineScan.candidate_recursive (PriorityStage.procedures A)
    (PriorityStage.pairProcedure_recursive A)

@[simp] theorem candidate_eq (A : Oracle) (t p : ℕ) :
    condition (candidate A (Nat.pair t p)) = PriorityStage.candidate A t (condition p):=
  StageEngineScan.candidate_eq (PriorityStage.procedures A) t p

/-- Record the first unfinished candidate that changes either word in the bounded scan. -/
def scanStep (A : Oracle) (v : ℕ) : ℕ:=
  StageEngineScan.scanStep (PriorityStage.procedures A) v

theorem scanStep_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun v => Part.some (scanStep A v)):=
  StageEngineScan.scanStep_recursive (PriorityStage.procedures A)
    (PriorityStage.pairProcedure_recursive A)

/-- Iterate the priority scan through the first `n` candidate levels. -/
def scan (A : Oracle) (p d n : ℕ) : ℕ:=
  StageEngineScan.scan (PriorityStage.procedures A) p d n

theorem scan_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun v =>
      Part.some (scan A (Nat.unpair (Nat.unpair v).1).1 (Nat.unpair (Nat.unpair v).1).2
        (Nat.unpair v).2)):=
  StageEngineScan.scan_recursive (PriorityStage.procedures A)
    (PriorityStage.pairProcedure_recursive A)

theorem source_scan_succ (A : Oracle) (p : Condition) (d : Finset ℕ) (t n : ℕ) :
    PriorityStage.scan A p d t (n+1) =
      match PriorityStage.scan A p d t n with
      | some i => some i
      | none => if t+n ∉ d ∧ PriorityStage.Changes A (t+n) p then some (t+n) else none:=
  StageEngineScan.source_scan_succ (PriorityStage.procedures A) p d t n

theorem scan_eq (A : Oracle) (p d n : ℕ) :
    scan A p d n = actionCode (PriorityStage.scan A (condition p) (members d) 0 n):=
  StageEngineScan.scan_eq (PriorityStage.procedures A) p d n

end
end TuringRigidity.StageComputability

end OAI
