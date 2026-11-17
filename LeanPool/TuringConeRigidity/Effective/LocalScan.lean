/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/LocalScan.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.LocalStage

public import LeanPool.TuringConeRigidity.Effective.StageEngineScan

/-!
# Local Scan
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.LocalComputability
open Encodable UniformOracle EncodedForcing CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Primitive-recursive first projection of a natural-number pair code. -/
abbrev f:=
  StageEngineScan.f

/-- Primitive-recursive second projection of a natural-number pair code. -/
abbrev r:=
  StageEngineScan.r

/-- Re-encode the two local words with a specified active level. -/
def levelCode (p t : ℕ) : ℕ:=
  StageEngineScan.levelCode p t

theorem levelCode_primrec : Primrec₂ levelCode:=
  StageEngineScan.levelCode_primrec

theorem levelCode_eq (p t : ℕ) : levelCode p t = code (atLevel (condition p) t):=
  StageEngineScan.levelCode_eq p t

@[simp] theorem condition_levelCode (p t : ℕ) : condition (levelCode p t) = atLevel (condition p)
  t:=
  StageEngineScan.condition_levelCode p t

/-- Compute the local pair candidate and normalize its active level to the requested priority. -/
def candidate (D : LocalInputs.Data) (v : ℕ) : ℕ:=
  StageEngineScan.candidate (LocalStage.procedures D) v

theorem candidate_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun v => Part.some (candidate D v)):=
  StageEngineScan.candidate_recursive (LocalStage.procedures D)
    (LocalStage.pairProcedure_recursive D)

@[simp] theorem candidate_eq (D : LocalInputs.Data) (t p : ℕ) :
    condition (candidate D (Nat.pair t p)) = LocalStage.candidate D t (condition p):=
  StageEngineScan.candidate_eq (LocalStage.procedures D) t p

/-- Keep the first unfinished local candidate whose words differ from the original condition. -/
def scanStep (D : LocalInputs.Data) (v : ℕ) : ℕ:=
  StageEngineScan.scanStep (LocalStage.procedures D) v

theorem scanStep_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun v => Part.some (scanStep D v)):=
  StageEngineScan.scanStep_recursive (LocalStage.procedures D)
    (LocalStage.pairProcedure_recursive D)

/-- Iterate the bounded local candidate scan. -/
def scan (D : LocalInputs.Data) (p d n : ℕ) : ℕ:=
  StageEngineScan.scan (LocalStage.procedures D) p d n

theorem scan_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun v =>
      Part.some (scan D (Nat.unpair (Nat.unpair v).1).1 (Nat.unpair (Nat.unpair v).1).2
        (Nat.unpair v).2)):=
  StageEngineScan.scan_recursive (LocalStage.procedures D) (LocalStage.pairProcedure_recursive D)

theorem source_scan_succ (D : LocalInputs.Data) (p : Condition) (d : Finset ℕ) (t n : ℕ) :
    LocalStage.scan D p d t (n+1) =
      match LocalStage.scan D p d t n with
      | some i => some i
      | none => if t+n ∉ d ∧ LocalStage.Changes D (t+n) p then some (t+n) else none:=
  StageEngineScan.source_scan_succ (LocalStage.procedures D) p d t n

theorem scan_eq (D : LocalInputs.Data) (p d n : ℕ) :
    scan D p d n = actionCode (LocalStage.scan D (condition p) (members d) 0 n):=
  StageEngineScan.scan_eq (LocalStage.procedures D) p d n

end
end TuringRigidity.LocalComputability

end OAI
