/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticProgramGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformPartialGraph
public import LeanPool.TuringConeRigidity.Computability.ArithmeticRelations
public import LeanPool.TuringConeRigidity.Representation.GenericTotality

/-!
# Arithmetic Program Graph
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ArithmeticProgramGraph
open Encodable UniformArithmetic IndexMatrix GenericIdentity

theorem eval_arith (p : OracleCode) {B : OracleFamily} (hB : ArithmeticOracle B)
    {c n a : ℕ → ℕ} (hc : Primrec c) (hn : Primrec n) (ha : Primrec a) :
    Arith (fun O v => a v ∈ OracleCode.eval (oracleFunction (B O (c v))) p (n v)) := by
  obtain ⟨d, hd⟩ := UniformPartialGraph.eval_iff_table p
  have h := (run_arith hB (hc.comp left_primrec) (Primrec.const (encode d))
    (hn.comp left_primrec) right_primrec (ha.comp left_primrec)).ex
  exact h.congr (fun O v => by
    simpa only [left, right, Nat.unpair_pair, machine_encode, Option.mem_def] using
      (hd (B O (c v)) (n v) (a v)).symm)

theorem output_arith (p : OracleCode) {B : OracleFamily} (hB : ArithmeticOracle B) :
    ArithmeticOracle (fun O v => programOutput p (B O v)) :=
  (eval_arith p hB left_primrec right_primrec (Primrec.const 1)).congr
    (fun _ _ => by simp [programOutput])

theorem value_arith (p : OracleCode) {P A : OracleFamily}
    (hP : ArithmeticOracle P) (hA : ArithmeticOracle A) :
    ArithmeticOracle (fun O v => value p (P O v) (A O v)) :=
  output_arith p (join_arith hA hP)

theorem total_arith (p : OracleCode) {P A : OracleFamily}
    (hP : ArithmeticOracle P) (hA : ArithmeticOracle A) :
    Arith (fun O v => Total p (P O v) (A O v)) := by
  have hB := join_arith hA hP
  have h0 := eval_arith p hB left_primrec right_primrec (Primrec.const 0)
  have h1 := eval_arith p hB left_primrec right_primrec (Primrec.const 1)
  exact (h0.or h1).all.congr (fun O v => by
    simpa only [left, right, Nat.unpair_pair, BinaryHalts] using
      (total_iff_binaryHalts p (P O v) (A O v)).symm)

end TuringRigidity.ArithmeticProgramGraph

end OAI
