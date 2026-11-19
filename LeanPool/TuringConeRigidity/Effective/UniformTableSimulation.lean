/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/UniformTableSimulation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformJumpSimulation

/-!
# Uniform Table Simulation
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.UniformPrograms
open Encodable CommonIdeal TableIndices IndexMatrix

theorem table_program (d : ℕ) :
    ∃ p : OracleCode, ∀ Y A : Oracle, Represents Y (machine d) A →
      OracleCode.eval (oracleFunction Y) p = oracleFunction A := by
  let X := {s : Oracle × Oracle // Represents s.1 (machine d) s.2}
  let Y := fun s : X => s.val.1
  have hr := total_comp (run_program Y) (primrec
    (Primrec₂.natPair.comp (Primrec.const d) Primrec.id))
  have hr' : Runs (fun s : X => oracleFunction (Y s)) (fun s v =>
      Part.some (encode (TableIndices.run s.val.1 (machine d) (Nat.unpair v).1 (Nat.unpair v).2)))
        := by
    simpa only [Nat.unpair_pair,Y,id_eq] using hr
  have hs : Runs (fun s => oracleFunction (Y s)) (fun s n => Part.some (bit (s.val.2 n))) :=
    UniformPrograms.total_search hr' (fun (s : X) n => bit (s.val.2 n))
      (fun (s : X) => s.property.1) (fun (s : X) => s.property.2)
  obtain ⟨p,hp⟩ := hs
  exact ⟨p,fun B A h => hp ⟨(B,A),h⟩⟩

theorem program_table (p : OracleCode) :
    ∃ d : ℕ, ∀ Y A : Oracle, OracleCode.eval (oracleFunction Y) p = oracleFunction A →
      Represents Y (machine d) A := by
  have hf : Partrec₂ (fun L : List ℕ => fun n => OracleCode.eval (BranchMachine.lookup L) p n) :=
    OracleCode.eval_partrec BranchMachine.lookup_partrec p
  obtain ⟨d,hd⟩ := partrec_code hf
  have hd' : ∀ L n, d.eval (Nat.pair (encode L) n) = OracleCode.eval (BranchMachine.lookup L) p n :=
    fun L n => hd (L,n)
  refine ⟨encode d,fun Y A he => ?_⟩
  have ha (n : ℕ) : Approximates (oracleFunction A n)
      (fun m => d.eval (Nat.pair (encode (UniformOracle.oraclePrefix (fun k => bit (Y k)) m)) n))
        := by
    simp only [hd']
    rw [← he]
    exact OracleCode.eval_approximates (UniformOracle.prefix_approximates (fun k => bit (Y k))) p n
  rw [machine_encode]
  constructor
  · intro n z a hz
    exact Part.mem_some_iff.mp ((ha n).1 (Nat.unpair z).1 a (Nat.Partrec.Code.evaln_sound hz))
  · intro n
    obtain ⟨m,hm⟩ := (ha n).2 (bit (A n)) (Part.mem_some _)
    obtain ⟨t,ht⟩ := Nat.Partrec.Code.evaln_complete.mp (hm m le_rfl)
    exact ⟨Nat.pair m t,bit (A n),by simpa [TableIndices.run,UniformOracle.trial] using ht⟩

theorem Runs.table_simulation {X : Type*} {Y Z : X → Oracle}
    (h : Runs (fun x => oracleFunction (Z x)) (fun x => oracleFunction (Y x))) (d : ℕ) :
    ∃ e : ℕ, ∀ x : X, ∀ A : Oracle, Represents (Y x) (machine d) A →
      Represents (Z x) (machine e) A := by
  obtain ⟨p,hp⟩ := table_program d
  obtain ⟨q,hq⟩ := h.simulate p
  obtain ⟨e,he⟩ := program_table q
  exact ⟨e,fun x A hA => he (Z x) A ((hq x).trans (hp (Y x) A hA))⟩

end TuringRigidity.UniformPrograms

end OAI
