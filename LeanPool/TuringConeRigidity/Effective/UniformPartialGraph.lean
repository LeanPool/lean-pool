/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/UniformPartialGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.TableIndices

/-!
# Uniform Partial Graph
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.UniformPartialGraph
open Encodable UniformOracle CommonIdeal

theorem eval_iff_table (p : OracleCode) :
    ∃ d : Nat.Partrec.Code, ∀ Y : Oracle, ∀ n a : ℕ,
      a ∈ OracleCode.eval (oracleFunction Y) p n ↔
        ∃ z, a ∈ TableIndices.run Y d n z := by
  have hf : Partrec₂ (fun L : List ℕ => fun n =>
      OracleCode.eval (BranchMachine.lookup L) p n) :=
    OracleCode.eval_partrec BranchMachine.lookup_partrec p
  obtain ⟨d, hd⟩ := partrec_code hf
  have hd' (L : List ℕ) (n : ℕ) :
      d.eval (Nat.pair (encode L) n) = OracleCode.eval (BranchMachine.lookup L) p n :=
    hd (L, n)
  refine ⟨d, fun Y n a => ?_⟩
  have ha : Approximates (OracleCode.eval (oracleFunction Y) p n)
      (fun m => d.eval (Nat.pair (encode (oraclePrefix (fun k => bit (Y k)) m)) n)) := by
    simp only [hd']
    exact OracleCode.eval_approximates (prefix_approximates (fun k => bit (Y k))) p n
  constructor
  · intro h
    obtain ⟨m, hm⟩ := ha.2 a h
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp (hm m le_rfl)
    exact ⟨Nat.pair m t, by simpa [TableIndices.run, trial] using ht⟩
  · rintro ⟨z, hz⟩
    exact ha.1 (Nat.unpair z).1 a (Nat.Partrec.Code.evaln_sound hz)

end TuringRigidity.UniformPartialGraph

end OAI
