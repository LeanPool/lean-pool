/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/UniformCohenPrefix.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformOracleSimulation
public import LeanPool.TuringConeRigidity.CohenForcing.CohenHalting

/-!
# Uniform Cohen Prefix
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.UniformCohenPrefix
open Encodable UniformPrograms UniformOracle CommonIdeal EncodedForcing CohenHalting
noncomputable section
attribute [local instance] Classical.propDecidable

theorem bit_eq_iff (a b : Bool) : bit a = bit b ↔ a = b := by
  cases a <;> cases b <;> simp [bit]

theorem numericPrefix_iff (G : Oracle) (p : ℕ) :
    oraclePrefix (fun i => bit (G i)) (word p).length = (word p).map bit ↔
      Prefix G (word p) := by
  constructor
  · intro h i hi
    have he := congrArg (fun l : List ℕ => l.getD i 0) h
    have hbit : bit (G i) = bit ((word p).getD i false) := by
      simpa [oraclePrefix,List.getD,hi] using he
    exact (bit_eq_iff _ _).mp hbit
  · intro h
    apply List.ext_getElem
    · simp [oraclePrefix]
    · intro i hi hj
      have hi' : i < (word p).length := by simpa [oraclePrefix] using hi
      simpa [oraclePrefix,List.getD,hi'] using congrArg bit (h i hi')

theorem prefix_program {X : Type*} {O : X → ℕ →. ℕ} (G : X → Oracle)
    (hG : Runs O (fun x => oracleFunction (G x))) :
    Runs O (fun x p => Part.some (if Prefix (G x) (word p) then 1 else 0)) := by
  classical
  have hq : Runs O (fun x i => Part.some (bit (G x i))) := hG
  have hi := total_comp (initial_program (fun x i => bit (G x i)) hq)
    (primrec (Primrec.list_length.comp word_primrec))
  have hw := primrec (O := O) (Primrec.encode.comp
    (Primrec.list_map word_primrec (bit_primrec.comp Primrec.snd).to₂))
  have hc := total_comp (primrec (O := O) (Primrec.ite
    (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))
    (Primrec.const 1) (Primrec.const 0))) (total_pair hi hw)
  exact hc.of_eq (fun x n => by
    simp only [Nat.unpair_pair,encode_injective.eq_iff,numericPrefix_iff])

end
end TuringRigidity.UniformCohenPrefix

end OAI
