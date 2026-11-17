/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/TableIndices.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.CommonIdealSearch

/-!
# Table Indices
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.TableIndices
open Encodable UniformOracle CommonIdeal

def run (Y : Oracle) (d : Nat.Partrec.Code) (n z : ℕ) : Option ℕ :=
  trial (fun k => bit (Y k)) d n z

def Represents (Y : Oracle) (d : Nat.Partrec.Code) (A : Oracle) : Prop :=
  (∀ n z a, a ∈ run Y d n z → a = bit (A n)) ∧
    ∀ n, ∃ z a, a ∈ run Y d n z

def Valid (Y : Oracle) (d : Nat.Partrec.Code) : Prop :=
  (∀ n, ∃ z b, run Y d n z = some (bit b)) ∧
    ∀ n z w a b, a ∈ run Y d n z → b ∈ run Y d n w → a = b

theorem represents_reduces {Y A : Oracle} {d : Nat.Partrec.Code} (h : Represents Y d A) :
    Reduces A Y := by
  apply RecursiveIn.iff_nat.mpr
  exact total_search (trial_recursive (fun k => bit (Y k)) d) (fun n => bit (A n)) h.1 h.2

theorem reduces_represents {Y A : Oracle} (h : Reduces A Y) :
    ∃ d : Nat.Partrec.Code, Represents Y d A := by
  obtain ⟨e, he⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp h
  have hf : Partrec₂ (fun L : List ℕ => fun n => OracleCode.eval (BranchMachine.lookup L) e n) :=
    OracleCode.eval_partrec BranchMachine.lookup_partrec e
  obtain ⟨d, hd⟩ := partrec_code hf
  have hd' : ∀ L n, d.eval (Nat.pair (encode L) n) = OracleCode.eval (BranchMachine.lookup L) e n :=
    fun L n => hd (L, n)
  have ha (n : ℕ) : Approximates (oracleFunction A n)
      (fun m => d.eval (Nat.pair (encode (oraclePrefix (fun k => bit (Y k)) m)) n)) := by
    simp only [hd']
    rw [← he]
    exact OracleCode.eval_approximates (prefix_approximates (fun k => bit (Y k))) e n
  refine ⟨d, ?_, ?_⟩
  · intro n z a hz
    exact Part.mem_some_iff.mp ((ha n).1 (Nat.unpair z).1 a (Nat.Partrec.Code.evaln_sound hz))
  · intro n
    obtain ⟨m, hm⟩ := (ha n).2 (bit (A n)) (Part.mem_some _)
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp (hm m le_rfl)
    exact ⟨Nat.pair m t, bit (A n), by simpa [run, trial] using ht⟩

theorem reduces_iff_represents (A Y : Oracle) :
    Reduces A Y ↔ ∃ d : Nat.Partrec.Code, Represents Y d A :=
  ⟨reduces_represents, fun ⟨_, h⟩ => represents_reduces h⟩

theorem valid_iff_represents (Y : Oracle) (d : Nat.Partrec.Code) :
    Valid Y d ↔ ∃ A : Oracle, Represents Y d A := by
  constructor
  · rintro ⟨htotal, hconsistent⟩
    choose z A hA using htotal
    refine ⟨A, ?_, ?_⟩
    · intro n w a ha
      exact hconsistent n w (z n) a (bit (A n)) ha (Option.mem_def.mpr (hA n))
    · intro n
      exact ⟨z n, bit (A n), Option.mem_def.mpr (hA n)⟩
  · rintro ⟨A, hs, ht⟩
    refine ⟨?_, ?_⟩
    · intro n
      obtain ⟨z, a, ha⟩ := ht n
      exact ⟨z, A n, by rw [← hs n z a ha]; exact Option.mem_def.mp ha⟩
    · intro n z w a b ha hb
      exact (hs n z a ha).trans (hs n w b hb).symm

theorem represents_unique {Y A B : Oracle} {d : Nat.Partrec.Code}
    (hA : Represents Y d A) (hB : Represents Y d B) : A = B := by
  apply oracleFunction_injective
  funext n
  obtain ⟨z, a, ha⟩ := hA.2 n
  have hh := (hA.1 n z a ha).symm.trans (hB.1 n z a ha)
  exact congrArg Part.some hh

noncomputable def output (Y : Oracle) (d : {d : Nat.Partrec.Code // Valid Y d}) : Oracle :=
  Classical.choose ((valid_iff_represents Y d.val).mp d.property)

theorem output_represents (Y : Oracle) (d : {d : Nat.Partrec.Code // Valid Y d}) :
    Represents Y d.val (output Y d) :=
  Classical.choose_spec ((valid_iff_represents Y d.val).mp d.property)

theorem index_surjective (Y : Oracle) (A : Oracle) (hA : Reduces A Y) :
    ∃ d : {d : Nat.Partrec.Code // Valid Y d}, output Y d = A := by
  obtain ⟨d, hd⟩ := reduces_represents hA
  let e : {d : Nat.Partrec.Code // Valid Y d} := ⟨d, (valid_iff_represents Y d).mpr ⟨A, hd⟩⟩
  exact ⟨e, represents_unique (output_represents Y e) hd⟩

end TuringRigidity.TableIndices

end OAI
