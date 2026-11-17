/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/UniformJumpSimulation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformOracleSimulation
public import LeanPool.TuringConeRigidity.Computability.OracleJump

/-!
# Uniform Jump Simulation
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.UniformPrograms
open Encodable CommonIdeal TableIndices IndexMatrix OracleJump
noncomputable section
variable {X : Type*}

theorem run_program (Y : X → Oracle) :
    Runs (fun x => oracleFunction (Y x)) (fun x v => Part.some
      (encode (run (Y x) (machine (Nat.unpair v).1)
        (Nat.unpair (Nat.unpair v).2).1 (Nat.unpair (Nat.unpair v).2).2))) := by
  let O := fun x => oracleFunction (Y x)
  let e := Primrec.fst.comp Primrec.unpair
  let rest := Primrec.snd.comp Primrec.unpair
  let n := Primrec.fst.comp (Primrec.unpair.comp rest)
  let z := Primrec.snd.comp (Primrec.unpair.comp rest)
  have he := primrec (O := O) e
  have hn := primrec (O := O) n
  have hm := primrec (O := O) (Primrec.fst.comp (Primrec.unpair.comp z))
  have ht := primrec (O := O) (Primrec.snd.comp (Primrec.unpair.comp z))
  have hL := total_comp (initial_program (fun x k => bit (Y x k)) query) hm
  let r := Primrec.snd.comp Primrec.unpair
  have hdecode := primrec (O := O) (Primrec.encode.comp (Nat.Partrec.Code.primrec_evaln.comp
    (((Primrec.fst.comp Primrec.unpair).pair
      (machine_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp r)))).pair
      (Primrec.snd.comp (Primrec.unpair.comp r)))))
  exact (total_comp hdecode (total_pair ht (total_pair he (total_pair hL hn)))).of_eq
    (fun x v => by simp [TableIndices.run,UniformOracle.trial])

/-- Return zero for a decoded successful computation and one for an absent result. -/
def haltFlag (v : ℕ) : ℕ :=
  if ((decode (α := Option ℕ) v).getD none).isSome then 0 else 1

theorem haltFlag_primrec : Primrec haltFlag := by
  apply (Primrec.cond (Primrec.option_isSome.comp
    (Primrec.option_getD_default.comp (Primrec.decode (α := Option ℕ))))
    (Primrec.const 0) (Primrec.const 1)).of_eq
  intro n
  change (cond ((decode (α := Option ℕ) n).getD none).isSome 0 1) = _
  cases h : ((decode (α := Option ℕ) n).getD none).isSome <;>
    simp only [haltFlag,h] <;> rfl

/-- Search for a finite trial witnessing halting of the indexed oracle machine. -/
def haltingSearch (Y : Oracle) (v : ℕ) : Part ℕ :=
  Nat.rfind (fun z => Part.some (run Y (machine (Nat.unpair v).1) (Nat.unpair v).2 z).isSome)

theorem haltingSearch_program (Y : X → Oracle) :
    Runs (fun x => oracleFunction (Y x)) (fun x => haltingSearch (Y x)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hr := total_comp (run_program Y) (primrec
    (Primrec₂.natPair.comp (f.comp f) (Primrec₂.natPair.comp (r.comp f) r)))
  have hh := (total_comp (primrec haltFlag_primrec) hr).find
  apply hh.of_eq
  intro x n
  unfold haltingSearch
  congr 1
  funext z
  simp only [Nat.unpair_pair,haltFlag,encodek,Option.getD_some]
  cases run (Y x) (machine (Nat.unpair n).1) (Nat.unpair n).2 z <;> rfl

theorem haltingSearch_dom (Y : Oracle) (v : ℕ) :
    (haltingSearch Y v).Dom ↔ Halts Y (Nat.unpair v).1 (Nat.unpair v).2 := by
  erw [haltingSearch,Nat.rfind_dom]
  simp [Halts,Option.isSome_iff_exists]

theorem uniform_partial_table (c : OracleCode) :
    ∃ e, ∀ Y : Oracle, ∀ n, Halts Y e n ↔ (OracleCode.eval (oracleFunction Y) c n).Dom := by
  have hh : Partrec₂ (fun L : List ℕ => fun n => OracleCode.eval (BranchMachine.lookup L) c n) :=
    OracleCode.eval_partrec BranchMachine.lookup_partrec c
  obtain ⟨d,hd⟩ := partrec_code hh
  have hd' : ∀ L n, d.eval (Nat.pair (encode L) n) = OracleCode.eval (BranchMachine.lookup L) c n :=
    fun L n => hd (L,n)
  refine ⟨encode d,fun Y n => ?_⟩
  let f := OracleCode.eval (oracleFunction Y) c
  have ha : Approximates (f n) (fun m => d.eval
      (Nat.pair (encode (UniformOracle.oraclePrefix (fun k => bit (Y k)) m)) n)) := by
    simp only [hd']
    exact OracleCode.eval_approximates (UniformOracle.prefix_approximates (fun k => bit (Y k))) c n
  constructor
  · rintro ⟨z,a,hz⟩
    simp only [machine_encode] at hz
    exact (ha.1 (Nat.unpair z).1 a (Nat.Partrec.Code.evaln_sound hz)).1
  · intro hf
    obtain ⟨m,hm⟩ := ha.2 ((f n).get hf) ⟨hf,rfl⟩
    obtain ⟨t,ht⟩ := Nat.Partrec.Code.evaln_complete.mp (hm m le_rfl)
    exact ⟨Nat.pair m t,(f n).get hf,by simpa [TableIndices.run,UniformOracle.trial] using ht⟩

theorem Runs.jump {Y Z : X → Oracle}
    (h : Runs (fun x => oracleFunction (Z x)) (fun x => oracleFunction (Y x))) :
    Runs (fun x => oracleFunction (jump (Z x))) (fun x => oracleFunction (jump (Y x))) := by
  classical
  obtain ⟨c,hc⟩ := h.trans (haltingSearch_program Y)
  obtain ⟨e,he⟩ := uniform_partial_table c
  have hhalts (x : X) (v : ℕ) : Halts (Z x) e v ↔
      Halts (Y x) (Nat.unpair v).1 (Nat.unpair v).2 := by
    rw [he,hc x,haltingSearch_dom]
  have hq := @query X (fun x => oracleFunction (OracleJump.jump (Z x)))
  exact (hq.comp (primrec (Primrec₂.natPair.comp (Primrec.const e) Primrec.id))).of_eq
    (fun x n => by
      change (Part.some (Nat.pair e n)).bind
        (fun input => Part.some (if OracleJump.jump (Z x) input then 1 else 0)) = _
      rw [Part.bind_some]
      simp [oracleFunction,OracleJump.jump,hhalts])

theorem Runs.iterate_jump {Y Z : X → Oracle}
    (h : Runs (fun x => oracleFunction (Z x)) (fun x => oracleFunction (Y x))) (k : ℕ) :
    Runs (fun x => oracleFunction (iterate (Z x) k))
      (fun x => oracleFunction (iterate (Y x) k)) := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih.jump

end
end TuringRigidity.UniformPrograms

end OAI
