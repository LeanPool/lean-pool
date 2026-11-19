/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/UniformOracleSimulation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformPrograms
public import LeanPool.TuringConeRigidity.Computability.Joins

/-!
# Uniform Oracle Simulation
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.UniformPrograms
variable {X Z : Type*} {O F H : X → ℕ →. ℕ}

theorem Runs.reindex (h : Runs O F) (g : Z → X) :
    Runs (O ∘ g) (F ∘ g) := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p,fun z => hp (g z)⟩

theorem Runs.simulate (h : Runs O F) (p : OracleCode) :
    Runs O (fun x => OracleCode.eval (F x) p) := by
  induction p with
  | zero => exact primrec (Primrec.const 0)
  | succ => exact primrec Primrec.succ
  | left => exact primrec (Primrec.fst.comp Primrec.unpair)
  | right => exact primrec (Primrec.snd.comp Primrec.unpair)
  | query => exact h
  | pair p q hp hq => exact hp.pair hq
  | comp p q hp hq => exact hp.comp hq
  | prec p q hp hq => exact hp.prec hq
  | find p hp => exact hp.find

theorem Runs.trans (h : Runs O F) (h' : Runs F H) : Runs O H := by
  obtain ⟨p,hp⟩ := h'
  exact (h.simulate p).of_eq (fun x n => congrFun (hp x) n)

theorem fixed_recursive {g f : ℕ →. ℕ} (hf : Nat.RecursiveIn {g} f)
    (hg : Runs O (fun _ => g)) : Runs O (fun _ => f) := by
  obtain ⟨p,hp⟩ := OracleCode.exists_code hf
  exact (hg.simulate p).of_eq (fun _ n => congrFun hp n)

theorem join_left_program (A B : X → Oracle) :
    Runs (fun x => oracleFunction (join (A x) (B x))) (fun x => oracleFunction (A x)) := by
  have hq := @query X (fun x => oracleFunction (join (A x) (B x)))
  exact (hq.comp (primrec (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))).of_eq
    (fun x n => by
      change (Part.some (2*n)).bind (fun input => oracleFunction (join (A x) (B x)) input) = _
      rw [Part.bind_some]
      simp [oracleFunction,join])

theorem join_right_program (A B : X → Oracle) :
    Runs (fun x => oracleFunction (join (A x) (B x))) (fun x => oracleFunction (B x)) := by
  have hq := @query X (fun x => oracleFunction (join (A x) (B x)))
  exact (hq.comp (primrec (Primrec.succ.comp
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)))).of_eq
    (fun x n => by
      change (Part.some (2*n+1)).bind (fun input => oracleFunction (join (A x) (B x)) input) = _
      rw [Part.bind_some]
      simp [oracleFunction,join,Nat.add_div])

end TuringRigidity.UniformPrograms

end OAI
