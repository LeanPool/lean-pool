/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/FixedArithmetic.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.EffectivePresentation
public import LeanPool.TuringConeRigidity.Effective.CodingBounds

/-!
# Fixed Arithmetic
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.FixedArithmetic
open Encodable EncodedForcing ArithmeticHierarchy UniformOracle OracleJump
open ArithmeticModelDecoding SetCoding RelationCoding BoundedDecoding

def zero : Oracle := fun _ => false

theorem low_columns : ∃ C : Oracle,
    Reduces C (jump zero) ∧ Reduces (jump C) (jump zero) ∧
      Function.Injective (fun k => degree (columns C k)) := by
  obtain ⟨C,hC,hlow,hind⟩ := CohenColumns.uniform_low_independent zero
  refine ⟨C,hC,?_,?_⟩
  · have h : degree (jump C) ≤ degree (jump (join zero C)) := jump_mono (reduces_join_right zero C)
    change degree (jump C) ≤ degree (jump zero)
    rw [← hlow]
    exact h
  · intro i j he
    have h := (hind ⊥ ⊥ bot_le bot_le i {j}).mp (by simpa using he.le)
    simpa only [Finset.mem_singleton] using h.2

def rows (C : Oracle) : Oracle := fun v =>
  C (Nat.pair (if (Nat.unpair (Nat.unpair v).1).1 = 0 then (Nat.unpair (Nat.unpair v).1).2
    else (Nat.unpair (Nat.unpair v).1).2+1) (Nat.unpair v).2)

theorem rows_reduces (C : Oracle) : Reduces (rows C) C := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  exact EffectiveFamilies.reindex_reduces C (Primrec₂.natPair.comp
    (Primrec.ite (Primrec.eq.comp (f.comp f) (Primrec.const 0)) (r.comp f) (Primrec.succ.comp
      (r.comp f))) r)

@[simp] theorem row_zero (C : Oracle) (k : ℕ) : columns (rows C) (Nat.pair 0 k) = columns C k := by
  funext n
  simp [columns,rows]

@[simp] theorem row_one (C : Oracle) (k : ℕ) : columns (rows C) (Nat.pair 1 k) = columns C (k+1)
  := by
  funext n
  simp [columns,rows]

theorem successor_code (C : Oracle) : ∃ p : RelationCode 2,
    RelationBelow p (degree (jump C)) ∧ ∀ a b,
      p.Holds (two a b) ↔ ∃ k, a = degree (columns C k) ∧ b = degree (columns C (k+1)) := by
  have hP : RecursivePred (rows C) (fun _ => True) := by
    exact (total_primrec (Primrec.const 1)).of_eq (fun n => by simp)
  obtain ⟨p,hp,hcode⟩ := EffectivePresentation.effective_coding (rows C) (fun _ => True) hP 2
  refine ⟨p,hp.mono (jump_mono (rows_reduces C)),fun a b => ?_⟩
  rw [hcode]
  constructor
  · rintro ⟨k,_,hk⟩
    exact ⟨k,by simpa [two] using (hk 0).symm,by simpa [two] using (hk 1).symm⟩
  · rintro ⟨k,rfl,rfl⟩
    refine ⟨k,trivial,fun i => ?_⟩
    fin_cases i <;> simp [two]

structure Frame where
  C : Oracle
  low : Reduces (jump C) (jump zero)
  injective : Function.Injective (fun k => degree (columns C k))
  successor : RelationCode 2
  below : RelationBelow successor (degree (jump zero))
  spec : ∀ a b, successor.Holds (two a b) ↔
    ∃ k, a = degree (columns C k) ∧ b = degree (columns C (k+1))

theorem frame_exists : Nonempty Frame := by
  obtain ⟨C,_,hlow,hinj⟩ := low_columns
  obtain ⟨S,hS,hs⟩ := successor_code C
  exact ⟨⟨C,hlow,hinj,S,hS.mono hlow,hs⟩⟩

end TuringRigidity.FixedArithmetic

end OAI
