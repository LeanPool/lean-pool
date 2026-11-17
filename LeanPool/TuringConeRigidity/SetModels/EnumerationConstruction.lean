/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/EnumerationConstruction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.EnumerationDecoding
public import LeanPool.TuringConeRigidity.SetModels.FixedArithmetic

/-!
# Enumeration Construction
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.EnumerationConstruction
open Encodable EncodedForcing ArithmeticHierarchy UniformOracle OracleJump
open ArithmeticModelDecoding SetCoding RelationCoding BoundedDecoding EnumerationDecoding

/-- Combine the two column families, reserving the first row tag for `C` and other row tags
for `H`. -/
def rows (C H : Oracle) : Oracle := fun v =>
  if (Nat.unpair (Nat.unpair v).1).1 = 0 then C (Nat.pair (Nat.unpair (Nat.unpair v).1).2
    (Nat.unpair v).2)
  else H (Nat.pair (Nat.unpair (Nat.unpair v).1).2 (Nat.unpair v).2)

theorem rows_reduces (C H : Oracle) : Reduces (rows C H) (join C H) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let p := Primrec₂.natPair.comp (r.comp f) r
  let even := Primrec.nat_mul.comp (Primrec.const 2) p
  have hi := Primrec.ite (Primrec.eq.comp (f.comp f) (Primrec.const 0)) even (Primrec.succ.comp
    even)
  have hh := EffectiveFamilies.reindex_reduces (join C H) hi
  convert hh using 1
  funext v
  by_cases h : (Nat.unpair (Nat.unpair v).1).1 = 0
  · simp only [rows,ite_eq_left h,join_even]
  · simp only [rows,ite_eq_right h,join_odd]

@[simp] theorem row_zero (C H : Oracle) (k : ℕ) : columns (rows C H) (Nat.pair 0 k) = columns C k
  := by
  funext n; simp [columns,rows]

@[simp] theorem row_one (C H : Oracle) (k : ℕ) : columns (rows C H) (Nat.pair 1 k) = columns H k
  := by
  funext n; simp [columns,rows]

theorem payload_code {C H : Oracle} (hC : Reduces C H) : ∃ p : RelationCode 2,
    RelationBelow p (degree (jump H)) ∧ ∀ a b,
      p.Holds (two a b) ↔ ∃ k, a = degree (columns C k) ∧ b = degree (columns H k) := by
  have hP : RecursivePred (rows C H) (fun _ => True) := by
    exact (total_primrec (Primrec.const 1)).of_eq (fun n => by simp)
  obtain ⟨p,hp,hcode⟩ := EffectivePresentation.effective_coding (rows C H) (fun _ => True) hP 2
  have hb := reduces_trans (rows_reduces C H) (join_reduces hC (reduces_refl H))
  refine ⟨p,hp.mono (jump_mono hb),fun a b => ?_⟩
  rw [hcode]
  constructor
  · rintro ⟨k,_,hk⟩
    exact ⟨k,by simpa [two] using (hk 0).symm,by simpa [two] using (hk 1).symm⟩
  · rintro ⟨k,rfl,rfl⟩
    refine ⟨k,trivial,fun i => ?_⟩
    fin_cases i <;> simp [two]

theorem enumeration_exists (H : Oracle) (hz : Reduces (jump FixedArithmetic.zero) H) :
    ∃ c : Enumeration, c.output = (fun k => degree (columns H k)) ∧
      RelationBelow c.successor (degree (jump H)) ∧ RelationBelow c.payload (degree (jump H)) := by
  obtain ⟨K⟩ := FixedArithmetic.frame_exists
  have hC : Reduces K.C H := reduces_trans (reduces_jump K.C) (reduces_trans K.low hz)
  obtain ⟨P,hP,hspec⟩ := payload_code hC
  let c : Enumeration := ⟨fun k => degree (columns K.C k),K.injective,
    fun k => degree (columns H k),K.successor,P,K.spec,hspec⟩
  exact ⟨c,rfl,K.below.mono (reduces_trans hz (reduces_jump H)),hP⟩

end TuringRigidity.EnumerationConstruction

end OAI
