/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticRelations.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticOracles

/-!
# Arithmetic Relations
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.UniformArithmetic
open Encodable CommonIdeal IndexMatrix TableIndices OracleJump
noncomputable section

theorem represents_arith {A B : OracleFamily} (hA : ArithmeticOracle A)
    (hB : ArithmeticOracle B) {e : ℕ → ℕ} (he : Primrec e) :
    Arith (fun O v => Represents (B O v) (machine (e v)) (A O v)) := by
  let c := left_primrec.comp (left_primrec.comp left_primrec)
  let n := right_primrec.comp (left_primrec.comp left_primrec)
  let z := right_primrec.comp left_primrec
  have hr := run_arith hB c (he.comp c) n z right_primrec
  have hb := bit_equal hA c n right_primrec
  have h := ((hr.imp hb).all.all.all).and ((hr.and hb).ex.ex.all)
  apply h.congr
  intro O v
  simp only [left,right,Nat.unpair_pair]
  constructor
  · rintro ⟨hs,ht⟩
    exact ⟨fun n z a ha => hs n z a (Option.mem_def.mp ha),
      fun n => by obtain ⟨z,a,ha,_⟩ := ht n; exact ⟨z,a,Option.mem_def.mpr ha⟩⟩
  · rintro ⟨hs,ht⟩
    exact ⟨fun n z a ha => hs n z a (Option.mem_def.mpr ha),
      fun n => by obtain ⟨z,a,ha⟩ := ht n; exact ⟨z,a,Option.mem_def.mp ha,hs n z a ha⟩⟩

theorem valid_tableOracle (B : Oracle) (e : ℕ) :
    Valid B (machine e) ↔ Represents B (machine e) (tableOracle B e) := by
  constructor
  · intro hv
    obtain ⟨A,hA⟩ := (valid_iff_represents B (machine e)).mp hv
    rw [tableOracle_eq hA]
    exact hA
  · intro h
    exact (valid_iff_represents B (machine e)).mpr ⟨_,h⟩

theorem valid_arith {B : OracleFamily} (hB : ArithmeticOracle B)
    {e : ℕ → ℕ} (he : Primrec e) :
    Arith (fun O v => IndexPresentation.Dom (B O v) (e v)) :=
  (represents_arith (tableOracle_arith hB he) hB he).congr
    (fun O v => (valid_tableOracle (B O v) (e v)).symm)

theorem reduces_arith {A B : OracleFamily} (hA : ArithmeticOracle A)
    (hB : ArithmeticOracle B) : Arith (fun O v => Reduces (A O v) (B O v)) := by
  have h := (represents_arith (hA.comp left_primrec) (hB.comp left_primrec) right_primrec).ex
  apply h.congr
  intro O v
  simp only [left,right,Nat.unpair_pair]
  rw [reduces_iff_represents]
  constructor
  · rintro ⟨e,he⟩
    exact ⟨machine e,he⟩
  · rintro ⟨e,he⟩
    exact ⟨encode e,by simpa using he⟩

theorem degree_equal_arith {A B : OracleFamily} (hA : ArithmeticOracle A)
    (hB : ArithmeticOracle B) : Arith (fun O v => degree (A O v) = degree (B O v)) :=
  ((reduces_arith hA hB).and (reduces_arith hB hA)).congr
    (fun O v => (degree_eq_iff (A O v) (B O v)).symm)

theorem join_arith {A B : OracleFamily} (hA : ArithmeticOracle A)
    (hB : ArithmeticOracle B) : ArithmeticOracle (fun O v => join (A O v) (B O v)) := by
  have ht : Arith (fun (_ : Oracles) v => (right v).bodd = true) :=
    .pure _ (Primrec.eq.comp (Primrec.nat_bodd.comp right_primrec) (Primrec.const true))
  have hd : Primrec (fun v => right v / 2) := Primrec.nat_div.comp right_primrec (Primrec.const 2)
  exact ((ht.and (query_at hB left_primrec hd)).or
    (ht.neg.and (query_at hA left_primrec hd))).congr (fun O v => by
      cases h : (right v).bodd <;> simp [join,h])

end
end TuringRigidity.UniformArithmetic

end OAI
