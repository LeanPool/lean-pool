/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticPrincipalIntersection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticRelations
public import LeanPool.TuringConeRigidity.Representation.GenericIdentity

/-!
# Arithmetic Principal Intersection
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ArithmeticPrincipalIntersection
open Encodable UniformArithmetic TableIndices IndexMatrix

theorem principal_iff_tables (U L R : Oracle) :
    GenericIdentity.PrincipalIntersection U L R ↔
      Reduces U L ∧ Reduces U R ∧ ∀ e : ℕ, IndexPresentation.Dom L e →
        Reduces (tableOracle L e) R → Reduces (tableOracle L e) U := by
  constructor
  · intro h
    have hU := (h (degree U)).mp le_rfl
    refine ⟨hU.1,hU.2,fun e he hR => ?_⟩
    exact (h (degree (tableOracle L e))).mpr
      ⟨represents_reduces ((valid_tableOracle L e).mp he),hR⟩
  · rintro ⟨hL,hR,h⟩ b
    obtain ⟨A,rfl⟩ := degree_surjective b
    constructor
    · intro hA
      exact ⟨reduces_trans hA hL,reduces_trans hA hR⟩
    · rintro ⟨haL,haR⟩
      change Reduces A R at haR
      change Reduces A U
      obtain ⟨d,hd⟩ := (reduces_iff_represents A L).mp haL
      have he : Represents L (machine (encode d)) A := by simpa using hd
      have hvalid : IndexPresentation.Dom L (encode d) :=
        (valid_iff_represents L _).mpr ⟨A,he⟩
      have ht := tableOracle_eq he
      have hh := h (encode d) hvalid (by simpa only [ht] using haR)
      simpa only [ht] using hh

theorem principal_arith {U L R : OracleFamily}
    (hU : ArithmeticOracle U) (hL : ArithmeticOracle L) (hR : ArithmeticOracle R) :
    Arith (fun O v => GenericIdentity.PrincipalIntersection (U O v) (L O v) (R O v)) := by
  have hleft := reduces_arith hU hL
  have hright := reduces_arith hU hR
  have hd := valid_arith (hL.comp left_primrec) right_primrec
  have hout := tableOracle_arith (hL.comp left_primrec) right_primrec
  have hr := reduces_arith hout (hR.comp left_primrec)
  have hu := reduces_arith hout (hU.comp left_primrec)
  apply (hleft.and (hright.and (hd.imp (hr.imp hu)).all)).congr
  intro O v
  simp only [left,right,Nat.unpair_pair]
  exact (principal_iff_tables (U O v) (L O v) (R O v)).symm

end TuringRigidity.ArithmeticPrincipalIntersection

end OAI
