/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticCommonRequirement.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticCommonRun

/-!
# Arithmetic Common Requirement
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ArithmeticCommonRequirement
open Encodable UniformArithmetic
open EncodedForcing (word word_primrec)

theorem prefix_arith {s t : ℕ → ℕ} (hs : Primrec s) (ht : Primrec t) :
    Arith (fun (_ : Oracles) v => word (s v) <+: word (t v)) :=
  (Arith.pure _ (Primrec.eq.comp (word_primrec.comp hs)
    (Primrec.list_take.comp (Primrec.list_length.comp (word_primrec.comp hs))
      (word_primrec.comp ht)))).congr (fun _ _ => List.prefix_iff_eq_take.symm)

theorem disagree_arith (p q : OracleCode) {s t : ℕ → ℕ}
    (hs : Primrec s) (ht : Primrec t) :
    Arith (fun O v => CommonIdeal.Disagree (O 0) p q (word (s v)) (word (t v))) := by
  let L := left_primrec
  let R := right_primrec
  let base := L.comp (L.comp L)
  have hp := ArithmeticCommonRun.run_arith p (hs.comp base) (R.comp (L.comp L)) (R.comp L)
  have hq := ArithmeticCommonRun.run_arith q (ht.comp base) (R.comp (L.comp L)) R
  have he := (equal (R.comp L) R).neg
  exact (he.and (hp.and hq)).ex.ex.ex.congr (fun _ _ => by
    simp only [CommonIdeal.Disagree,left,right,Nat.unpair_pair])

theorem agree_arith (p q : OracleCode) {s t : ℕ → ℕ}
    (hs : Primrec s) (ht : Primrec t) :
    Arith (fun O v => CommonIdeal.Agree (O 0) p q (word (s v)) (word (t v))) := by
  let L := left_primrec
  let R := right_primrec
  let L2 := L.comp L
  let L3 := L.comp L2
  let L4 := L.comp L3
  let base := L.comp L4
  have hsu := prefix_arith (hs.comp base) (R.comp L4)
  have htv := prefix_arith (ht.comp base) (R.comp L3)
  have hp := ArithmeticCommonRun.run_arith p (R.comp L4) (R.comp L2) (R.comp L)
  have hq := ArithmeticCommonRun.run_arith q (R.comp L3) (R.comp L2) R
  have he := equal (R.comp L) R
  apply (hsu.imp (htv.imp (hp.imp (hq.imp he)))).all.all.all.all.all.congr
  intro O v
  simp only [left,right,Nat.unpair_pair]
  constructor
  · intro h u w n a b hu hw ha hb
    exact h (encode u) (encode w) n a b
      (by simpa [word] using hu) (by simpa [word] using hw)
      (by simpa [word] using ha) (by simpa [word] using hb)
  · intro h u w n a b hu hw ha hb
    exact h (word u) (word w) n a b hu hw ha hb

theorem requirement_arith (p q : OracleCode) {s t : ℕ → ℕ}
    (hs : Primrec s) (ht : Primrec t) :
    Arith (fun O v => CommonIdeal.Requirement (O 0) p q (word (s v)) (word (t v))) :=
  (disagree_arith p q hs ht).or (agree_arith p q hs ht)

end TuringRigidity.ArithmeticCommonRequirement

end OAI
