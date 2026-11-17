/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticActions.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticIdeals
public import LeanPool.TuringConeRigidity.OrdinalCodes.NumericalExtension

/-!
# Arithmetic Actions
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.UniformArithmetic
open EncodedForcing NumericalAutomorphism NumericalExtension
noncomputable section

theorem action_arith {H P : OracleFamily} (hH : ArithmeticOracle H)
    (hP : ArithmeticOracle P) : Arith (fun O v => Action (H O v) (fun w => P O v w = true)) := by
  let l := left_primrec
  let r := right_primrec
  have ht := (query_at hP (l.comp l) (Primrec₂.natPair.comp (r.comp l) r)).ex.all
  have hs := (query_at hP (l.comp l) (Primrec₂.natPair.comp r (r.comp l))).ex.all
  let c := l.comp (l.comp (l.comp l))
  let n := r.comp (l.comp (l.comp l))
  let m := r.comp (l.comp l)
  let n' := r.comp l
  let m' := r
  have hp := query_at hP c (Primrec₂.natPair.comp n m)
  have hq := query_at hP c (Primrec₂.natPair.comp n' m')
  have hl := reduces_arith (columns_at hH c n) (columns_at hH c n')
  have hr := reduces_arith (columns_at hH c m) (columns_at hH c m')
  have ho := (hp.imp (hq.imp (hl.iff hr))).all.all.all.all
  let d := l.comp (l.comp l)
  have hp' := query_at hP d (Primrec₂.natPair.comp (r.comp (l.comp l)) (r.comp l))
  have he := degree_equal_arith (columns_at hH d (r.comp l)) (columns_at hH d r)
  have hq' := query_at hP d (Primrec₂.natPair.comp (r.comp (l.comp l)) r)
  have hu := (hp'.imp (he.imp hq')).all.all.all
  apply (ht.and (hs.and (ho.and hu))).congr
  intro O v
  simp only [left,right,Nat.unpair_pair]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩,
    fun h => ⟨h.total,h.onto,h.order,h.saturated⟩⟩

theorem compatible_arith {A H R P : OracleFamily}
    (hA : ArithmeticOracle A) (hH : ArithmeticOracle H)
    (hR : ArithmeticOracle R) (hP : ArithmeticOracle P) :
    Arith (fun O v => Compatible (A O v) (H O v)
      (fun w => R O v w = true) (fun w => P O v w = true)) := by
  let l := left_primrec
  let r := right_primrec
  let c := l.comp (l.comp (l.comp l))
  let i := r.comp (l.comp (l.comp l))
  let j := r.comp (l.comp l)
  let n := r.comp l
  let m := r
  have hr := query_at hR c (Primrec₂.natPair.comp i j)
  have hp := query_at hP c (Primrec₂.natPair.comp n m)
  have hi := degree_equal_arith (columns_at hA c i) (columns_at hH c n)
  have hj := degree_equal_arith (columns_at hA c j) (columns_at hH c m)
  exact (hr.imp (hp.imp (hi.imp hj))).all.all.all.all.congr
    (fun _ _ => by simp only [Compatible,left,right,Nat.unpair_pair])

end
end TuringRigidity.UniformArithmetic

end OAI
