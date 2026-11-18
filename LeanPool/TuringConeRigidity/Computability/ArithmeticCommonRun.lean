/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticCommonRun.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticTables
public import LeanPool.TuringConeRigidity.CohenForcing.EncodedForcing

/-!
# Arithmetic Common Run
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ArithmeticCommonRun
open Encodable UniformArithmetic UniformOracle
open EncodedForcing (word)

theorem word_eq (s : ℕ) : BorelGeneric.word s = word s := rfl

theorem run_iff_trial (p : OracleCode) (d : Nat.Partrec.Code)
    (hd : ∀ L w, d.eval (Nat.pair (encode L) w) = CommonIdeal.finiteRun p [] L w)
    (A : Oracle) (s n a : ℕ) :
    a ∈ CommonIdeal.run A p (word s) n ↔
      ∃ m c t, Prefix A m c ∧
        d.evaln t (Nat.pair (encode (UniformArithmetic.table c)) (Nat.pair s n)) = some a := by
  have happrox := CommonIdeal.finiteRun_approximates A p [] s n
  simp only [List.nil_append,word_eq] at happrox
  constructor
  · intro ha
    obtain ⟨m,hm⟩ := happrox.2 a ha
    have hh := hm m le_rfl
    dsimp only at hh
    rw [←hd] at hh
    obtain ⟨t,ht⟩ := Nat.Partrec.Code.evaln_complete.mp hh
    let L := oraclePrefix (fun k => CommonIdeal.bit (A k)) m
    refine ⟨m,encode L,t,?_,?_⟩
    · rw [prefix_iff]
      simp [UniformArithmetic.table,L]
    · simpa [UniformArithmetic.table,L] using ht
  · rintro ⟨m,c,t,hp,ht⟩
    have hh := Nat.Partrec.Code.evaln_sound ht
    rw [hd,(prefix_iff A m c).mp hp] at hh
    exact happrox.1 m a hh

theorem run_arith (p : OracleCode) {s n a : ℕ → ℕ}
    (hs : Primrec s) (hn : Primrec n) (ha : Primrec a) :
    Arith (fun O v => a v ∈ CommonIdeal.run (O 0) p (word (s v)) (n v)) := by
  obtain ⟨d,hd⟩ := CommonIdeal.finiteRun_code p []
  let L := left_primrec
  let R := right_primrec
  let base := L.comp (L.comp L)
  have hO : ArithmeticOracle (fun O _ => O 0) := (Arith.query 0).comp _ R
  have hp := prefix_arith hO (Primrec.const 0) (R.comp (L.comp L)) (R.comp L)
  have ht : Arith (fun (_ : Oracles) v =>
      d.evaln (right v)
        (Nat.pair (encode (UniformArithmetic.table (right (left v))))
          (Nat.pair (s (left (left (left v)))) (n (left (left (left v)))))) =
        some (a (left (left (left v))))) :=
    .pure _ (Primrec.eq.comp
      (Nat.Partrec.Code.primrec_evaln.comp
        ((R.pair (Primrec.const d)).pair
          (Primrec₂.natPair.comp (Primrec.encode.comp (table_primrec.comp (R.comp L)))
            (Primrec₂.natPair.comp (hs.comp base) (hn.comp base)))))
      (Primrec.option_some.comp (ha.comp base)))
  apply (hp.and ht).ex.ex.ex.congr
  intro O v
  simp only [left,right,Nat.unpair_pair]
  exact (run_iff_trial p d hd (O 0) (s v) (n v) (a v)).symm

end TuringRigidity.ArithmeticCommonRun

end OAI
