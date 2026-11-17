/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticShuffleCertificate.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.FiniteShuffleComputation
public import LeanPool.TuringConeRigidity.Computability.UniformArithmetic

/-!
# Arithmetic Shuffle Certificate
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ArithmeticShuffleCertificate
open Encodable UniformArithmetic FiniteShuffleComputation FiniteShuffleCertificate
open EncodedForcing (word word_primrec)

theorem certificate_arith :
    Arith (fun O n => Certificate (fun t => O 0 (encode t) = true) (word n)) := by
  let L := left_primrec
  let R := right_primrec
  let hn := L.comp (L.comp L)
  let hk := R.comp (L.comp L)
  let hs := R.comp L
  have hshuffle := finiteShuffleWord_primrec.comp
    (Primrec₂.natPair.comp hs (Primrec₂.natPair.comp hn R))
  have hquery := (Arith.query 0).comp _ hshuffle
  have hbound := Arith.pure (fun v => right v ≤ right (left (left v)))
    (Primrec.nat_le.comp R hk)
  have hex := (hbound.and hquery).ex
  have hlength := equal (Primrec.list_length.comp (word_primrec.comp R)) (R.comp L)
  have hall := (hlength.imp hex).all
  have hsize := Arith.pure (fun v => 2 * right v ≤ (word (left v)).length)
    (Primrec.nat_le.comp (Primrec.nat_mul.comp (Primrec.const 2) R)
      (Primrec.list_length.comp (word_primrec.comp L)))
  apply (hsize.and hall).ex.congr
  intro O n
  simp only [left,right,Nat.unpair_pair,finiteShuffleWord]
  constructor
  · rintro ⟨k,hk,h⟩
    refine ⟨k,hk,fun s hs => ?_⟩
    have hlen : (word (encode s)).length = k := by simpa [word] using hs
    simpa [word] using h (encode s) hlen
  · rintro ⟨k,hk,h⟩
    exact ⟨k,hk,fun s hs => h (word s) hs⟩

theorem open_arith : Arith (fun O n =>
    ∃ r : List Bool, O 0 (encode r) = true ∧ r <+: word n) := by
  have hp : Arith (fun (_ : Oracles) v => word (right v) <+: word (left v)) :=
    (Arith.pure _ (Primrec.eq.comp (word_primrec.comp right_primrec)
      (Primrec.list_take.comp (Primrec.list_length.comp (word_primrec.comp right_primrec))
        (word_primrec.comp left_primrec)))).congr (fun _ _ => List.prefix_iff_eq_take.symm)
  have hq := (Arith.query 0).comp _ (Primrec.encode.comp (word_primrec.comp right_primrec))
  apply (hq.and hp).ex.congr
  intro O n
  simp only [left,right,Nat.unpair_pair]
  constructor
  · rintro ⟨r,hr,hp⟩
    exact ⟨word r,hr,hp⟩
  · rintro ⟨r,hr,hp⟩
    exact ⟨encode r,by simpa [word] using hr,by simpa [word] using hp⟩

end TuringRigidity.ArithmeticShuffleCertificate

end OAI
