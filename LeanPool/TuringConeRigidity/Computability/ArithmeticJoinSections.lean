/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticJoinSections.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.FiniteJoinSections
public import LeanPool.TuringConeRigidity.Computability.ArithmeticRelations

/-!
# Arithmetic Join Sections
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ArithmeticJoinSections
open Encodable UniformArithmetic FiniteShuffle ShuffleRequirements FiniteJoinSections
open EncodedForcing (word word_primrec)

theorem default_arith {s : ℕ → ℕ} (hs : Primrec s) :
    ArithmeticOracle (fun _ v i => (word (s v)).getD i false) :=
  .pure _ (Primrec.eq.comp ((Primrec.list_getD false).comp
    (word_primrec.comp (hs.comp left_primrec)) right_primrec) (Primrec.const true))

theorem realizes_arith {A : OracleFamily} (hA : ArithmeticOracle A)
    {s c : ℕ → ℕ} (hs : Primrec s) (hc : Primrec c) :
    Arith (fun O v => Realizes (word (s v)) (A O (c v))) := by
  have hb := query_at (default_arith hs) left_primrec right_primrec
  have ha := query_at hA (hc.comp left_primrec) right_primrec
  have he := (hb.iff ha).congr (fun O v => by
    exact Bool.eq_iff_iff.symm)
  exact ((less right_primrec
    (Primrec.list_length.comp (word_primrec.comp (hs.comp left_primrec)))).imp he).all.congr
      (fun _ _ => by simp only [Realizes,Agree,left,right,Nat.unpair_pair])

theorem cover_arith {s t u : ℕ → ℕ} (hs : Primrec s) (ht : Primrec t)
    (hu : Primrec u) : Arith (fun (_ : Oracles) v =>
      Cover (word (s v)) (word (t v)) (word (u v))) := by
  let len := fun {f : ℕ → ℕ} (hf : Primrec f) => Primrec.list_length.comp (word_primrec.comp hf)
  have hls := (less (Primrec.nat_mul.comp (Primrec.const 2) (len hs)) (len hu)).neg
  have hlt := (less (Primrec.nat_mul.comp (Primrec.const 2) (len ht)) (len hu)).neg
  have hr := realizes_arith (join_arith (default_arith hs) (default_arith ht)) hu Primrec.id
  exact (hls.and (hlt.and hr)).congr (fun _ _ => by
    simp only [Cover,not_lt,id_eq])

theorem product_arith {D : Oracles → List Bool → Prop}
    (hD : Arith (fun O v => D O (word v))) {s t : ℕ → ℕ}
    (hs : Primrec s) (ht : Primrec t) :
    Arith (fun O v => Product (D O) (word (s v)) (word (t v))) := by
  have hd := hD.comp _ right_primrec
  have hc := cover_arith (hs.comp left_primrec) (ht.comp left_primrec) right_primrec
  apply (hd.and hc).ex.congr
  intro O v
  simp only [left,right,Nat.unpair_pair]
  constructor
  · rintro ⟨u,hd,hc⟩
    exact ⟨word u,hd,hc⟩
  · rintro ⟨u,hd,hc⟩
    exact ⟨encode u,by simpa [word] using hd,by simpa [word] using hc⟩

theorem section_arith {D : Oracles → List Bool → Prop}
    (hD : Arith (fun O v => D O (word v))) (t : List Bool) :
    Arith (fun O v => Section (D O) t (word v)) := by
  have hp := ArithmeticCommonRequirement.prefix_arith (Primrec.const (encode t)) right_primrec
  have hd := product_arith hD left_primrec right_primrec
  apply (hp.and hd).ex.congr
  intro O v
  simp only [left,right,Nat.unpair_pair]
  constructor
  · rintro ⟨u,ht,hu⟩
    exact ⟨word u,by simpa [word] using ht,hu⟩
  · rintro ⟨u,ht,hu⟩
    exact ⟨encode u,by simpa [word] using ht,by simpa [word] using hu⟩

theorem fiber_arith {D : Oracles → List Bool → Prop}
    (hD : Arith (fun O v => D O (word v))) {A : OracleFamily}
    (hA : ArithmeticOracle A) :
    Arith (fun O v => Fiber (D O) (A O 0) (word v)) := by
  have hr := realizes_arith hA right_primrec (Primrec.const 0)
  have hd := product_arith hD right_primrec left_primrec
  apply (hr.and hd).ex.congr
  intro O v
  simp only [left,right,Nat.unpair_pair]
  constructor
  · rintro ⟨s,hs,hd⟩
    exact ⟨word s,hs,hd⟩
  · rintro ⟨s,hs,hd⟩
    exact ⟨encode s,by simpa [word] using hs,by simpa [word] using hd⟩

end TuringRigidity.ArithmeticJoinSections

end OAI
