/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelInternalRelations.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelArithmeticClosure

/-!
# Set Model Internal Relations
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelSyntax
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelArithmetic SetModelFunctions
open BoundedDefinability UniformArithmetic Encodable
universe u
noncomputable section
variable {M : ZFSet.{u}}

theorem orderedPair_definable (C : Context M) (i j k : ℕ) :
    Definable M (fun e => e i = ZFSet.pair (e j) (e k)) :=
  ⟨.orderedPair (2*i) (2*j) (2*k),fun _ => ZFSet.omega,
    fun _ => C.omega_mem,fun e => by simp⟩

theorem binary_definition (C : Context M) (R : Oracle → Oracle → Prop)
    (hR : Arith (fun O _ => R (O 0) (O 1))) :
    Definable M (fun e => R (oracleOf (e 0)) (oracleOf (e 1))) := by
  obtain ⟨Q,hQ,hc⟩ := arith_definition C hR
  apply (hQ.existsParam C.omega_mem).congr
  intro e
  rw [omega_exists]
  constructor
  · rintro ⟨n,hn⟩
    exact (hc (cons (natSet n) e) n rfl).mp hn
  · intro h
    exact ⟨0,(hc (cons (natSet 0) e) 0 rfl).mpr h⟩

theorem internal_binary_relation (C : Context M) (R : Oracle → Oracle → Prop)
    (hR : Arith (fun O _ => R (O 0) (O 1))) :
    ∃ g ∈ M, ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ g ↔ R A B := by
  obtain ⟨r,hr,hrc⟩ := internal_reals M C.transitive C.power C.separation C.infinity
  have hd := binary_definition C R hR
  let S := fun e : ℕ → ZFSet.{u} => ∃ x ∈ r, ∃ y ∈ r,
    e 0 = ZFSet.pair x y ∧ R (oracleOf x) (oracleOf y)
  have hS : Definable M S := by
    have h := ((orderedPair_definable C 2 1 0).and
      (hd.subst (fun i => if i=0 then 1 else 0))).existsParam hr
    exact h.existsParam hr
  let g := ZFSet.sep (fun z => S (cons z (fun _ => ZFSet.omega))) (ZFSet.prod r r)
  refine ⟨g,hS.sep_mem C (fun _ => ZFSet.omega) (fun _ => C.omega_mem) (C.prod_mem hr hr),?_⟩
  intro A hA B hB
  have ha : realSet A ∈ r := (hrc _).mpr ⟨A,hA,rfl⟩
  have hb : realSet B ∈ r := (hrc _).mpr ⟨B,hB,rfl⟩
  simp only [g,ZFSet.mem_sep,ZFSet.pair_mem_prod,ha,hb,true_and,S,cons_zero]
  constructor
  · rintro ⟨x,hx,y,hy,hxy,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hxy
    simpa only [oracleOf_realSet] using h
  · intro h
    exact ⟨realSet A,ha,realSet B,hb,rfl,by simpa only [oracleOf_realSet] using h⟩

theorem jump_equal_arith : Arith (fun O _ => O 1 = OracleJump.jump (O 0)) := by
  have h := ((query_at (parameter_arith 1) (Primrec.const 0) right_primrec).iff
    (query_at (jump_arith (parameter_arith 0)) (Primrec.const 0) right_primrec)).all
  apply h.congr
  intro O v
  simp only [right,Nat.unpair_pair]
  constructor
  · intro hh
    funext n
    have hn := hh n
    cases ha : O 1 n <;> cases hb : OracleJump.jump (O 0) n <;> simp_all
  · intro h n
    rw [h]

theorem internal_jump_graph (C : Context M) :
    ∃ g ∈ M, ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ g ↔ B = OracleJump.jump A :=
  internal_binary_relation C (fun A B => B = OracleJump.jump A) jump_equal_arith

theorem internal_degreeEquality_graph (C : Context M) :
    ∃ g ∈ M, ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ g ↔ degree A = degree B :=
  internal_binary_relation C (fun A B => degree A = degree B)
    (degree_equal_arith (parameter_arith 0) (parameter_arith 1))

end
end TuringRigidity.SetModelSyntax

end OAI
