/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SentenceSupportFormula.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SentenceSupportCertificate
public import LeanPool.TuringConeRigidity.Syntax.SentenceFamilyFormula

/-!
# Sentence Support Formula
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel RelativeConstructible BoundedSetTheory TransitiveNameModel
open BoundedDefinability SetModelFunctions SetModelReals
universe u

variable {M : ZFSet.{u}}

def SetSupportStep (G c b : ZFSet.{u}) : Prop :=
  (∃ i ∈ ZFSet.omega, ∃ j ∈ ZFSet.omega,
    BinaryGraph (fun i j => binary 0 (atom i) (atom j)) i j c ∧ BinaryGraph (fun i j => max i j +
      1) i j b) ∨
  (∃ i ∈ ZFSet.omega, ∃ j ∈ ZFSet.omega,
    BinaryGraph (fun i j => binary 1 (atom i) (atom j)) i j c ∧ BinaryGraph (fun i j => max i j +
      1) i j b) ∨
  (∃ i ∈ ZFSet.omega, ∃ j ∈ ZFSet.omega, ∃ a ∈ ZFSet.omega, ∃ d ∈ ZFSet.omega,
    BinaryGraph (binary 2) i j c ∧ ZFSet.pair i a ∈ G ∧ ZFSet.pair j d ∈ G ∧ BinaryGraph max a d
      b) ∨
  (∃ i ∈ ZFSet.omega, UnaryGraph (unary 3) i c ∧ ZFSet.pair i b ∈ G) ∨
  (∃ i ∈ ZFSet.omega, ∃ a ∈ ZFSet.omega,
    UnaryGraph (unary 4) i c ∧ ZFSet.pair i a ∈ G ∧ UnaryGraph (fun n => n-1) a b)

theorem setSupportStep_encode (G : ZFSet.{u}) (p : SentenceForm) (b : ℕ) :
    SetSupportStep G (natSet (Encodable.encode p)) (natSet b) ↔ SupportStep G p b := by
  unfold SetSupportStep
  simp_rw [omega_exists]
  simp only [BinaryGraph,UnaryGraph,natSet_injective.eq_iff]
  cases p <;>
    simp [SupportStep,HasBound,encode_equal,encode_member,encode_conj,encode_neg,encode_ex,
      binary,unary,cell,atom,Nat.pair_eq_pair]

theorem defPairMem (C : Context M) (i j g : ℕ) :
    Definable M (fun e => ZFSet.pair (e i) (e j) ∈ e g) :=
  ⟨.pairMem (2*i) (2*j) (2*g),fun _ => ZFSet.omega,fun _ => C.omega_mem,
    fun e => by simp only [Formula.eval_pairMem,mix_even]⟩

theorem defOrderedPair (C : Context M) (z i j : ℕ) :
    Definable M (fun e => e z = ZFSet.pair (e i) (e j)) :=
  ⟨.orderedPair (2*z) (2*i) (2*j),fun _ => ZFSet.omega,fun _ => C.omega_mem,
    fun e => by simp only [Formula.eval_orderedPair,mix_even]⟩

theorem defIff {P Q : (ℕ → ZFSet.{u}) → Prop}
    (hp : Definable M P) (hq : Definable M Q) : Definable M (fun e => P e ↔ Q e) :=
  ((defImp hp hq).and (defImp hq hp)).congr (fun _ => iff_def.symm)

theorem setSupportStep_definable (C : Context M) (g c b : ℕ) :
    Definable M (fun e => SetSupportStep (e g) (e c) (e b)) := by
  have hm : Primrec₂ (fun i j : ℕ => max i j + 1) := Primrec.succ.comp Primrec.nat_max
  have ha (t : ℕ) := (((binaryGraph_definable C _ (atomic_primrec t) 1 0 (c+2)).and
    (binaryGraph_definable C _ hm 1 0 (b+2))).existsParam C.omega_mem).existsParam C.omega_mem
  have hc := (((((binaryGraph_definable C _ (binary_primrec 2) 3 2 (c+4)).and
    ((defPairMem C 3 1 (g+4)).and ((defPairMem C 2 0 (g+4)).and
      (binaryGraph_definable C max Primrec.nat_max 1 0 (b+4))))).existsParam
        C.omega_mem).existsParam
        C.omega_mem).existsParam C.omega_mem).existsParam C.omega_mem
  have hn := ((unaryGraph_definable C _ (unary_primrec 3) 0 (c+1)).and
    (defPairMem C 0 (b+1) (g+1))).existsParam C.omega_mem
  have hp : Primrec (fun n : ℕ => n-1) := Primrec.nat_sub.comp Primrec.id (Primrec.const 1)
  have hx := (((unaryGraph_definable C _ (unary_primrec 4) 1 (c+2)).and
    ((defPairMem C 1 0 (g+2)).and (unaryGraph_definable C _ hp 0 (b+2)))).existsParam
      C.omega_mem).existsParam C.omega_mem
  exact defOr (ha 0) (defOr (ha 1) (defOr hc (defOr hn hx)))

def SetSupportRecursion (F G : ZFSet.{u}) : Prop :=
  (∀ z ∈ G, ∃ c ∈ F, ∃ b ∈ ZFSet.omega, z = ZFSet.pair c b) ∧
    ∀ c ∈ F, ∀ b ∈ ZFSet.omega, ZFSet.pair c b ∈ G ↔ SetSupportStep G c b

theorem setSupportRecursion_spec (root : SentenceForm) (G : ZFSet.{u}) :
    SetSupportRecursion (family root) G ↔ SupportRecursion root G := by
  constructor
  · rintro ⟨hn,hr⟩
    constructor
    · intro z hz
      obtain ⟨c,hc,b,hb,rfl⟩ := hn z hz
      obtain ⟨p,hp,rfl⟩ := (mem_family root c).mp hc
      obtain ⟨n,rfl⟩ := (mem_omega b).mp hb
      exact ⟨p,hp,n,rfl⟩
    · intro p hp n
      exact (hr _ ((code_mem_family root p).mpr hp) _ ((mem_omega _).mpr ⟨n,rfl⟩)).trans
        (setSupportStep_encode G p n)
  · rintro ⟨hn,hr⟩
    constructor
    · intro z hz
      obtain ⟨p,hp,n,rfl⟩ := hn z hz
      exact ⟨_,(code_mem_family root p).mpr hp,_,(mem_omega _).mpr ⟨n,rfl⟩,rfl⟩
    · intro c hc b hb
      obtain ⟨p,hp,rfl⟩ := (mem_family root c).mp hc
      obtain ⟨n,rfl⟩ := (mem_omega b).mp hb
      exact (hr p hp n).trans (setSupportStep_encode G p n).symm

theorem setSupportRecursion_definable (C : Context M) (f g : ℕ) :
    Definable M (fun e => SetSupportRecursion (e f) (e g)) := by
  have hn := defAllMem (((defOrderedPair C 2 1 0).existsParam C.omega_mem).existsMem (f+1)) g
  have hr := defAllMem (defAllParam (defIff (defPairMem C 1 0 (g+2))
    (setSupportStep_definable C (g+2) 1 0)) C.omega_mem) f
  exact hn.and hr

end TuringRigidity.SentenceCoding

end OAI
