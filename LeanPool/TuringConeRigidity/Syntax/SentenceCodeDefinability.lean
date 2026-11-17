/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SentenceCodeDefinability.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SentenceCode
public import LeanPool.TuringConeRigidity.SetModels.SetModelArithmeticSyntax

/-!
# Sentence Code Definability
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.SentenceCoding
open BoundedSetTheory TransitiveNameModel BoundedDefinability SetModelFunctions SetModelSyntax
universe u

variable {M : ZFSet.{u}}

theorem defOr {P Q : (ℕ → ZFSet.{u}) → Prop}
    (hP : Definable M P) (hQ : Definable M Q) : Definable M (fun e => P e ∨ Q e) :=
  (hP.neg.and hQ.neg).neg.congr (fun _ => by tauto)

theorem defImp {P Q : (ℕ → ZFSet.{u}) → Prop}
    (hP : Definable M P) (hQ : Definable M Q) : Definable M (fun e => P e → Q e) :=
  (hP.and hQ.neg).neg.congr (fun _ => by tauto)

theorem defAllMem {P : (ℕ → ZFSet.{u}) → Prop}
    (h : Definable M P) (i : ℕ) : Definable M (fun e => ∀ x ∈ e i, P (cons x e)) :=
  (h.neg.existsMem i).neg.congr (fun _ => by simp)

theorem defAllParam {P : (ℕ → ZFSet.{u}) → Prop} {a : ZFSet.{u}}
    (h : Definable M P) (ha : a ∈ M) : Definable M (fun e => ∀ x ∈ a, P (cons x e)) :=
  (h.neg.existsParam ha).neg.congr (fun _ => by simp)

theorem defMemberParam {a : ZFSet.{u}} (ha : a ∈ M) (i : ℕ) :
    Definable M (fun e => e i ∈ a) :=
  ⟨.member (2*i) 1,fun _ => a,fun _ => ha,fun e => by simp [Formula.Eval,mix]⟩

theorem defSubset (C : Context M) (i j : ℕ) : Definable M (fun e => e i ⊆ e j) :=
  defAllMem (member_definable C 0 (j+1)) i

def UnaryGraph (f : ℕ → ℕ) (x y : ZFSet.{u}) : Prop :=
  ∃ n : ℕ, x = natSet n ∧ y = natSet (f n)

def BinaryGraph (f : ℕ → ℕ → ℕ) (x y z : ZFSet.{u}) : Prop :=
  ∃ n m : ℕ, x = natSet n ∧ y = natSet m ∧ z = natSet (f n m)

theorem unaryGraph_definable (C : Context M) (f : ℕ → ℕ) (hf : Primrec f) (i j : ℕ) :
    Definable M (fun e => UnaryGraph f (e i) (e j)) := by
  obtain ⟨g,hg,hcode⟩ := primrec_graph C hf
  refine (((defMemberParam C.omega_mem i).and (defMemberParam C.omega_mem j)).and
    (pairMem_param hg i j)).congr ?_
  intro e
  simp only [UnaryGraph,mem_omega]
  constructor
  · rintro ⟨⟨⟨n,hn⟩,⟨m,hm⟩⟩,h⟩
    refine ⟨n,hn,?_⟩
    have hm' : m = f n := (hcode n m).mp (by rwa [hn,hm] at h)
    rw [← hm',hm]
  · rintro ⟨n,hn,hm⟩
    exact ⟨⟨⟨n,hn⟩,⟨f n,hm⟩⟩,by rw [hn,hm]; exact (hcode n (f n)).mpr rfl⟩

theorem binaryGraph_definable (C : Context M) (f : ℕ → ℕ → ℕ)
    (hf : Primrec₂ f) (i j k : ℕ) :
    Definable M (fun e => BinaryGraph f (e i) (e j) (e k)) := by
  have hu : Primrec (Nat.unpaired f) := hf.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)
  have hd := ((pairCode_definable C (i+1) (j+1) 0).and
    (unaryGraph_definable C (Nat.unpaired f) hu 0 (k+1))).existsParam C.omega_mem
  refine hd.congr ?_
  intro e
  simp only [cons_zero,cons_succ,UnaryGraph,BinaryGraph]
  constructor
  · rintro ⟨z,_,hz,n,hn,hk⟩
    have hxy := hz.1
    obtain ⟨a,ha,b,hb,he⟩ := ZFSet.mem_prod.mp hxy
    obtain ⟨hi,hj⟩ := ZFSet.pair_inj.mp he
    obtain ⟨a,rfl⟩ := (mem_omega a).mp ha
    obtain ⟨b,rfl⟩ := (mem_omega b).mp hb
    have heq : n = Nat.pair a b := (pairCode_nat a b n).mp (by rwa [hi,hj,hn] at hz)
    exact ⟨a,b,hi,hj,by rw [heq] at hk; simpa [Nat.unpaired,Nat.unpair_pair] using hk⟩
  · rintro ⟨a,b,hi,hj,hk⟩
    refine ⟨natSet (Nat.pair a b),(mem_omega _).mpr ⟨_,rfl⟩,?_,Nat.pair a b,rfl,?_⟩
    · rw [hi,hj]; exact (pairCode_nat a b _).mpr rfl
    · simpa [Nat.unpaired,Nat.unpair_pair] using hk

theorem atom_primrec : Primrec atom := Primrec₂.natPair.comp (Primrec.const 0) Primrec.id

theorem cell_primrec : Primrec₂ cell :=
  Primrec₂.natPair.comp (Primrec.succ.comp Primrec.fst) Primrec.snd

theorem binary_primrec (t : ℕ) : Primrec₂ (binary t) :=
  cell_primrec.comp (Primrec.const (atom t))
    (cell_primrec.comp Primrec.fst (cell_primrec.comp Primrec.snd (Primrec.const (atom 0))))

theorem unary_primrec (t : ℕ) : Primrec (unary t) :=
  cell_primrec.comp (Primrec.const (atom t))
    (cell_primrec.comp Primrec.id (Primrec.const (atom 0)))

theorem atomic_primrec (t : ℕ) : Primrec₂ (fun i j => binary t (atom i) (atom j)) :=
  (binary_primrec t).comp (atom_primrec.comp Primrec.fst) (atom_primrec.comp Primrec.snd)

end TuringRigidity.SentenceCoding

end OAI
