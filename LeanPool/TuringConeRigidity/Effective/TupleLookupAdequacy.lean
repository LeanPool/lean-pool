/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/TupleLookupAdequacy.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.UniformSentenceSupport
public import LeanPool.TuringConeRigidity.Effective.TuplePrefixSyntax

/-!
# Tuple Lookup Adequacy
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

variable {M : ZFSet.{u}}

theorem internal_tuple_graph_bound (C : Context M) {A : ZFSet.{u}} (hA : A ∈ M) :
    ∃ G ∈ M, ∀ (n : ℕ) (v : Fin n → ZFSet.{u}),
      (∀ i, v i ∈ A) → tupleGraph v ∈ G := by
  obtain ⟨G,hG,hdef⟩ := internal_power M C.transitive C.power (C.prod_mem C.omega_mem hA)
  refine ⟨G,hG,fun n v hv => (hdef _).mpr ⟨?_,?_⟩⟩
  · exact tupleGraph_mem M C.transitive C.pairing C.union C.omega_mem v
      (fun i => C.transitive A hA _ (hv i))
  · intro z hz
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz
    exact ZFSet.mem_prod.mpr ⟨_,(mem_omega _).mpr ⟨i.val,rfl⟩,_,hv i,rfl⟩

def TupleLookup (G t i x : ZFSet.{u}) : Prop :=
  ∃ n ∈ ZFSet.omega, ∃ g ∈ G, t = ZFSet.pair n g ∧ ZFSet.pair i x ∈ g

theorem tupleLookup_definable (C : Context M) {G : ZFSet.{u}} (hG : G ∈ M) (t i x : ℕ) :
    Definable M (fun e => TupleLookup G (e t) (e i) (e x)) :=
  (((defOrderedPair C (t+2) 1 0).and (defPairMem C (i+2) (x+2) 0)).existsParam hG).existsParam
    C.omega_mem

theorem tupleLookup_spec (G : ZFSet.{u}) {n : ℕ} (v : Fin n → ZFSet.{u})
    (hG : tupleGraph v ∈ G) (i x : ZFSet.{u}) :
    TupleLookup G (tupleCode v) i x ↔ ∃ k : Fin n, i = natSet k.val ∧ x = v k := by
  constructor
  · rintro ⟨m,_,g,_,he,hx⟩
    have hg : g = tupleGraph v := (ZFSet.pair_inj.mp he).2.symm
    rw [hg] at hx
    obtain ⟨k,hk⟩ := ZFSet.mem_range.mp hx
    obtain ⟨hi,hx⟩ := ZFSet.pair_inj.mp hk
    exact ⟨k,hi.symm,hx.symm⟩
  · rintro ⟨k,rfl,rfl⟩
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,tupleGraph v,hG,rfl,
      (tupleGraph_pair v k _).mpr rfl⟩

theorem tupleLookup_nat (G : ZFSet.{u}) {n : ℕ} (v : Fin n → ZFSet.{u})
    (hG : tupleGraph v ∈ G) (i : ℕ) (x : ZFSet.{u}) :
    TupleLookup G (tupleCode v) (natSet i) x ↔ i < n ∧ x = tupleEnv v i := by
  rw [tupleLookup_spec G v hG]
  constructor
  · rintro ⟨k,hi,rfl⟩
    have he := natSet_injective hi
    subst i
    exact ⟨k.isLt,by simp [tupleEnv]⟩
  · rintro ⟨hi,hx⟩
    exact ⟨⟨i,hi⟩,rfl,by simpa [tupleEnv,hi] using hx⟩

def TupleAdequate (Q B G c t : ZFSet.{u}) : Prop :=
  ∃ n ∈ ZFSet.omega, ∃ g ∈ G, ∃ b ∈ ZFSet.omega,
    t = ZFSet.pair n g ∧ BoundWitness Q B c b ∧ b ⊆ n

theorem tupleAdequate_definable (C : Context M) {Q B G : ZFSet.{u}}
    (hQ : Q ∈ M) (hB : B ∈ M) (hG : G ∈ M) (c t : ℕ) :
    Definable M (fun e => TupleAdequate Q B G (e c) (e t)) :=
  ((((defOrderedPair C (t+3) 2 1).and ((boundWitness_definable C hQ hB (c+3) 0).and
    (defSubset C 0 2))).existsParam C.omega_mem).existsParam hG).existsParam C.omega_mem

theorem tupleAdequate_spec (Q B G : ZFSet.{u})
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B) (p : SentenceForm)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hG : tupleGraph v ∈ G) :
    TupleAdequate Q B G (natSet (Encodable.encode p)) (tupleCode v) ↔ p.bound ≤ n := by
  constructor
  · rintro ⟨m,_,g,_,b,_,he,hb,hle⟩
    have hm : m = natSet n := (ZFSet.pair_inj.mp he).1.symm
    obtain ⟨q,hq,rfl⟩ := (boundWitness_spec Q B _ b hQ hB).mp hb
    have hpq : p = q := Encodable.encode_injective (natSet_injective hq)
    subst q
    rw [hm] at hle
    exact (natSet_subset_iff p.bound n).mp hle
  · intro hb
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,tupleGraph v,hG,
      natSet p.bound,(mem_omega _).mpr ⟨p.bound,rfl⟩,rfl,
      (boundWitness_spec Q B _ _ hQ hB).mpr ⟨p,rfl,rfl⟩,
      (natSet_subset_iff p.bound n).mpr hb⟩

def TuplePrefix (A G t x s : ZFSet.{u}) : Prop :=
  (tuplePrefixFormula 0 1 2 3 4 5 6).Eval
    (cons A (cons ZFSet.omega (cons G (cons t (cons x (cons s (fun _ => natSet 0)))))))

theorem tuplePrefix_spec (A G : ZFSet.{u})
    (hG : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) (x s : ZFSet.{u}) (hx : x ∈ A) :
    TuplePrefix A G (tupleCode v) x s ↔ s = tupleCode (Fin.cases x v) :=
  tuplePrefixFormula_spec 0 1 2 3 4 5 6 _ rfl rfl hG v hv rfl hx

theorem tuplePrefix_definable (C : Context M) {G : ZFSet.{u}} (hG : G ∈ M) (a t x s : ℕ) :
    Definable M (fun e => TuplePrefix (e a) G (e t) (e x) (e s)) := by
  let d := cons ZFSet.omega (cons G (fun _ => natSet 0))
  let r : ℕ → ℕ := fun i => match i with
    | 0 => 2*a | 1 => 1 | 2 => 3 | 3 => 2*t | 4 => 2*x | 5 => 2*s | _ => 5
  refine ⟨(tuplePrefixFormula 0 1 2 3 4 5 6).rename r,d,?_,?_⟩
  · intro i
    rcases i with _|_|i
    · exact C.omega_mem
    · exact hG
    · exact C.transitive _ C.omega_mem _ ((mem_omega _).mpr ⟨0,rfl⟩)
  · intro e
    rw [Formula.eval_rename_comp]
    have he : mix e d ∘ r = cons (e a) (cons ZFSet.omega (cons G
        (cons (e t) (cons (e x) (cons (e s) (fun _ => natSet 0)))))) := by
      funext i
      rcases i with _|_|_|_|_|_|i <;> simp only [r, d, Function.comp_apply, mix_even, cons_zero,
        cons_succ] <;> rfl
    rw [he]
    rfl

end TuringRigidity.RelativeConstructible

end OAI
