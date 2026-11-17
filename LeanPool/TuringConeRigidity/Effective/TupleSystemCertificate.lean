/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/TupleSystemCertificate.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.VariableTruthSyntax

/-!
# Tuple System Certificate
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem tuplePrefix_sound (A G x s : ZFSet.{u}) {n : ℕ}
    (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) (hx : x ∈ A)
    (hs : TuplePrefix A G (tupleCode v) x s) :
    s = tupleCode (Fin.cases (motive := fun _ => ZFSet.{u}) x v) := by
  unfold TuplePrefix at hs
  simp only [tuplePrefixFormula,Formula.Eval,Formula.eval_orderedPair,
    cons_zero,cons_succ] at hs
  simp only [prefixGraphsFormula,Formula.Eval,Formula.eval_successor,
    Formula.eval_functionGraph,Formula.eval_pairMem,Formula.eval_allMem,
    Formula.eval_imp,cons_zero,cons_succ] at hs
  change ∃ n' ∈ ZFSet.omega, ∃ g ∈ G, ∃ m ∈ ZFSet.omega, ∃ h ∈ G,
    tupleCode v = ZFSet.pair n' g ∧ s = ZFSet.pair m h ∧
      PrefixGraphs A n' g m h x at hs
  obtain ⟨n',_,g,_,m,_,h,_,he,hs,hp⟩ := hs
  obtain ⟨hn,hg⟩ := ZFSet.pair_inj.mp he
  rw [← hn] at hp
  obtain ⟨hm,hh⟩ := (prefixGraphs_spec A g m h x v hv hx hg.symm).mp hp
  rw [hs,hm,hh]
  rfl

/-- A family of set-coded finite tuples containing the empty tuple and closed under prepending
entries. -/
def TupleSystem (A G T : ZFSet.{u}) : Prop :=
  (∀ t ∈ T, ∃ n ∈ ZFSet.omega, ∃ g ∈ G,
    t = ZFSet.pair n g ∧ FunctionGraph n A g) ∧
  ZFSet.pair (natSet 0) (natSet 0) ∈ T ∧
  ∀ t ∈ T, ∀ x ∈ A, ∃ s ∈ T, TuplePrefix A G t x s

theorem tupleSystem_definable {M : ZFSet.{u}} (C : Context M) (a G T : ℕ) :
    Definable M (fun e => TupleSystem (e a) (e G) (e T)) := by
  have hfg (f n a : ℕ) : Definable M (fun e => FunctionGraph (e n) (e a) (e f)) := by
    refine ⟨.functionGraph (2*f) (2*n) (2*a),fun _ => ZFSet.omega,
      fun _ => C.omega_mem,?_⟩
    intro e
    simp only [Formula.eval_functionGraph,mix_even,FunctionGraph]
  have hn := defAllMem ((((defOrderedPair C 2 1 0).and
    (hfg 0 1 (a+3))).existsMem (G+2)).existsParam C.omega_mem) T
  have hz : Definable M (fun e => ZFSet.pair (natSet 0) (natSet 0) ∈ e T) := (((equal_param
    (C.nat_mem 0) 0).and
    (defPairMem C 0 0 (T+1))).existsParam C.omega_mem).congr (fun e => by
      simp [show natSet.{u} 0 ∈ ZFSet.omega from (mem_omega _).mpr ⟨0, rfl⟩])
  have hc := defAllMem (defAllMem
    ((tuplePrefix_variable C (a+3) (G+3) 2 1 0).existsMem (T+2)) (a+1)) T
  exact hn.and (hz.and hc)

theorem TupleSystem.exact {A G T : ZFSet.{u}} (h : TupleSystem A G T) :
    T = tupleSpace A ∧ ∀ (n : ℕ) (v : Fin n → ZFSet.{u}),
      (∀ i, v i ∈ A) → tupleGraph v ∈ G := by
  have hin : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleCode v ∈ T := by
    intro n
    induction n with
    | zero =>
      intro v _
      have hg : tupleGraph v = (∅ : ZFSet.{u}) := by
        apply ZFSet.ext; intro z
        simp [tupleGraph]
      change ZFSet.pair (natSet 0) (tupleGraph v) ∈ T
      rw [hg]
      exact h.2.1
    | succ n ih =>
      intro v hv
      let w : Fin n → ZFSet.{u} := fun i => v i.succ
      obtain ⟨s,hs,hp⟩ := h.2.2 (tupleCode w) (ih w (fun i => hv i.succ)) (v 0) (hv 0)
      have he := tuplePrefix_sound A G (v 0) s w (fun i => hv i.succ) (hv 0) hp
      have hvw : (Fin.cases (motive := fun _ => ZFSet.{u}) (v 0) w) = v := by
        funext i; exact Fin.cases rfl (fun _ => rfl) i
      rwa [he,hvw] at hs
  constructor
  · apply ZFSet.ext; intro t
    constructor
    · intro ht
      obtain ⟨n,hn,g,_,he,hg⟩ := h.1 t ht
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      obtain ⟨v,hv,rfl⟩ := functionGraph_tuple A g n hg
      exact (mem_tupleSpace A t).mpr ⟨n,v,hv,he⟩
    · intro ht
      obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
      exact hin n v hv
  · intro n v hv
    obtain ⟨m,_,g,hg,he,_⟩ := h.1 (tupleCode v) (hin n v hv)
    have he' : tupleGraph v = g := (ZFSet.pair_inj.mp he).2
    rwa [← he'] at hg

theorem tupleSystem_canonical (A G : ZFSet.{u})
    (hG : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G) :
    TupleSystem A G (tupleSpace A) := by
  refine ⟨?_,?_,?_⟩
  · intro t ht
    obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
    exact ⟨_,(mem_omega _).mpr ⟨n,rfl⟩,_,hG n v hv,rfl,tupleGraph_function A v hv⟩
  · let v : Fin 0 → ZFSet.{u} := Fin.elim0
    have hg : tupleGraph v = (∅ : ZFSet.{u}) := by
      apply ZFSet.ext; intro z; simp [tupleGraph]
    have ht := (mem_tupleSpace A _).mpr ⟨0,v,fun i => Fin.elim0 i,rfl⟩
    change ZFSet.pair (natSet 0) (tupleGraph v) ∈ tupleSpace A at ht
    rwa [hg] at ht
  · intro t ht x hx
    obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
    let w : Fin (n+1) → ZFSet.{u} := Fin.cases x v
    exact ⟨tupleCode w,(mem_tupleSpace A _).mpr ⟨n+1,w,fun i => Fin.cases hx hv i,rfl⟩,
      (tuplePrefix_spec A G hG v hv x _ hx).mpr rfl⟩

end TuringRigidity.RelativeConstructible

end OAI
