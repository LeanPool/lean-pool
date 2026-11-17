/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ElementaryAxioms.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ElementarySatisfaction

/-!
# Elementary Axioms
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel SentenceForm
universe u

theorem Valid.pairing {M : ZFSet.{u}} (hv : Valid M) : Pairing M := by
  intro a ha b hb
  let p := ex (all (iff (.member 0 1) (disj (.equal 0 2) (.equal 0 3))))
  have hp : ∀ e : ℕ → ZFSet.{u}, p.Sat Set.univ e := by
    intro e
    simp only
      [p,Sat,sat_all,sat_iff,sat_disj,cons_zero,cons_succ,Set.mem_univ,true_and,forall_const]
    exact ⟨{e 0,e 1},fun x => ZFSet.mem_pair⟩
  have h := hv p hp (cons a (fun _ => b)) (by intro i; cases i <;> assumption)
  simpa only [p,Sat,sat_all,sat_iff,sat_disj,cons_zero,cons_succ,SetLike.mem_coe] using h

theorem Valid.union {M : ZFSet.{u}} (hv : Valid M) : BoundedSetTheory.Union M := by
  intro a ha
  let p := ex (all (iff (.member 0 1) (ex (.conj (.member 0 3) (.member 1 0)))))
  have hp : ∀ e : ℕ → ZFSet.{u}, p.Sat Set.univ e := by
    intro e
    simp only [p,Sat,sat_all,sat_iff,cons_zero,cons_succ,Set.mem_univ,true_and,forall_const]
    exact ⟨ZFSet.sUnion (e 0),fun x => ZFSet.mem_sUnion⟩
  have h := hv p hp (fun _ => a) (fun _ => ha)
  simpa only [p,Sat,sat_all,sat_iff,cons_zero,cons_succ,SetLike.mem_coe] using h

theorem Valid.powerSet {M : ZFSet.{u}} (hv : Valid M) : PowerSet M := by
  intro a ha
  let p := ex (all (iff (.member 0 1) (all (imp (.member 0 1) (.member 0 3)))))
  have hp : ∀ e : ℕ → ZFSet.{u}, p.Sat Set.univ e := by
    intro e
    simp only [p,Sat,sat_all,sat_iff,sat_imp,cons_zero,cons_succ,Set.mem_univ,true_and,forall_const]
    exact ⟨ZFSet.powerset (e 0),fun x => ZFSet.mem_powerset⟩
  have h := hv p hp (fun _ => a) (fun _ => ha)
  simpa only [p,Sat,sat_all,sat_iff,sat_imp,cons_zero,cons_succ,SetLike.mem_coe] using h

theorem Valid.empty {M : ZFSet.{u}} (hv : Valid M) (hne : ∃ a, a ∈ M) : BasicAxioms.EmptySet M := by
  obtain ⟨a,ha⟩ := hne
  let p := ex (all (.neg (.member 0 1)))
  have hp : ∀ e : ℕ → ZFSet.{u}, p.Sat Set.univ e := by
    intro e
    simp only [p,Sat,sat_all,cons_zero,cons_succ,Set.mem_univ,true_and,forall_const]
    exact ⟨∅,ZFSet.notMem_empty⟩
  have h := hv p hp (fun _ => a) (fun _ => ha)
  simpa only [BasicAxioms.EmptySet,p,Sat,sat_all,cons_zero,cons_succ,SetLike.mem_coe] using h

theorem Valid.infinity {M : ZFSet.{u}} (hv : Valid M) (hne : ∃ a, a ∈ M) : Infinity M := by
  obtain ⟨a,ha⟩ := hne
  let p := ex (.conj (ex (.conj (.member 0 1) (all (.neg (.member 0 1)))))
    (all (imp (.member 0 1) (ex (.conj (.member 0 2)
      (all (iff (.member 0 1) (disj (.equal 0 2) (.member 0 2)))))))))
  have hp : ∀ e : ℕ → ZFSet.{u}, p.Sat Set.univ e := by
    intro e
    simp only
      [p, Sat, sat_all, sat_iff, sat_imp, sat_disj, cons_zero, cons_succ, Set.mem_univ, true_and,
        forall_const]
    refine ⟨ZFSet.omega,⟨∅,ZFSet.omega_zero,ZFSet.notMem_empty⟩,?_⟩
    intro x hx
    exact ⟨insert x x,ZFSet.omega_succ hx,fun z => ZFSet.mem_insert_iff⟩
  have h := hv p hp (fun _ => a) (fun _ => ha)
  simpa only [Infinity,p,Sat,sat_all,sat_iff,sat_imp,sat_disj,cons_zero,cons_succ,SetLike.mem_coe]
    using h

theorem ambient_choice_graph (a : ZFSet.{u}) (hn : ∀ x ∈ a, ∃ y, y ∈ x) :
    ∃ f : ZFSet.{u}, ChoiceGraph a f := by
  classical
  let pick (x : Conditions a) := Classical.choose (hn (label a x) (label_mem a x))
  have hp (x : Conditions a) : pick x ∈ label a x := Classical.choose_spec (hn _ (label_mem a x))
  let f := ZFSet.range (fun x : Conditions a => ZFSet.pair (label a x) (pick x))
  refine ⟨f,?_,?_⟩
  · intro z hz
    obtain ⟨x,rfl⟩ := ZFSet.mem_range.mp hz
    exact ⟨_,label_mem _ x,_,hp x,rfl⟩
  · intro x hx
    obtain ⟨i,rfl⟩ := label_surjective a hx
    refine ⟨pick i,hp i,ZFSet.mem_range_self i,?_⟩
    intro z _ hz
    obtain ⟨j,hj⟩ := ZFSet.mem_range.mp hz
    obtain ⟨he,hz⟩ := ZFSet.pair_inj.mp hj
    have hj : j = i := label_injective a he
    exact hz.symm.trans (congrArg pick hj)

theorem Valid.choice {M : ZFSet.{u}} (hv : Valid M) (hM : Transitive M) : Choice M := by
  intro a ha hn
  let p := imp (all (imp (.member 0 1) (ex (.member 0 1))))
    (ex (fromBounded (ChoiceCode.graph 1 0)))
  have hp : ∀ e : ℕ → ZFSet.{u}, p.Sat Set.univ e := by
    intro e
    simp only [p,sat_imp,sat_all,Sat,bounded_univ,ChoiceCode.eval_graph,
      cons_zero,cons_succ,Set.mem_univ,true_and,forall_const]
    exact ambient_choice_graph (e 0)
  have h := hv p hp (fun _ => a) (fun _ => ha)
  simp only [p,sat_imp,sat_all,Sat,bounded_sat,cons_zero,cons_succ] at h
  obtain ⟨f,hf,hfg⟩ := h (fun x hx hxa => by
    obtain ⟨y,hy⟩ := hn x hxa
    exact ⟨y,hM x hx y hy,hy⟩)
  refine ⟨f,hf,?_⟩
  have hb := (Formula.absolute (ChoiceCode.graph 1 0) M hM (cons f (fun _ => a))
    (by intro i; cases i <;> assumption)).mp hfg
  exact (ChoiceCode.eval_graph 1 0 _).mp hb

end TuringRigidity.ElementaryModel

end OAI
