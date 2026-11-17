/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SigmaSequenceTrace.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaPowerDefinability
public import LeanPool.TuringConeRigidity.Syntax.SigmaParameterizedClosure
public import LeanPool.TuringConeRigidity.SetModels.SetModelIteration

/-!
# Sigma Sequence Trace
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel BoundedDefinability SetModelFunctions SetModelIteration
  RelativeConstructible
universe u

def SequenceTrace (M : ZFSet.{u}) (S : ZFSet.{u} → ZFSet.{u} → Prop)
    (n x y d r f z : ZFSet.{u}) : Prop :=
  d = insert n n ∧ FunctionGraph d r f ∧ z = ∅ ∧
    ZFSet.pair z x ∈ f ∧ ZFSet.pair n y ∈ f ∧
    ∀ i ∈ n, ∃ j ∈ M, j = insert i i ∧ ∀ v ∈ r, ∀ w ∈ r,
      (ZFSet.pair i v ∈ f ∧ ZFSet.pair j w ∈ f) → S v w

theorem sequenceTrace_sigma (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (S : ZFSet.{u} → ZFSet.{u} → Prop)
    (hS : SigmaDefinable M (fun e => S (e 1) (e 0))) :
    SigmaDefinable M (fun e => SequenceTrace M S (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6)) := by
  let C : Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hcore : Definable M (fun e => e 3 = insert (e 0) (e 0) ∧ FunctionGraph (e 3) (e 4) (e 5) ∧
      e 6 = ∅ ∧ ZFSet.pair (e 6) (e 1) ∈ e 5 ∧ ZFSet.pair (e 0) (e 2) ∈ e 5) := by
    refine ⟨.conj (.successor 6 0) (.conj (.functionGraph 10 6 8)
      (.conj (.empty 12) (.conj (.pairMem 12 2 10) (.pairMem 0 4 10)))),
      fun _ => ZFSet.omega,fun _ => C.omega_mem,?_⟩
    intro e
    simp [Formula.Eval,Formula.eval_successor,Formula.eval_functionGraph,
      Formula.eval_empty,Formula.eval_pairMem,mix,FunctionGraph]
  have hAnte : Definable M (fun e => ZFSet.pair (e 3) (e 1) ∈ e 9 ∧
      ZFSet.pair (e 2) (e 0) ∈ e 9) := by
    refine ⟨.conj (.pairMem 6 2 18) (.pairMem 4 0 18),
      fun _ => ZFSet.omega,fun _ => C.omega_mem,?_⟩
    intro e; simp [Formula.Eval,Formula.eval_pairMem,mix]
  have himp := SigmaDefinable.impBounded C hAnte hS
  have hall := (himp.allMem hM hT 7).allMem hM hT 6
  have hsucc : Definable M (fun e => e 0 = insert (e 1) (e 1)) := by
    refine ⟨.successor 0 2,fun _ => ZFSet.omega,fun _ => C.omega_mem,?_⟩
    intro e; simp [Formula.eval_successor,mix]
  have hstep := (((hsucc.toSigma hM).and hall).existsSet).allMem hM hT 0
  exact ((hcore.toSigma hM).and hstep).congr (fun _ _ => by
    simp only [SequenceTrace,cons_zero,cons_succ,and_assoc])

theorem SequenceTrace.correct (M : ZFSet.{u}) (S : ZFSet.{u} → ZFSet.{u} → Prop)
    (s : ℕ → ZFSet.{u}) (hS : ∀ i w, S (s i) w → w = s (i + 1))
    (n : ℕ) {y d r f z : ZFSet.{u}}
    (h : SequenceTrace M S (natSet n) (s 0) y d r f z) : y = s n := by
  obtain ⟨rfl,hfun,rfl,hzero,hy,hstep⟩ := h
  have hd : insert (natSet.{u} n) (natSet n) = natSet (n+1) := rfl
  rw [hd] at hfun
  have computes (i : ℕ) (hi : i ≤ n) : ZFSet.pair (natSet i) (s i) ∈ f := by
    induction i with
    | zero => exact hzero
    | succ i ih =>
      have hip := ih (by omega)
      have hiv : s i ∈ r := by
        obtain ⟨x,_,v,hv,heq⟩ := hfun.1 _ hip
        obtain ⟨_,rfl⟩ := ZFSet.pair_inj.mp heq
        exact hv
      have hjd : natSet.{u} (i+1) ∈ natSet (n+1) := (natSet_mem_natSet _ _).mpr (by omega)
      obtain ⟨w,hw,hjw,_⟩ := hfun.2 _ hjd
      obtain ⟨j,_,hj,hs⟩ := hstep (natSet i) ((natSet_mem_natSet _ _).mpr (by omega))
      have hj' : j = natSet (i+1) := hj
      have hs' := hs (s i) hiv w hw ⟨hip,hj' ▸ hjw⟩
      exact (hS i w hs') ▸ hjw
  exact hfun.functional ((natSet_mem_natSet _ _).mpr (Nat.lt_succ_self n)) hy (computes n le_rfl)

theorem sequenceTrace_exists (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (S : ZFSet.{u} → ZFSet.{u} → Prop) (s : ℕ → ZFSet.{u})
    (hs : ∀ i, s i ∈ M) (hstep : ∀ i, S (s i) (s (i + 1))) (n : ℕ) :
    ∃ z ∈ M, ∃ f ∈ M, ∃ r ∈ M, ∃ d ∈ M, SequenceTrace M S (natSet n) (s 0) (s n) d r f z := by
  let C : Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  let f := finiteGraph (n+1) s
  have hf : f ∈ M := finiteGraph_mem M hM hT.pairing hT.union C.omega_mem _ s (fun i _ => hs i)
  let r := iterUnion 2 f
  have hr := iterUnion_mem M hM hT.union hf 2
  have hval (i : ℕ) (hi : i < n+1) : s i ∈ r :=
    second_mem_doubleUnion ((pair_mem_finiteGraph _ _ _ _).mpr ⟨hi,rfl⟩)
  have hfun : FunctionGraph (natSet (n+1)) r f := by
    constructor
    · intro z hz
      obtain ⟨i,hi,rfl⟩ := (mem_finiteGraph _ _ _).mp hz
      exact ⟨natSet i,(natSet_mem_natSet _ _).mpr hi,s i,hval i hi,rfl⟩
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := (mem_natSet (n+1) x).mp hx
      refine ⟨s i,hval i hi,(pair_mem_finiteGraph _ _ _ _).mpr ⟨hi,rfl⟩,?_⟩
      intro y _ hy
      exact ((pair_mem_finiteGraph _ _ _ _).mp hy).2
  refine ⟨∅,C.nat_mem 0,f,hf,r,hr,natSet (n+1),C.nat_mem _,rfl,hfun,rfl,
    (pair_mem_finiteGraph _ _ _ _).mpr ⟨by omega,rfl⟩,
    (pair_mem_finiteGraph _ _ _ _).mpr ⟨by omega,rfl⟩,?_⟩
  intro i hi
  obtain ⟨i,hi,rfl⟩ := (mem_natSet n i).mp hi
  refine ⟨natSet (i+1),C.nat_mem _,rfl,?_⟩
  intro v _ w _ hp
  rw [((pair_mem_finiteGraph _ _ _ _).mp hp.1).2,
    ((pair_mem_finiteGraph _ _ _ _).mp hp.2).2]
  exact hstep i

end TuringRigidity.BoundedSetTheory

end OAI
