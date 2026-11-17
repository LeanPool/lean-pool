/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/TuplePrefixSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.ConstructibleTupleSpace

/-!
# Tuple Prefix Syntax
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

def PrefixGraphs (A n g m h x : ZFSet.{u}) : Prop :=
  m = insert n n ∧ FunctionGraph m A h ∧ ZFSet.pair (natSet 0) x ∈ h ∧
    ∀ i ∈ n, ∃ j ∈ m, j = insert i i ∧
      ∀ y ∈ A, ZFSet.pair i y ∈ g → ZFSet.pair j y ∈ h

theorem prefixGraphs_spec (A g m h x : ZFSet.{u}) {n : ℕ}
    (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) (hx : x ∈ A)
    (hg : g = tupleGraph v) :
    PrefixGraphs A (natSet n) g m h x ↔
      m = natSet (n+1) ∧ h = tupleGraph (Fin.cases (motive := fun _ => ZFSet.{u}) x v) := by
  subst g
  constructor
  · rintro ⟨rfl,hh,hzero,hshift⟩
    have hn : insert (natSet.{u} n) (natSet n) = natSet (n+1) := rfl
    rw [hn] at hh
    obtain ⟨w,hw,rfl⟩ := functionGraph_tuple A h (n+1) hh
    have hwv : w = Fin.cases (motive := fun _ => ZFSet.{u}) x v := by
      funext i
      refine Fin.cases ?_ (fun k => ?_) i
      · exact ((tupleGraph_pair w 0 x).mp hzero).symm
      · obtain ⟨j,_,hj,ht⟩ := hshift (natSet k.val) ((natSet_mem_natSet _ _).mpr k.isLt)
        have hpair := ht (v k) (hv k) ((tupleGraph_pair v k _).mpr rfl)
        rw [hj] at hpair
        exact ((tupleGraph_pair w k.succ (v k)).mp hpair).symm
    rw [hwv]
    exact ⟨rfl,rfl⟩
  · rintro ⟨hm,hh⟩
    rw [hm,hh]
    unfold PrefixGraphs
    refine ⟨rfl,?_,?_,?_⟩
    · apply tupleGraph_function
      intro i
      exact Fin.cases hx hv i
    · change ZFSet.pair (natSet 0) x ∈ ZFSet.range
        (fun i : Fin (n+1) => ZFSet.pair (natSet i.val) ((Fin.cases (motive := fun _ => ZFSet.{u})
          x v : Fin (n+1) → ZFSet.{u}) i))
      exact ZFSet.mem_range_self
        (f := fun i : Fin (n+1) => ZFSet.pair (natSet i.val)
          (Fin.cases (motive := fun _ => ZFSet.{u}) x v i))
        (⟨0,Nat.zero_lt_succ n⟩ : Fin (n+1))
    · intro i hi
      obtain ⟨k,hk,rfl⟩ := (mem_natSet n i).mp hi
      refine ⟨natSet (k+1),(natSet_mem_natSet _ _).mpr (Nat.succ_lt_succ hk),rfl,?_⟩
      intro y _ hy
      have he := (tupleGraph_pair v ⟨k,hk⟩ y).mp hy
      exact (tupleGraph_pair (Fin.cases (motive := fun _ => ZFSet.{u}) x v) (Fin.succ ⟨k,hk⟩)
        y).mpr he

def prefixGraphsFormula (A n g m h x z : ℕ) : Formula :=
  .conj (.successor m n) (.conj (.functionGraph h m A)
    (.conj (.pairMem z x h)
      (.allMem n (.existsMem (m+1) (.conj (.successor 0 1)
        (.allMem (A+2) (.imp (.pairMem 2 0 (g+3)) (.pairMem 1 0 (h+3)))))))))

theorem prefixGraphsFormula_spec (A n g m h x z : ℕ) (e : ℕ → ZFSet.{u})
    (hz : e z = natSet 0) :
    (prefixGraphsFormula A n g m h x z).Eval e ↔
      PrefixGraphs (e A) (e n) (e g) (e m) (e h) (e x) := by
  simp only [prefixGraphsFormula,Formula.Eval,Formula.eval_successor,Formula.eval_functionGraph,
Formula.eval_pairMem, Formula.eval_allMem, Formula.eval_imp, cons_zero, cons_succ, hz,
  PrefixGraphs, FunctionGraph]

def tuplePrefixFormula (A o Q t x u z : ℕ) : Formula :=
  .existsMem o (.existsMem (Q+1) (.existsMem (o+2) (.existsMem (Q+3)
    (.conj (.orderedPair (t+4) 3 2) (.conj (.orderedPair (u+4) 1 0)
      (prefixGraphsFormula (A+4) 3 2 1 0 (x+4) (z+4)))))))

theorem tuplePrefixFormula_spec (A o Q t x u z : ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hz : e z = natSet 0)
    (hQ : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ e A) → tupleGraph v ∈ e Q)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ e A)
    (ht : e t = tupleCode v) (hx : e x ∈ e A) :
    (tuplePrefixFormula A o Q t x u z).Eval e ↔ e u = tupleCode (Fin.cases (motive := fun _ =>
      ZFSet.{u}) (e x) v) := by
  simp only [tuplePrefixFormula,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ]
  simp only [prefixGraphsFormula,Formula.Eval,Formula.eval_successor,Formula.eval_functionGraph,
    Formula.eval_pairMem,Formula.eval_allMem,Formula.eval_imp,cons_zero,cons_succ,hz]
  change (∃ n' ∈ e o, ∃ g ∈ e Q, ∃ m ∈ e o, ∃ h ∈ e Q,
    e t = ZFSet.pair n' g ∧ e u = ZFSet.pair m h ∧ PrefixGraphs (e A) n' g m h (e x)) ↔ _
  rw [ho]
  constructor
  · rintro ⟨n',_,g,_,m,_,h,_,ht',hu,hp⟩
    have he := ZFSet.pair_inj.mp (ht.symm.trans ht')
    have hn : n' = natSet n := he.1.symm
    have hg : g = tupleGraph v := he.2.symm
    rw [hn] at hp
    obtain ⟨hm,hh⟩ := (prefixGraphs_spec (e A) g m h (e x) v hv hx hg).mp hp
    rw [hu,hm,hh]; rfl
  · intro hu
    refine ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,tupleGraph v,hQ n v hv,
      natSet (n+1),(mem_omega _).mpr ⟨n+1,rfl⟩,tupleGraph (Fin.cases (motive := fun _ =>
        ZFSet.{u}) (e x) v),
      hQ (n+1) _ (fun i => Fin.cases hx hv i),ht,hu,?_⟩
    exact (prefixGraphs_spec (e A) _ _ _ _ v hv hx rfl).mpr ⟨rfl,rfl⟩

end TuringRigidity.RelativeConstructible

end OAI
