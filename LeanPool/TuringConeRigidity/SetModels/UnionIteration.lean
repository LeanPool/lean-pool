/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/UnionIteration.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalInfinity
public import LeanPool.TuringConeRigidity.Syntax.CheckGraphConstruction

/-!
# Union Iteration
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open BoundedSetTheory
universe u

/-- A set-coded total single-valued function graph from `d` to `r`. -/
def FunctionGraph (d r f : ZFSet.{u}) : Prop :=
  (∀ z ∈ f, ∃ x ∈ d, ∃ y ∈ r, z = ZFSet.pair x y) ∧
  (∀ x ∈ d, ∃ y ∈ r, ZFSet.pair x y ∈ f ∧
    ∀ z ∈ r, ZFSet.pair x z ∈ f → z = y)

theorem FunctionGraph.value_mem {d r f x y : ZFSet.{u}}
    (h : FunctionGraph d r f) (hp : ZFSet.pair x y ∈ f) : y ∈ r := by
  obtain ⟨a,_,b,hb,he⟩ := h.1 _ hp
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  exact hb

theorem FunctionGraph.functional {d r f x y z : ZFSet.{u}}
    (h : FunctionGraph d r f) (hx : x ∈ d)
    (hy : ZFSet.pair x y ∈ f) (hz : ZFSet.pair x z ∈ f) : y = z := by
  obtain ⟨v,_,_,hu⟩ := h.2 x hx
  exact (hu y (h.value_mem hy) hy).trans (hu z (h.value_mem hz) hz).symm

/-- A function graph starting at `a` and following the set-union operation at successor
indices. -/
def UnionIteration (k r f a : ZFSet.{u}) : Prop := FunctionGraph k r f ∧
  ZFSet.pair ∅ a ∈ f ∧
  ∀ i ∈ k, ∀ j ∈ k, j = insert i i → ∀ v ∈ r, ∀ w ∈ r,
    ZFSet.pair i v ∈ f → ZFSet.pair j w ∈ f → w = ZFSet.sUnion v

theorem UnionIteration.correct {n : ℕ} {r f a : ZFSet.{u}}
    (h : UnionIteration (natSet (n + 1)) r f a) (i : ℕ) (hi : i ≤ n)
    (v : ZFSet.{u}) (hv : ZFSet.pair (natSet i) v ∈ f) : v = iterUnion i a := by
  induction i generalizing v with
  | zero => exact h.1.functional ((natSet_mem_natSet 0 (n+1)).mpr (Nat.zero_lt_succ n)) hv h.2.1
  | succ i ih =>
    have hik := (natSet_mem_natSet i (n+1)).mpr (Nat.lt_succ_of_le (Nat.le_of_succ_le hi))
    have hjk := (natSet_mem_natSet (i+1) (n+1)).mpr (Nat.lt_succ_of_le hi)
    obtain ⟨w,hw,hfw,_⟩ := h.1.2 _ hik
    have he := h.2.2 _ hik _ hjk rfl w hw v (h.1.value_mem hv) hfw hv
    rw [ih (Nat.le_of_succ_le hi) w hfw] at he
    exact he

/-- The graph of the first `n + 1` iterated unions of `a`. -/
noncomputable def unionGraph (a : ZFSet.{u}) (n : ℕ) : ZFSet.{u} :=
  ZFSet.range (fun i : Fin (n+1) => ZFSet.pair (natSet i.val) (iterUnion i.val a))

theorem mem_unionGraph (a z : ZFSet.{u}) (n : ℕ) :
    z ∈ unionGraph a n ↔ ∃ i ≤ n, z = ZFSet.pair (natSet i) (iterUnion i a) := by
  rw [unionGraph,ZFSet.mem_range]
  exact ⟨fun ⟨i,hi⟩ => ⟨i.val,Nat.le_of_lt_succ i.isLt,hi.symm⟩,
    fun ⟨i,hi,hz⟩ => ⟨⟨i,Nat.lt_succ_of_le hi⟩,hz.symm⟩⟩

theorem unionGraph_pair (a x v : ZFSet.{u}) (n : ℕ) :
    ZFSet.pair x v ∈ unionGraph a n ↔ ∃ i ≤ n, x = natSet i ∧ v = iterUnion i a := by
  rw [mem_unionGraph]
  exact exists_congr (fun i => and_congr_right (fun _ => ZFSet.pair_inj))

theorem unionGraph_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M)
    {a : ZFSet.{u}} (ha : a ∈ M) (n : ℕ) : unionGraph a n ∈ M := by
  have hn (n : ℕ) : natSet.{u} n ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
  induction n with
  | zero =>
    have he : unionGraph a 0 = ({ZFSet.pair (natSet 0) a} : ZFSet.{u}) := by
      apply ZFSet.ext; intro z
      simp only [mem_unionGraph,Nat.le_zero_eq,ZFSet.mem_singleton]
      simp only [exists_eq_left,iterUnion]
    rw [he]
    exact singleton_mem M hM hP (orderedPair_mem M hM hP (hn 0) ha)
  | succ n ih =>
    have he : unionGraph a (n+1) = unionGraph a n ∪
        ({ZFSet.pair (natSet (n+1)) (iterUnion (n+1) a)} : ZFSet.{u}) := by
      apply ZFSet.ext; intro z
      rw [mem_unionGraph,ZFSet.mem_union,mem_unionGraph,ZFSet.mem_singleton]
      constructor
      · rintro ⟨i,hi,hz⟩
        rcases Nat.lt_or_eq_of_le hi with hi|rfl
        · exact Or.inl ⟨i,Nat.le_of_lt_succ hi,hz⟩
        · exact Or.inr hz
      · rintro (⟨i,hi,hz⟩|hz)
        · exact ⟨i,Nat.le.step hi,hz⟩
        · exact ⟨n+1,le_refl _,hz⟩
    rw [he]
    exact binary_union_mem M hM hP hU ih
      (singleton_mem M hM hP (orderedPair_mem M hM hP (hn (n+1))
        (iterUnion_mem M hM hU ha (n+1))))

theorem unionGraph_valid (a : ZFSet.{u}) (n : ℕ) :
    UnionIteration (natSet (n+1)) (iterUnion 2 (unionGraph a n)) (unionGraph a n) a := by
  have hpair (i : ℕ) (hi : i ≤ n) :
      ZFSet.pair (natSet i) (iterUnion i a) ∈ unionGraph a n :=
    (unionGraph_pair a _ _ n).mpr ⟨i,hi,rfl,rfl⟩
  refine ⟨⟨?_,?_⟩,hpair 0 (Nat.zero_le n),?_⟩
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := (mem_unionGraph a z n).mp hz
    exact ⟨_,(natSet_mem_natSet i (n+1)).mpr (Nat.lt_succ_of_le hi),_,second_mem_doubleUnion hz,rfl⟩
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := (mem_natSet (n+1) x).mp hx
    have hp := hpair i (Nat.le_of_lt_succ hi)
    refine ⟨_,second_mem_doubleUnion hp,hp,?_⟩
    intro v _ hv
    obtain ⟨j,_,he,hv⟩ := (unionGraph_pair a _ v n).mp hv
    obtain rfl := natSet_injective he
    exact hv
  · intro x _ y _ hxy v _ w _ hxv hyw
    obtain ⟨i,_,rfl,rfl⟩ := (unionGraph_pair a x v n).mp hxv
    obtain ⟨j,_,rfl,rfl⟩ := (unionGraph_pair a y w n).mp hyw
    have he : j = i+1 := natSet_injective hxy
    rw [he]; rfl

namespace IterationFormula
open Formula

/-- Bounded formula asserting that `b` is exactly the union of `a`. -/
def unionOf (b a : ℕ) : Formula := .conj
  (allMem b (.existsMem (a+1) (.member 1 0)))
  (allMem a (allMem 0 (.member 0 (b+2))))

@[simp] theorem eval_unionOf (b a : ℕ) (e : ℕ → ZFSet.{u}) :
    (unionOf b a).Eval e ↔ e b = ZFSet.sUnion (e a) := by
  simp only [unionOf,Formula.Eval,eval_allMem,cons_zero,cons_succ]
  constructor
  · rintro ⟨hf,hb⟩
    apply ZFSet.ext; intro z; rw [ZFSet.mem_sUnion]
    exact ⟨hf z,fun ⟨y,hy,hz⟩ => hb y hy z hz⟩
  · intro h; rw [h]
    exact ⟨fun z hz => ZFSet.mem_sUnion.mp hz,
      fun y hy z hz => ZFSet.mem_sUnion.mpr ⟨y,hy,hz⟩⟩

/-- Bounded formula expressing a function trace of iterated union from the initial value. -/
def iteration (k r f a e : ℕ) : Formula := .conj (functionGraph f k r)
  (.conj (pairMem e a f)
    (allMem k (allMem (k+1) (imp (successor 0 1)
      (allMem (r+2) (allMem (r+3)
        (imp (.conj (pairMem 3 1 (f+4)) (pairMem 2 0 (f+4))) (unionOf 0 1))))))))

theorem eval_iteration (k r f a e : ℕ) (env : ℕ → ZFSet.{u}) (he : env e = ∅) :
    (iteration k r f a e).Eval env ↔ UnionIteration (env k) (env r) (env f) (env a) := by
  simp only [iteration,Formula.Eval,eval_functionGraph,eval_pairMem,
    eval_allMem,eval_imp,eval_successor,eval_unionOf,cons_zero,cons_succ,
    UnionIteration,FunctionGraph,he,and_imp]
end IterationFormula

end TuringRigidity.TransitiveNameModel

end OAI
