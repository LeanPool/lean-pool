/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/FiniteModelGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelReals

/-!
# Finite Model Graph
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

noncomputable def finiteModelGraph (f : ℕ → ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => {ZFSet.pair (natSet 0) (f 0)}
  | n+1 => finiteModelGraph f n ∪ ({ZFSet.pair (natSet (n+1)) (f (n+1))} : ZFSet.{u})

theorem mem_finiteModelGraph (f : ℕ → ZFSet.{u}) (n : ℕ) (z : ZFSet.{u}) :
    z ∈ finiteModelGraph f n ↔ ∃ i, i ≤ n ∧ z = ZFSet.pair (natSet i) (f i) := by
  induction n with
  | zero =>
    rw [finiteModelGraph,ZFSet.mem_singleton]
    constructor
    · intro h; exact ⟨0,le_rfl,h⟩
    · rintro ⟨i,hi,h⟩
      have he : i = 0 := Nat.eq_zero_of_le_zero hi
      simpa only [he] using h
  | succ n ih =>
    rw [finiteModelGraph,ZFSet.mem_union,ZFSet.mem_singleton,ih]
    constructor
    · rintro (⟨i,hi,hz⟩|hz)
      · exact ⟨i,Nat.le_succ_of_le hi,hz⟩
      · exact ⟨n+1,le_rfl,hz⟩
    · rintro ⟨i,hi,hz⟩
      by_cases hin : i ≤ n
      · exact Or.inl ⟨i,hin,hz⟩
      · have he : i = n+1 := by omega
        exact Or.inr (he ▸ hz)

theorem finiteModelGraph_pair (f : ℕ → ZFSet.{u}) (n i : ℕ) (y : ZFSet.{u}) :
    ZFSet.pair (natSet i) y ∈ finiteModelGraph f n ↔ i ≤ n ∧ y = f i := by
  rw [mem_finiteModelGraph]
  constructor
  · rintro ⟨j,hj,he⟩
    obtain ⟨hij,hy⟩ := ZFSet.pair_inj.mp he
    have heq := natSet_injective hij
    subst j
    exact ⟨hj,hy⟩
  · rintro ⟨hi,rfl⟩
    exact ⟨i,hi,rfl⟩

theorem finiteModelGraph_function (R : ZFSet.{u}) (f : ℕ → ZFSet.{u}) (hf : ∀ i, f i ∈ R) (n : ℕ) :
    TransitiveNameModel.FunctionGraph (natSet (n+1)) R (finiteModelGraph.{u} f n) := by
  constructor
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := (mem_finiteModelGraph f n z).mp hz
    exact ⟨natSet i,(natSet_mem_natSet i (n+1)).mpr (by omega),f i,
      hf i,rfl⟩
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := (mem_natSet (n+1) x).mp hx
    have hin : i ≤ n := by omega
    refine ⟨f i,hf i,
      (finiteModelGraph_pair f n i _).mpr ⟨hin,rfl⟩,?_⟩
    intro y _ hy
    exact ((finiteModelGraph_pair f n i y).mp hy).2

theorem finiteModelGraph_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M)
    (f : ℕ → ZFSet.{u}) (hf : ∀ i, f i ∈ M) (n : ℕ) : finiteModelGraph f n ∈ M := by
  have hn (i : ℕ) : natSet.{u} i ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨i,rfl⟩)
  induction n with
  | zero => exact singleton_mem M hM hP (orderedPair_mem M hM hP (hn 0) (hf 0))
  | succ n ih =>
    exact binary_union_mem M hM hP hU ih
      (singleton_mem M hM hP (orderedPair_mem M hM hP (hn (n+1)) (hf (n+1))))

theorem internal_finite_model_graph_bound (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hω : ZFSet.omega.{u} ∈ M) (R : ZFSet.{u}) (hR : R ∈ M) :
    ∃ Q ∈ M, (∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ ZFSet.prod ZFSet.omega R) ∧
      ∀ f : ℕ → ZFSet.{u}, (∀ i, f i ∈ R) → ∀ n, finiteModelGraph f n ∈ Q := by
  obtain ⟨Q,hQ,hQdef⟩ := internal_power M hM hPow (product_mem M hM hP hU hPow hS hω hR)
  refine ⟨Q,hQ,hQdef,?_⟩
  intro f hf n
  apply (hQdef _).mpr
  refine ⟨finiteModelGraph_mem M hM hP hU hω f (fun i => hM _ hR _ (hf i)) n,?_⟩
  intro z hz
  obtain ⟨i,_,rfl⟩ := (mem_finiteModelGraph f n z).mp hz
  exact ZFSet.mem_prod.mpr ⟨_,(mem_omega _).mpr ⟨i,rfl⟩,_,hf i,rfl⟩

end TuringRigidity.BoundedSetTheory

end OAI
