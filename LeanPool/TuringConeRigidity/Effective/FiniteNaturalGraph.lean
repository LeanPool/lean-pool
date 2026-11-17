/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteNaturalGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelNaturalNumbers

/-!
# Finite Natural Graph
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

noncomputable def finiteNaturalGraph (f : ℕ → ℕ) : ℕ → ZFSet.{u}
  | 0 => {ZFSet.pair (natSet 0) (natSet (f 0))}
  | n+1 => finiteNaturalGraph f n ∪ ({ZFSet.pair (natSet (n+1)) (natSet (f (n+1)))} : ZFSet.{u})

theorem mem_finiteNaturalGraph (f : ℕ → ℕ) (n : ℕ) (z : ZFSet.{u}) :
    z ∈ finiteNaturalGraph f n ↔ ∃ i, i ≤ n ∧ z = ZFSet.pair (natSet i) (natSet (f i)) := by
  induction n with
  | zero =>
    rw [finiteNaturalGraph,ZFSet.mem_singleton]
    constructor
    · intro h; exact ⟨0,le_rfl,h⟩
    · rintro ⟨i,hi,h⟩
      have he : i = 0 := Nat.eq_zero_of_le_zero hi
      simpa only [he] using h
  | succ n ih =>
    rw [finiteNaturalGraph,ZFSet.mem_union,ZFSet.mem_singleton,ih]
    constructor
    · rintro (⟨i,hi,hz⟩|hz)
      · exact ⟨i,Nat.le_succ_of_le hi,hz⟩
      · exact ⟨n+1,le_rfl,hz⟩
    · rintro ⟨i,hi,hz⟩
      by_cases hin : i ≤ n
      · exact Or.inl ⟨i,hin,hz⟩
      · have he : i = n+1 := by omega
        exact Or.inr (he ▸ hz)

theorem finiteNaturalGraph_pair (f : ℕ → ℕ) (n i : ℕ) (y : ZFSet.{u}) :
    ZFSet.pair (natSet i) y ∈ finiteNaturalGraph f n ↔ i ≤ n ∧ y = natSet (f i) := by
  rw [mem_finiteNaturalGraph]
  constructor
  · rintro ⟨j,hj,he⟩
    obtain ⟨hij,hy⟩ := ZFSet.pair_inj.mp he
    have heq := natSet_injective hij
    subst j
    exact ⟨hj,hy⟩
  · rintro ⟨hi,rfl⟩
    exact ⟨i,hi,rfl⟩

theorem finiteNaturalGraph_function (f : ℕ → ℕ) (n : ℕ) :
    TransitiveNameModel.FunctionGraph (natSet (n+1)) ZFSet.omega (finiteNaturalGraph.{u} f n) := by
  constructor
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := (mem_finiteNaturalGraph f n z).mp hz
    exact ⟨natSet i,(natSet_mem_natSet i (n+1)).mpr (by omega),natSet (f i),
      (mem_omega _).mpr ⟨f i,rfl⟩,rfl⟩
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := (mem_natSet (n+1) x).mp hx
    have hin : i ≤ n := by omega
    refine ⟨natSet (f i),(mem_omega _).mpr ⟨f i,rfl⟩,
      (finiteNaturalGraph_pair f n i _).mpr ⟨hin,rfl⟩,?_⟩
    intro y _ hy
    exact ((finiteNaturalGraph_pair f n i y).mp hy).2

theorem finiteNaturalGraph_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M)
    (f : ℕ → ℕ) (n : ℕ) : finiteNaturalGraph f n ∈ M := by
  have hn (i : ℕ) : natSet.{u} i ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨i,rfl⟩)
  induction n with
  | zero => exact singleton_mem M hM hP (orderedPair_mem M hM hP (hn 0) (hn (f 0)))
  | succ n ih =>
    exact binary_union_mem M hM hP hU ih
      (singleton_mem M hM hP (orderedPair_mem M hM hP (hn (n+1)) (hn (f (n+1)))))

theorem internal_finite_natural_graph_bound (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hω : ZFSet.omega.{u} ∈ M) :
    ∃ Q ∈ M, (∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ ZFSet.prod ZFSet.omega ZFSet.omega) ∧
      ∀ f : ℕ → ℕ, ∀ n, finiteNaturalGraph f n ∈ Q := by
  obtain ⟨Q,hQ,hQdef⟩ := internal_power M hM hPow (product_mem M hM hP hU hPow hS hω hω)
  refine ⟨Q,hQ,hQdef,?_⟩
  intro f n
  apply (hQdef _).mpr
  refine ⟨finiteNaturalGraph_mem M hM hP hU hω f n,?_⟩
  intro z hz
  obtain ⟨i,_,rfl⟩ := (mem_finiteNaturalGraph f n z).mp hz
  exact ZFSet.mem_prod.mpr ⟨_,(mem_omega _).mpr ⟨i,rfl⟩,_,(mem_omega _).mpr ⟨f i,rfl⟩,rfl⟩

end TuringRigidity.BoundedSetTheory

end OAI
