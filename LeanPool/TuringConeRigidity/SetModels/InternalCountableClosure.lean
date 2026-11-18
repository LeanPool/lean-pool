/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalCountableClosure.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalCountableFamily
public import LeanPool.TuringConeRigidity.SetModels.InternalCountableMap

/-!
# Internal Countable Closure
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCountableClosure
open TransitiveNameModel BoundedSetTheory

theorem constant_graph (A : ZFSet.{0}) :
    orbitGraph (fun _ => A) = ZFSet.prod ZFSet.omega {A} := by
  apply ZFSet.ext; intro z
  rw [mem_orbitGraph,ZFSet.mem_prod]
  constructor
  · rintro ⟨n,rfl⟩
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,A,ZFSet.mem_singleton.mpr rfl,rfl⟩
  · rintro ⟨n,hn,x,hx,rfl⟩
    obtain rfl := ZFSet.mem_singleton.mp hx
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    exact ⟨n,rfl⟩

theorem finite_countable (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hfin : (A : Set ZFSet.{0}).Finite) (hne : ∃ x, x ∈ A) :
    InternallyCountable M A := by
  apply InternalCountableFiniteUnion.internally_countable_union M A hM hT hA (fun _ => A)
    (fun _ => (InternalFiniteSubsets.mem_finiteSubsets_iff A A).mpr ⟨fun _ h => h,hfin⟩)
    _ (fun x hx => ⟨0,hx⟩) hne
  rw [constant_graph]
  exact product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    (sourceT_omega_mem M hM hT) (singleton_mem M hM hT.pairing hA)

theorem singleton_countable (M a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) : InternallyCountable M ({a} : ZFSet.{0}) := by
  apply finite_countable M {a} hM hT (singleton_mem M hM hT.pairing ha)
  · simpa only [ZFSet.coe_singleton] using Set.finite_singleton a
  · exact ⟨a,ZFSet.mem_singleton.mpr rfl⟩

theorem pair_countable (M a b : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) : InternallyCountable M ({a,b} : ZFSet.{0}) := by
  apply finite_countable M {a,b} hM hT (pair_mem M hM hT.pairing ha hb)
  · simpa only [ZFSet.coe_insert,ZFSet.coe_singleton] using (Set.finite_singleton b).insert a
  · exact ⟨a,ZFSet.mem_pair.mpr (Or.inl rfl)⟩

theorem countable_union (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M)
    (hcA : A = ∅ ∨ InternallyCountable M A) (hcB : B = ∅ ∨ InternallyCountable M B) :
    A ∪ B = ∅ ∨ InternallyCountable M (A ∪ B) := by
  have h := InternalCountableFamily.countable_sUnion M {A,B} hM hT
    (pair_mem M hM hT.pairing hA hB) (Or.inr (pair_countable M A B hM hT hA hB))
    (fun E hE => (ZFSet.mem_pair.mp hE).elim (fun h => h ▸ hcA) (fun h => h ▸ hcB))
  simpa only [ZFSet.sUnion_pair] using h

theorem countable_insert (M A a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (ha : a ∈ M) (hcA : A = ∅ ∨ InternallyCountable M A) :
    InternallyCountable M (insert a A) := by
  have he : ({a} : ZFSet.{0}) ∪ A = insert a A := by
    apply ZFSet.ext; intro z
    simp only [ZFSet.mem_union,ZFSet.mem_singleton,ZFSet.mem_insert_iff]
  have h := countable_union M {a} A hM hT (singleton_mem M hM hT.pairing ha) hA
    (Or.inr (singleton_countable M a hM hT ha)) hcA
  rw [he] at h
  rcases h with h|h
  · exact False.elim (ZFSet.notMem_empty a (h ▸ ZFSet.mem_insert a A))
  · exact h

/-- The relation fixing members of `A` that belong to `B` and relating other members of `A` to
`d` when `d` belongs to `B`. -/
noncomputable def retractGraph (A B d : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod A B).sep (fun z => ∃ x ∈ A, ∃ y ∈ B,
    z = ZFSet.pair x y ∧ ((x ∈ B ∧ y = x) ∨ (x ∉ B ∧ y = d)))

theorem pair_retractGraph (A B d x y : ZFSet.{0}) :
    ZFSet.pair x y ∈ retractGraph A B d ↔
      x ∈ A ∧ y ∈ B ∧ ((x ∈ B ∧ y = x) ∨ (x ∉ B ∧ y = d)) := by
  simp only [retractGraph,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x',hx,y',hy,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hx,hy,h⟩
  · rintro ⟨hx,hy,h⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hx,hy⟩,x,hx,y,hy,rfl,h⟩

theorem retractGraph_mem (M A B d : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hd : d ∈ M) : retractGraph A B d ∈ M := by
  let e := cons A (cons B (fun _ => d))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    · exact hA
    · exact hB
    · exact hd
  simpa only [retractGraph,Formula.Eval,Formula.eval_orderedPair,Formula.eval_disj,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
        (.disj (.conj (.member 1 4) (.equal 0 1))
          (.conj (.neg (.member 1 4)) (.equal 0 5)))))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hA hB)

theorem retractGraph_function (A B d : ZFSet.{0}) (hd : d ∈ B) :
    FunctionGraph A B (retractGraph A B d) := by
  classical
  constructor
  · intro z hz; exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro x hx
    by_cases hxB : x ∈ B
    · refine ⟨x,hxB,(pair_retractGraph A B d x x).mpr ⟨hx,hxB,Or.inl ⟨hxB,rfl⟩⟩,?_⟩
      intro y _ hy
      exact ((pair_retractGraph A B d x y).mp hy).2.2.elim And.right
        (fun h => False.elim (h.1 hxB))
    · refine ⟨d,hd,(pair_retractGraph A B d x d).mpr ⟨hx,hd,Or.inr ⟨hxB,rfl⟩⟩,?_⟩
      intro y _ hy
      exact ((pair_retractGraph A B d x y).mp hy).2.2.elim
        (fun h => False.elim (hxB h.1)) And.right

theorem countable_subset (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hsub : B ⊆ A)
    (hct : InternallyCountable M A) (hne : ∃ d, d ∈ B) : InternallyCountable M B := by
  obtain ⟨d,hd⟩ := hne
  apply InternalCountableMap.countable_of_surjection M A B (retractGraph A B d) hM hT hA hB
    (retractGraph_mem M A B d hM hT hA hB (hM B hB d hd)) (retractGraph_function A B d hd) _ hct
  intro y hy
  exact ⟨y,hsub hy,(pair_retractGraph A B d y y).mpr ⟨hsub hy,hy,Or.inl ⟨hy,rfl⟩⟩⟩

end TuringRigidity.InternalCountableClosure

end OAI
