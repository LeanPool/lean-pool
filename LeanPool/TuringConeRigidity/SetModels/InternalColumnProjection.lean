/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalColumnProjection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalCountableMap

/-!
# Internal Column Projection
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalColumnProjection
open TransitiveNameModel BoundedSetTheory InternalCountableMap

noncomputable def columns (K S : ZFSet.{0}) : ZFSet.{0} :=
  K.sep (fun x => ∃ n ∈ ZFSet.omega, ZFSet.pair x n ∈ S)

theorem mem_columns (K S x : ZFSet.{0}) :
    x ∈ columns K S ↔ x ∈ K ∧ ∃ n ∈ ZFSet.omega, ZFSet.pair x n ∈ S := ZFSet.mem_sep

theorem columns_mem (M K S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (hS : S ∈ M) : columns K S ∈ M := by
  let e := cons ZFSet.omega (fun _ => S)
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i
    · exact sourceT_omega_mem M hM hT
    · exact hS
  simpa only [columns,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.pairMem 1 0 3)) e he hK

theorem support_subset_columns (K S : ZFSet.{0}) (hS : S ⊆ ZFSet.prod K ZFSet.omega) :
    S ⊆ ZFSet.prod (columns K S) ZFSet.omega := by
  intro z hz
  obtain ⟨x,hx,n,hn,rfl⟩ := ZFSet.mem_prod.mp (hS hz)
  exact ZFSet.pair_mem_prod.mpr ⟨(mem_columns K S x).mpr ⟨hx,n,hn,hz⟩,hn⟩

noncomputable def projection (K S : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod S (columns K S)).sep (fun z => ∃ s ∈ S, ∃ x ∈ columns K S,
    z = ZFSet.pair s x ∧ ∃ n ∈ ZFSet.omega, s = ZFSet.pair x n)

theorem pair_projection (K S s x : ZFSet.{0}) :
    ZFSet.pair s x ∈ projection K S ↔
      s ∈ S ∧ x ∈ columns K S ∧ ∃ n ∈ ZFSet.omega, s = ZFSet.pair x n := by
  simp only [projection,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,s',hs,x',hx,he,hn⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hs,hx,hn⟩
  · rintro ⟨hs,hx,hn⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hs,hx⟩,s,hs,x,hx,rfl,hn⟩

theorem projection_mem (M K S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (hS : S ∈ M) : projection K S ∈ M := by
  have hC := columns_mem M K S hM hT hK hS
  let e := cons S (cons (columns K S) (fun _ => ZFSet.omega))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    · exact hS
    · exact hC
    · exact sourceT_omega_mem M hM hT
  simpa only [projection,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
        (.existsMem 5 (.orderedPair 2 1 0))))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hS hC)

theorem projection_function (K S : ZFSet.{0}) (hS : S ⊆ ZFSet.prod K ZFSet.omega) :
    FunctionGraph S (columns K S) (projection K S) := by
  constructor
  · intro z hz; exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro s hs
    obtain ⟨x,hx,n,hn,he⟩ := ZFSet.mem_prod.mp (hS hs)
    have hxC : x ∈ columns K S := (mem_columns K S x).mpr ⟨hx,n,hn,he ▸ hs⟩
    refine ⟨x,hxC,(pair_projection K S s x).mpr ⟨hs,hxC,n,hn,he⟩,?_⟩
    intro y _ hsy
    obtain ⟨_,_,m,_,hm⟩ := (pair_projection K S s y).mp hsy
    exact (ZFSet.pair_inj.mp (hm.symm.trans he)).1

theorem projection_onto (K S : ZFSet.{0}) :
    ∀ x ∈ columns K S, ∃ s ∈ S, ZFSet.pair s x ∈ projection K S := by
  intro x hx
  obtain ⟨_,n,hn,hs⟩ := (mem_columns K S x).mp hx
  exact ⟨ZFSet.pair x n,hs,(pair_projection K S _ x).mpr ⟨hs,hx,n,hn,rfl⟩⟩

theorem columns_counted (M K S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (hS : S ∈ M) (hsub : S ⊆ ZFSet.prod K ZFSet.omega)
    (hct : S = ∅ ∨ InternallyCountable M S) :
    columns K S ∈ M ∧ columns K S ⊆ K ∧
      S ⊆ ZFSet.prod (columns K S) ZFSet.omega ∧
      (columns K S = ∅ ∨ InternallyCountable M (columns K S)) := by
  refine ⟨columns_mem M K S hM hT hK hS,fun _ h => (mem_columns K S _).mp h |>.1,
    support_subset_columns K S hsub,?_⟩
  rcases hct with he|hc
  · left
    apply ZFSet.ext; intro x
    simp only [columns,he,ZFSet.mem_sep,ZFSet.notMem_empty,and_false,exists_false]
  · right
    exact countable_of_surjection M S (columns K S) (projection K S) hM hT hS
      (columns_mem M K S hM hT hK hS) (projection_mem M K S hM hT hK hS)
      (projection_function K S hsub) (projection_onto K S) hc

end TuringRigidity.InternalColumnProjection

end OAI
