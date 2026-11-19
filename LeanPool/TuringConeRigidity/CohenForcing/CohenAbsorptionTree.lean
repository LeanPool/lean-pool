/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenAbsorptionTree.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalRegularTree
public import LeanPool.TuringConeRigidity.SetModels.InternalRegularSplitter

/-!
# Cohen Absorption Tree
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenAbsorptionTree
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalProjectedGeneric RegularBinaryTree RegularDecisionPartition

theorem top_code (c : ZFSet.{0}) : IsCode c c := by
  refine ⟨(fun _ h => h),ZFSet.ext (fun p => ?_)⟩
  rw [mem_regular]
  exact ⟨And.left,fun hp => ⟨hp,fun q hq _ => ⟨q,hq,fun _ h => h⟩⟩⟩

theorem internal_dense_tree (M q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hq : q ∈ M) (hct : InternallyCountable M q) :
    ∃ c ∈ M,
      (∀ z, z ∈ c ↔ ∃ p ∈ q, ∃ s ∈ CohenGroundPoset.conditions ZFSet.omega,
        z = TaggedProductConditions.code p s) ∧
      InternalCollapse.orderSet c ∈ M ∧ InternallyCountable M c ∧
      ∃ B ∈ M, (∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U) ∧
        ∃ T ∈ M, ∃ E : ℕ → ZFSet.{0}, orbitGraph E ∈ M ∧
          ∃ A ∈ M, FunctionGraph InternalCohen.conditions (positive B) A ∧
            (∀ (s : List Bool) U,
              ZFSet.pair (InternalCohen.wordCode s) U ∈ A ↔ U = tree c B T E s) ∧
            (∀ s : List Bool, tree c B T E s ∈ positive B) ∧
            (∀ s : List Bool, Refines c (tree c B T E s) (E s.length)
              (tree c B T E (s ++ [false])) (tree c B T E (s ++ [true]))) ∧
            (∀ s t : List Bool, s <+: t → tree c B T E t ⊆ tree c B T E s) ∧
            (∀ s u v : List Bool, ∀ p ∈ tree c B T E (s ++ [false] ++ u),
              p ∉ tree c B T E (s ++ [true] ++ v)) ∧
            (∀ D, IsCode c D → D ≠ ∅ → ∃ s : List Bool, tree c B T E s ⊆ D) := by
  obtain ⟨c,hc,hcs,hco,hcc,B,hBM,hB,S,hSM,hSc,hSP,hSs,hSd,T,hTM,hTf,hTs⟩ :=
    InternalRegularSplitter.counted_cohen_presentation M q hM hT hq hct
  have hc0 : c ≠ ∅ := by
    obtain ⟨g,_,hg,_⟩ := hcc
    obtain ⟨p,hp,_,_⟩ := hg.2 (natSet 0) ((mem_omega _).mpr ⟨0,rfl⟩)
    exact fun he => ZFSet.notMem_empty p (he ▸ hp)
  have hcP : c ∈ positive B := ZFSet.mem_sep.mpr ⟨(hB c).mpr ⟨hc,top_code c⟩,hc0⟩
  obtain ⟨g,hgM,hgf,hgo⟩ := hSc
  obtain ⟨E,hES,hEg⟩ := InternalCountableFamily.sequence_of_graph S g hgf
  have hE : ∀ n, E n ∈ B := fun n => (ZFSet.mem_sep.mp (hSP (hES n))).1
  have hEM : orbitGraph E ∈ M := hEg.symm ▸ hgM
  have hDense : ∀ D, IsCode c D → D ≠ ∅ → ∃ n, E n ≠ ∅ ∧ E n ⊆ D := by
    intro D hD hD0
    obtain ⟨V,hV,hVD⟩ := hSd D hD hD0
    obtain ⟨n,hn,hnV⟩ := hgo V hV
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    have hVE : V = E n := (orbitGraph_pair E n V).mp (hEg.symm ▸ hnV)
    exact ⟨n,(ZFSet.mem_sep.mp (hSP (hES n))).2,hVE ▸ hVD⟩
  obtain ⟨A,hAM,hAf,hAs⟩ := InternalRegularTree.tree_graph_internal M c B T E
    hM hT hBM hTM hcP hTf hE hEM
  refine ⟨c,hc,hcs,hco,hcc,B,hBM,hB,T,hTM,E,hEM,A,hAM,hAf,hAs,
    tree_positive c B T E hcP hTf hE,
    tree_refines c B T E hcP hTf hE hTs,
    tree_prefix c B T E hcP hTf hE hTs,
    tree_incompatible c B T E hcP hTf hE hTs,?_⟩
  exact tree_dense c B T E hcP hTf hE (fun U hU => ((hB U).mp hU).2) hTs hDense

end TuringRigidity.CohenAbsorptionTree

end OAI
