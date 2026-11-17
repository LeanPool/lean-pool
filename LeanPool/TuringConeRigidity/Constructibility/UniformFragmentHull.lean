/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformFragmentHull.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.GeneratedHull

/-!
# Uniform Fragment Hull
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u
namespace FiniteTuple

theorem uniform_internal_fragment_hull (M t : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M)
    (ht : t ∈ M) (h0t : (∅ : ZFSet.{u}) ∈ t) :
    ∃ K ∈ M, ∀ xs : List ZFSet.{u}, (∀ x ∈ xs, x ∈ M) →
      ∀ d ∈ M, Transitive d → (t ∪ elements xs) ⊆ d → ∀ φ : Formula,
        ∃ h ∈ M, (t ∪ elements xs) ⊆ h ∧ h ⊆ d ∧ StructureExtensional h ∧
          (∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ h) → (φ.Realize h e ↔ φ.Realize d e)) ∧
          ∃ f ∈ M, ∃ j : ZFSet.{u} → ZFSet.{u}, Presents h f j ∧
            (∀ x ∈ h, j x ∈ K) ∧ (∀ x ∈ h, ∀ y ∈ h, j x = j y → x = y) := by
  have hω := omega_mem M hM hS.bounded hI
  have hA := indexSpace_mem M hM hP hU hPow hS.bounded hω ht
  obtain ⟨T,hT,hTT,hpair⟩ := internal_transitive_container M hM hP hU hS.bounded hR hI
    (pair_mem M hM hP hA hω)
  have hAT : indexSpace t ⊆ T := fun x hx => hTT _
    (hTT _ hpair _ (ZFSet.mem_pair.mpr (Or.inl rfl))) x hx
  have hωT : ZFSet.omega.{u} ⊆ T := fun x hx => hTT _
    (hTT _ hpair _ (ZFSet.mem_pair.mpr (Or.inr rfl))) x hx
  have hnT : ∀ n, natSet.{u} n ∈ T := fun n => hωT ((mem_omega _).mpr ⟨n,rfl⟩)
  obtain ⟨K,hK,hgraphs⟩ := FiniteTerm.uniform_internal_evaluation_graph M T hM hP hU hPow hS hR hI
    hT hTT hnT
  refine ⟨K,hK,?_⟩
  intro xs hxs d hd hdt hsd φ
  let n := max 2 φ.width
  have hspace := space_mem M hM hP hU hPow hS.bounded hd n
  obtain ⟨V,hV,hVT,hpairV⟩ := internal_transitive_container M hM hP hU hS.bounded hR hI
    (pair_mem M hM hP hd hspace)
  have hdV : d ⊆ V := fun x hx => hVT _
    (hVT _ hpairV _ (ZFSet.mem_pair.mpr (Or.inl rfl))) x hx
  have hspaceV : space d n ⊆ V := fun x hx => hVT _
    (hVT _ hpairV _ (ZFSet.mem_pair.mpr (Or.inr rfl))) x hx
  obtain ⟨L,hL,hLf,hLc⟩ := FiniteTerm.internal_leaf_graph M hM hP hU hPow hS.bounded hR hω ht xs hxs
  obtain ⟨O,hO,hOf,_,hOps⟩ := FiniteTerm.internal_skolem_operations M hM hP hU hPow hS.bounded hR
    hI hAC
    hd n (differenceBody :: fragment n φ) 0
  obtain ⟨E,hE,hEsub,hEgraph⟩ := hgraphs (indexSpace t) hA hAT ZFSet.omega hω hωT L hL O hO V hV
  let h := FiniteTerm.generatedRange d K E
  have hh : h ∈ M := FiniteTerm.generatedRange_mem M hM hS.bounded hd hK hE
  have hevalSeed (x : ZFSet.{u}) (hx : x ∈ t ∪ elements xs) :
      ∃ c, FiniteTerm.Eval (indexSpace t) ZFSet.omega L O V c x := by
    obtain ⟨a,ha,hax⟩ := hLc x hx
    exact ⟨_,FiniteTerm.Eval.leaf ha (hdV (hsd hx)) hax⟩
  have hsh : t ∪ elements xs ⊆ h := fun x hx =>
    (FiniteTerm.mem_generatedRange hEgraph hEsub x).mpr ⟨hsd hx,hevalSeed x hx⟩
  have hhd : h ⊆ d := fun x hx => ((FiniteTerm.mem_generatedRange hEgraph hEsub x).mp hx).1
  have hzero := hevalSeed ∅ (ZFSet.mem_union.mpr (Or.inl h0t))
  have hclosed (ψ : Formula) (hψ : ψ ∈ differenceBody :: fragment n φ) :
      ∃ g, SkolemGraph d n ψ (fun _ => d) g ∧ Closed n g h := by
    obtain ⟨i,g,_,hgs,hgo⟩ := hOps ψ hψ
    exact ⟨g,hgs,FiniteTerm.generatedRange_closed n hVT hdV hspaceV hEgraph hEsub hzero
      (fun z hz => (ZFSet.mem_sep.mp (hgs.1 hz)).1) i hgo⟩
  have hext : StructureExtensional h := by
    obtain ⟨g,hgs,hcl⟩ := hclosed differenceBody List.mem_cons_self
    exact closed_extensional d h g n (Nat.le_max_left _ _) hdt hhd hcl ⟨g,fun _ hx => hx,hgs⟩
  have htransfer : ∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ h) → (φ.Realize h e ↔ φ.Realize d e) := by
    intro e he
    exact realize_of_witnesses d h hhd φ
      (witnesses_of_closed_graphs d h n φ (Nat.le_max_right _ _) hhd
        (fun ψ hψ => hclosed ψ (List.mem_cons_of_mem _ hψ))) e he
  obtain ⟨f,hf,j,hfj,hj,hi⟩ := FiniteTerm.internal_evaluated_injection M hM hP hU hPow hS.bounded
    hAC
    hh hK hE hLf hOf hEsub hEgraph
    (fun x hx => ((FiniteTerm.mem_generatedRange hEgraph hEsub x).mp hx).2)
  exact ⟨h,hh,hsh,hhd,hext,htransfer,f,hf,j,hfj,hj,hi⟩

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
