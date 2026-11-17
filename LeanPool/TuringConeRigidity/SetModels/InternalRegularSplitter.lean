/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalRegularSplitter.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RegularDecisionPartition
public import LeanPool.TuringConeRigidity.SetModels.InternalProjectedGeneric
public import LeanPool.TuringConeRigidity.CohenForcing.CohenProductSplitting

/-!
# Internal Regular Splitter
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalRegularSplitter
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalProjectedGeneric RegularDecisionPartition RegularCodeSplitting

theorem splitter_graph (M c B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hsplit : ∀ p ∈ c, ∃ p0 ∈ c, ∃ p1 ∈ c, p ⊆ p0 ∧ p ⊆ p1 ∧
      ¬ ∃ r ∈ c, p0 ⊆ r ∧ p1 ⊆ r) :
    ∃ T ∈ M, FunctionGraph (ZFSet.prod (positive B) B)
      (ZFSet.prod (positive B) (positive B)) T ∧
      ∀ U ∈ positive B, ∀ D ∈ B, ∀ V W,
        ZFSet.pair (ZFSet.pair U D) (ZFSet.pair V W) ∈ T →
          V ∈ positive B ∧ W ∈ positive B ∧ Refines c U D V W := by
  let P := positive B
  let X := ZFSet.prod P B
  let Y := ZFSet.prod P P
  have hP := positive_mem M B hM hT hBM
  have hX := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    hP hBM
  have hY := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    hP hP
  let e := cons X (cons Y (cons P (cons B (fun _ => c))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    · exact hX
    · exact hY
    · exact hP
    · exact hBM
    · exact hc
  let φ : Formula := .existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
    (.existsMem 5 (.existsMem 7 (.conj (.orderedPair 3 1 0)
      (.existsMem 7 (.existsMem 8 (.conj (.orderedPair 4 1 0)
        (refiningFormula 11 3 2 1 0)))))))))
  let R := (ZFSet.prod X Y).sep (fun z => φ.Eval (cons z e))
  have hRM : R ∈ M := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hX hY)
  have hR (U D V W : ZFSet.{0}) :
      ZFSet.pair (ZFSet.pair U D) (ZFSet.pair V W) ∈ R ↔
        U ∈ P ∧ D ∈ B ∧ V ∈ P ∧ W ∈ P ∧ Refines c U D V W := by
    simp only [R,ZFSet.mem_sep,φ,Formula.Eval,Formula.eval_orderedPair,
      refiningFormula_spec,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨_,x,_,y,_,hxy,U',hU,D',hD,hUD,V',hV,W',hW,hVW,h⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hxy
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hUD
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hVW
      exact ⟨hU,hD,hV,hW,h⟩
    · rintro ⟨hU,hD,hV,hW,h⟩
      have hx : ZFSet.pair U D ∈ X := ZFSet.pair_mem_prod.mpr ⟨hU,hD⟩
      have hy : ZFSet.pair V W ∈ Y := ZFSet.pair_mem_prod.mpr ⟨hV,hW⟩
      exact ⟨ZFSet.pair_mem_prod.mpr ⟨hx,hy⟩,_,hx,_,hy,rfl,U,hU,D,hD,rfl,V,hV,W,hW,rfl,h⟩
  have htotal : ∀ x ∈ X, ∃ y ∈ Y, ZFSet.pair x y ∈ R := by
    intro x hx
    obtain ⟨U,hU,D,hD,rfl⟩ := ZFSet.mem_prod.mp hx
    obtain ⟨hUB,hU0⟩ := ZFSet.mem_sep.mp hU
    obtain ⟨V,hV,W,hW,h⟩ := refining_partition M c B hM hT hc hB hsplit U D hUB hD hU0
    have hVP : V ∈ P := ZFSet.mem_sep.mpr ⟨hV,h.1.2.2.1⟩
    have hWP : W ∈ P := ZFSet.mem_sep.mpr ⟨hW,h.1.2.2.2.1⟩
    exact ⟨ZFSet.pair V W,ZFSet.pair_mem_prod.mpr ⟨hVP,hWP⟩,
      (hR U D V W).mpr ⟨hU,hD,hVP,hWP,h⟩⟩
  obtain ⟨T,hTmem,hfun,hTR⟩ := InternalRelationSelection.select_relation M X Y R
    hM hT hX hY hRM htotal
  exact ⟨T,hTmem,hfun,fun U _ D _ V W hp => ((hR U D V W).mp (hTR hp)).2.2⟩

theorem counted_cohen_presentation (M q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hq : q ∈ M) (hct : InternallyCountable M q) :
    ∃ c ∈ M,
      (∀ z, z ∈ c ↔ ∃ p ∈ q, ∃ s ∈ CohenGroundPoset.conditions ZFSet.omega,
        z = TaggedProductConditions.code p s) ∧
      InternalCollapse.orderSet c ∈ M ∧ InternallyCountable M c ∧
      ∃ B ∈ M, (∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U) ∧
        ∃ S ∈ M, InternallyCountable M S ∧ S ⊆ positive B ∧
          (∀ U, U ∈ S ↔ ∃ p ∈ c, U = InternalBooleanDense.basicCode c p) ∧
          (∀ U, IsCode c U → U ≠ ∅ → ∃ V ∈ S, V ⊆ U) ∧
          ∃ T ∈ M, FunctionGraph (ZFSet.prod (positive B) B)
            (ZFSet.prod (positive B) (positive B)) T ∧
            ∀ U ∈ positive B, ∀ D ∈ B, ∀ V W,
              ZFSet.pair (ZFSet.pair U D) (ZFSet.pair V W) ∈ T →
                V ∈ positive B ∧ W ∈ positive B ∧ Refines c U D V W := by
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨c,hc,hcs,hco,hcc⟩ := TaggedProductConditions.product_countable M q
    (CohenGroundPoset.conditions ZFSet.omega) hM hT hq
    (CohenGroundPoset.conditions_mem M _ hM hT hω) hct
    (CountedCohenConditions.conditions_countable M _ hM hT hω
      (Or.inr (InternalCountableProduct.omega_countable M hM hT)))
  obtain ⟨B,hBM,hB⟩ := internal_algebra M c hM hT hc
  obtain ⟨S,hSM,hSc,hSs,hSp,hSd⟩ := CountedRegularBasis.counted_basis M c hM hT hc hcc
  refine ⟨c,hc,hcs,hco,hcc,B,hBM,hB,S,hSM,hSc,?_,hSs,hSd,?_⟩
  · intro U hU
    exact ZFSet.mem_sep.mpr ⟨(hB U).mpr ⟨hM S hSM U hU,(hSp U hU).1⟩,(hSp U hU).2⟩
  · exact splitter_graph M c B hM hT hc hBM hB (CohenProductSplitting.product_splits q c hcs)

end TuringRigidity.InternalRegularSplitter

end OAI
