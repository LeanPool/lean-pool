/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/BooleanExpressionCoverage.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BooleanExpressionAssembly

/-!
# Boolean Expression Coverage
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BooleanExpressionCertificate
open TransitiveNameModel BoundedSetTheory InternalBooleanSyntax InternalGeneratedAlgebra
open InternalRegularOperations InternalRegularAlgebra

theorem sup_certified (M c B Q S F : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hSM : S ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hFQ : F ∈ Q)
    (hFC : F ⊆ certified M c B Q S) : supCode c F ∈ certified M c B Q S := by
  obtain ⟨hFM,hFB⟩ := (hQ F).mp hFQ
  have he := parameters_mem M c B Q S hM hT hc hBM hQM hSM
  have hColl := sigma_collection M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice
  obtain ⟨W,hWM,hW⟩ := hColl (.bounded witnessBody) (parameters c B Q S) he F hFM (by
    intro U hUF
    obtain ⟨_,K,hKM,hK⟩ := ZFSet.mem_sep.mp (hFC hUF)
    exact ⟨K,hKM,(witnessBody_realize M c B Q S K U hM he hKM (hM F hFM U hUF)).mpr hK⟩)
  obtain ⟨L,hLM,hL,hWL⟩ := internal_transitive_container M hM hT.pairing hT.union
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hWM
  have hKL (K : ZFSet.{0}) (hK : K ∈ W) : K ⊆ L :=
    fun t ht => hL K (hL W hWL K hK) t ht
  let a := goodGraphs (ZFSet.sUnion W) c B Q S L
  have haM : a ∈ M := goodGraphs_mem M _ c B Q S L hM hT
    (union_mem M hM hT.union hWM) hc hBM hQM hSM hLM
  let g := ZFSet.sUnion a
  have hgM : g ∈ M := union_mem M hM hT.union haM
  have hg : Certificate c B Q S L g := Certificate.sUnion (fun f hf => (ZFSet.mem_sep.mp hf).2)
  have htotal (U : ZFSet.{0}) (hUF : U ∈ F) : ∃ t ∈ L, ZFSet.pair t U ∈ g := by
    obtain ⟨K,hKW,hK⟩ := hW U hUF
    obtain ⟨_,f,hfK,hf,t,htK,hp⟩ :=
      (witnessBody_realize M c B Q S K U hM he (hM W hWM K hKW) (hM F hFM U hUF)).mp hK
    have hfa : f ∈ a := ZFSet.mem_sep.mpr ⟨ZFSet.mem_sUnion.mpr ⟨K,hKW,hfK⟩,hf.enlarge (hKL K hKW)⟩
    exact ⟨t,hKL K hKW htK,ZFSet.mem_sUnion.mpr ⟨f,hfa,hp⟩⟩
  let T := children L F g
  have hTM : T ∈ M := children_mem M L F g hM hT hLM hFM hgM
  let s := FiniteTerm.tag 2 T
  have hsM : s ∈ M := tag_mem M hM hT 2 hTM
  let D := L ∪ ({T,s} : ZFSet.{0})
  have hLD : L ⊆ D := fun _ h => ZFSet.mem_union.mpr (Or.inl h)
  have hTD : T ∈ D := ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_pair.mpr (Or.inl rfl)))
  have hsD : s ∈ D := ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_pair.mpr (Or.inr rfl)))
  have hDM : D ∈ M := binary_union_mem M hM hT.pairing hT.union hLM (pair_mem M hM hT.pairing hTM
    hsM)
  have hVB := internal_join M c B F hM hT hc hB hFM
  have hVM := ((hB _).mp hVB).1
  have hs : Step c B Q S D g s (supCode c F) := by
    refine Or.inr (Or.inr ⟨T,hTD,F,hFQ,rfl,rfl,?_,?_⟩)
    · exact fun t ht => (ZFSet.mem_sep.mp ht).2
    · intro U hUF
      obtain ⟨t,htL,hp⟩ := htotal U hUF
      exact ⟨t,ZFSet.mem_sep.mpr ⟨htL,U,hUF,hp⟩,hp⟩
  let f := g ∪ ({ZFSet.pair s (supCode c F)} : ZFSet.{0})
  have hfM : f ∈ M := binary_union_mem M hM hT.pairing hT.union hgM
    (singleton_mem M hM hT.pairing (orderedPair_mem M hM hT.pairing hsM hVM))
  have hf := (hg.enlarge hLD).insert hsD hVB hs
  exact ZFSet.mem_sep.mpr ⟨hVB,witness_of_certificate M c B Q S D f s _ hM hT hDM hfM hf
    (ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_singleton.mpr rfl)))⟩

theorem certified_closed (M c B Q S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hSM : S ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) : Closed c B Q (certified M c B Q S) :=
  ⟨fun _ h => (ZFSet.mem_sep.mp h).1,
    fun U hU => neg_certified M c B Q S U hM hT hc hB hU,
    fun F hF hFC => sup_certified M c B Q S F hM hT hc hBM hQM hSM hB hQ hF hFC⟩

theorem generated_certificate (M c B Q S U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hSM : S ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hSB : S ⊆ B)
    (hU : U ∈ generated c B Q S) : ∃ K ∈ M, Witness c B Q S K U := by
  have hC := certified_closed M c B Q S hM hT hc hBM hQM hSM hB hQ
  have hCM := certified_mem M c B Q S hM hT hc hBM hQM hSM
  have hCQ := (hQ _).mpr ⟨hCM,hC.1⟩
  have hSC : S ⊆ certified M c B Q S := by
    intro V hV
    exact seed_certified M c B Q S V hM hT (hM S hSM V hV) (hSB hV) hV
  exact (ZFSet.mem_sep.mp (generated_le c B Q S _ hCQ hSC hC hU)).2

theorem certified_eq_generated (M c B Q S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hSM : S ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hSB : S ⊆ B) :
    certified M c B Q S = generated c B Q S := by
  have hA := generated_closed c B Q S (algebra_closed M c B Q hM hT hc hB hQ)
  apply ZFSet.ext; intro U
  constructor
  · intro hU
    obtain ⟨_,K,_,_,g,_,hg,t,_,hp⟩ := ZFSet.mem_sep.mp hU
    exact hg.induction (fun V => V ∈ generated c B Q S) (fun V hV => seeds_subset c B Q S hSB hV)
      (fun V _ hV => hA.2.1 V hV) (fun F hF hFA => hA.2.2 F hF (fun V hV => hFA V hV)) t U hp
  · intro hU
    exact ZFSet.mem_sep.mpr ⟨generated_subset c B Q S hU,
      generated_certificate M c B Q S U hM hT hc hBM hQM hSM hB hQ hSB hU⟩

end TuringRigidity.BooleanExpressionCertificate

end OAI
