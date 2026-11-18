/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/RelativeLevySchemas.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.RelativeSigmaSchemas

/-!
# Relative Levy Schemas
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel
universe u

theorem ground_relativeModel_levy_schemas (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) :
    LevySigmaSeparation (relativeModel M (groundReals M)) ∧
      LevySigmaReplacement (relativeModel M (groundReals M)) := by
  let N := relativeModel M (groundReals M)
  have hR := groundReals_mem M hM hT
  have hN := relativeModel_transitive M (groundReals M) hM
  have hS := relativeModel_sigma_separation M (groundReals M) hM hT hR
  have hRep := relativeModel_sigma_replacement M (groundReals M) hM hT hR
  have correct := LevySigma.normalize_correct N hN
    (relativeModel_pairing M _ hM hT hR) (relativeModel_union M _ hM hT hR)
    hS.bounded hRep (ground_relativeModel_infinity M hM hT)
    (relativeModel_sigma_collection M _ hM hT hR)
  constructor
  · intro φ e he a ha
    obtain ⟨b,hb,hbdef⟩ := hS φ.normalize e he a ha
    refine ⟨b,hb,?_⟩
    intro x hx
    rw [hbdef x hx,correct φ (cons x e) (by
      intro i
      cases i
      · exact hx
      · exact he _)]
  · intro φ e he a ha htotal
    have eq (x y : ZFSet.{u}) (hx : x ∈ N) (hy : y ∈ N) :
        φ.normalize.Realize N (cons y (cons x e)) ↔ φ.Realize N (cons y (cons x e)) :=
      correct φ _ (by
        intro i
        rcases i with _ | i
        · exact hy
        rcases i with _ | i
        · exact hx
        exact he i)
    obtain ⟨b,hb,hbdef⟩ := hRep φ.normalize e he a ha (by
      intro x hx
      have hxN := hN a ha x hx
      obtain ⟨y,hy,hφ,hu⟩ := htotal x hx
      exact ⟨y,hy,(eq x y hxN hy).mpr hφ,fun z hz h => hu z hz ((eq x z hxN hz).mp h)⟩)
    refine ⟨b,hb,?_⟩
    intro y hy
    rw [hbdef y hy]
    apply exists_congr; intro x
    exact and_congr_right (fun hx => eq x y (hN a ha x hx) hy)

theorem relativeModel_empty_set (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) : BasicAxioms.EmptySet (relativeModel M R) :=
  ⟨∅,(mem_relativeModel M R _ hM hT hR).mpr (empty_in_relativeModel M R hM hT),
    fun x _ => ZFSet.notMem_empty x⟩

theorem relativeModel_extensionality (M R : ZFSet.{u}) (hM : Transitive M) :
    BasicAxioms.Extensionality (relativeModel M R) :=
  BasicAxioms.extensionality _ (relativeModel_transitive M R hM)

theorem relativeModel_foundation (M R : ZFSet.{u}) (hM : Transitive M) :
    BasicAxioms.Foundation (relativeModel M R) :=
  BasicAxioms.foundation _ (relativeModel_transitive M R hM)

end TuringRigidity.RelativeConstructible

end OAI
