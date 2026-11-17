/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/SeedBoundStageSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BoundedHierarchyCertificates
public import LeanPool.TuringConeRigidity.Constructibility.RelativeConstruction

/-!
# Seed Bound Stage Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem insertedSelf_definable {M : ZFSet.{u}} (C : Context M) (s R : ℕ) :
    Definable M (fun e => e s = insert (e R) (e R)) := by
  have h := (member_definable C R s).and ((defSubset C R s).and
    (defAllMem (defOr (equal_definable C 0 (R+1)) (member_definable C 0 (R+1))) s))
  apply h.congr
  intro e
  constructor
  · rintro ⟨hR,hsub,hall⟩
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_insert_iff]
    exact ⟨fun hz => hall z hz,fun h => h.elim (fun he => he ▸ hR) (fun hz => hsub hz)⟩
  · rintro he
    rw [he]
    exact ⟨ZFSet.mem_insert_iff.mpr (Or.inl rfl),
      fun _ hz => ZFSet.mem_insert_iff.mpr (Or.inr hz),fun _ hz => ZFSet.mem_insert_iff.mp hz⟩

def SeedBoundStage (N w sq R x A : ZFSet.{u}) : Prop :=
  ∃ s ∈ N, ∃ d ∈ N, ∃ f ∈ N, ∃ r ∈ N,
    s = insert R R ∧ x ∈ d ∧ CheckedHierarchyGraph N w sq s d r f ∧ StageStep s f r x A

theorem seedBoundStage_domainDefinable {M : ZFSet.{u}} (C : Context M) :
    DomainDefinable M (fun N e => SeedBoundStage N (e 3) (e 4) (e 2) (e 1) (e 0)) := by
  have h := (insertedSelf_definable C 3 6).toDomain.and
    ((member_definable C 5 2).toDomain.and
      ((checkedHierarchyGraph_domainDefinable C 7 8 3 2 0 1).and
        (stageStep_definable C 3 1 0 5 4).toDomain))
  exact h.existsSet.existsSet.existsSet.existsSet

theorem SeedBoundStage.sound {M N x A : ZFSet.{u}} (hM : Transitive M)
    (hf : ∀ p : SentenceForm, family p ∈ N)
    (hs : ∀ p : SentenceForm, supportGraph p ∈ N)
    (h : SeedBoundStage N ZFSet.omega (ZFSet.prod ZFSet.omega ZFSet.omega)
      (groundReals M) x A) : A = stage (groundReals M) x := by
  obtain ⟨s,_,d,_,f,_,r,_,he,hx,hg,hstep⟩ := h
  have heq : s = seed (groundReals M) := he.trans (ground_seed_shape M hM).symm
  rw [heq] at hg hstep
  exact hg.stage_exact hf hs hx hstep

theorem seed_bound_stage_at_levels (M x : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hx : x ∈ relativeModel M (groundReals M)) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧
      ∀ δ : Ordinal.{u}, δ.toZFSet ∈ M → γ ≤ δ →
        x ∈ level (groundReals M) δ ∧ stage (groundReals M) x ∈ level (groundReals M) δ ∧
        ∀ A : ZFSet.{u}, SeedBoundStage (level (groundReals M) δ) ZFSet.omega
          (ZFSet.prod ZFSet.omega ZFSet.omega) (groundReals M) x A ↔ A = stage (groundReals M) x
            := by
  let R := groundReals M
  have hR := groundReals_mem M hM hT
  have C := ground_relative_context M hM hT
  have hRep := relativeModel_sigma_replacement M R hM hT hR
  have hColl := relativeModel_sigma_collection M R hM hT hR
  have hRN : R ∈ relativeModel M R :=
    (mem_relativeModel M R R hM hT hR).mpr (parameter_in_relativeModel M R hM hT)
  have hs := seed_mem_collection _ R C hRep hRN
  obtain ⟨d,hd,f,hf,hxd,hg⟩ := relative_internal_hierarchy_cover M x hM hT hx
  have hr := iterUnion_mem _ C.transitive C.union hf 2
  obtain ⟨α,hα,hαspec⟩ := hierarchy_checked_at_levels M (seed R) d _ f hM hT hs hd hr hf hg
  have hA := stage_mem_collection _ R x C hRep hColl hRN hx
  obtain ⟨β,hβ,hβA⟩ := (mem_relativeModel M R _ hM hT hR).mp hA
  refine ⟨max α β,internal_ordinal_max M hα hβ,?_⟩
  intro δ hδ hle
  obtain ⟨hsL,hdL,hrL,hfL,_,_,hfamily,hsupport,hchecked⟩ :=
    hαspec δ hδ ((le_max_left α β).trans hle)
  have hxL := level_transitive R δ d hdL x hxd
  refine ⟨hxL,level_mono R ((le_max_right α β).trans hle) hβA,?_⟩
  intro A
  constructor
  · exact SeedBoundStage.sound hM hfamily hsupport
  · rintro rfl
    exact ⟨seed R,hsL,d,hdL,f,hfL,_,hrL,ground_seed_shape M hM,hxd,hchecked,
      (hg.stageStep_iff x hxd _).mpr rfl⟩

end TuringRigidity.RelativeConstructible

end OAI
