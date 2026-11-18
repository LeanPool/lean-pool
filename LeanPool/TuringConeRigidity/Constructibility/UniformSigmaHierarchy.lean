/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformSigmaHierarchy.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.UniformSigmaDefinability
public import LeanPool.TuringConeRigidity.Constructibility.UniformHierarchyStage

/-!
# Uniform Sigma Hierarchy
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem definablePower_uniformSigma (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    UniformSigmaDefinable M (fun _ e => e 0 = definablePower (e 1)) := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,
    hT.separation.finitePrefix.bounded,hT.infinity⟩
  obtain ⟨Q,hQ,_,hq⟩ := internal_family_bound M hM C.pairing C.union C.power C.omega_mem
  obtain ⟨B,hB,hb⟩ := internal_support_bound C
  have hc := (defSystem_definable C hQ hB 5 3 2 1 0 4).toUniformSigma
  apply hc.existsSet.existsSet.existsSet.existsSet.congr
  intro E hE hTE _ e he
  change (∃ G ∈ E, ∃ T ∈ E, ∃ H ∈ E, ∃ Z ∈ E,
    DefSystem Q B (e 1) G T H Z (e 0)) ↔ e 0 = definablePower (e 1)
  constructor
  · rintro ⟨G,_,T,_,H,_,Z,_,h⟩; exact h.exact hq hb
  · intro h; rw [h]
    exact internal_defSystem E hE hTE Q B (e 1) (he 1) hq hb

theorem hierarchyGraph_uniformSigma (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (s d r f : ℕ) :
    UniformSigmaDefinable M (fun E e => HierarchyGraph E (e s) (e d) (e r) (e f)) := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,
    hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hd := (defAllMem (defSubset C 0 (d+1)) d).toUniformSigma
  have hf := (functionGraph_definable C d r f).toUniformSigma
  have hv : UniformSigmaDefinable M (fun _ e => e 1 = definablePower (e 0)) :=
    (definablePower_uniformSigma M hM hT).subst (fun i => if i = 0 then 1 else 0)
  have hs := (stageStep_definable C (s+3) (f+3) (r+3) 2 0).toUniformSigma.and hv
  have hi := UniformSigmaDefinable.impBounded C (defPairMem C 1 0 (f+2)) hs.existsSet
  exact hd.and (hf.and ((hi.allMem (r+1)).allMem d))

theorem stageCertificate_uniformSigma (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    UniformSigmaDefinable M (fun E e =>
      ∃ d ∈ E, ∃ f ∈ E, ∃ r ∈ E, e 1 ∈ d ∧
        HierarchyGraph E (e 2) d r f ∧ StageStep (e 2) f r (e 1) (e 0)) := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,
    hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hg := hierarchyGraph_uniformSigma M hM hT 5 2 0 1
  have hs := (stageStep_definable C 5 1 0 4 3).toUniformSigma
  have hx := (member_definable C 4 2).toUniformSigma
  exact (hx.and (hg.and hs)).existsSet.existsSet.existsSet

theorem stageCertificate_iff (E R x A : ZFSet.{u}) (hE : Transitive E) (hTE : SourceT E)
    (hR : R ∈ E) (hx : x ∈ E) :
    (∃ d ∈ E, ∃ f ∈ E, ∃ r ∈ E, x ∈ d ∧
      HierarchyGraph E (seed R) d r f ∧ StageStep (seed R) f r x A) ↔ A = stage R x := by
  constructor
  · rintro ⟨d,_,f,_,r,_,hxd,hg,hs⟩
    exact (hg.stageStep_iff x hxd A).mp hs
  · intro h
    obtain ⟨d,hd,f,hf,hxd,hg⟩ := internal_hierarchy_cover E R x hE hTE hR hx
    exact ⟨d,hd,f,hf,_,iterUnion_mem E hE hTE.union hf 2,hxd,hg,
      (hg.stageStep_iff x hxd A).mpr h⟩

end TuringRigidity.RelativeConstructible

end OAI
