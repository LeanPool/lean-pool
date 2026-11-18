/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/CheckedHierarchySyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.CheckedDefSuccessor
public import LeanPool.TuringConeRigidity.Constructibility.DomainSyntaxClosure

/-!
# Checked Hierarchy Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

/-- A hierarchy graph whose stage successors carry the internal definable-power certificates. -/
def CheckedHierarchyGraph (N w sq s d r f : ZFSet.{u}) : Prop :=
  Transitive d ∧ FunctionGraph d r f ∧
    ∀ x ∈ d, ∀ v ∈ r, ZFSet.pair x v ∈ f →
      ∃ A ∈ N, StageStep s f r x A ∧ CheckedDefSuccessor N w sq A v

theorem checkedHierarchyGraph_domainDefinable {M : ZFSet.{u}} (C : Context M)
    (w sq s d r f : ℕ) :
    DomainDefinable M (fun N e => CheckedHierarchyGraph N (e w) (e sq) (e s) (e d) (e r) (e f)) :=
      by
  have hd := (defAllMem (defSubset C 0 (d+1)) d).toDomain
  have hf := (functionGraph_definable C d r f).toDomain
  have hv := (checkedDefSuccessor_domainDefinable C).subst
    (fun i => match i with | 0 => 1 | 1 => 0 | 2 => w+3 | _ => sq+3)
  have hs := (stageStep_definable C (s+3) (f+3) (r+3) 2 0).toDomain.and hv
  have hi := (defPairMem C 1 0 (f+2)).toDomain.imp hs.existsSet
  exact hd.and (hf.and ((hi.allMem C (r+1)).allMem C d))

theorem CheckedHierarchyGraph.sound {N s d r f : ZFSet.{u}}
    (hf : ∀ p : SentenceForm, family p ∈ N)
    (hs : ∀ p : SentenceForm, supportGraph p ∈ N)
    (h : CheckedHierarchyGraph N ZFSet.omega (ZFSet.prod ZFSet.omega ZFSet.omega) s d r f) :
    HierarchyGraph N s d r f := by
  refine ⟨h.1,h.2.1,?_⟩
  intro x hx v hv hpair
  obtain ⟨A,hA,hstep,hdef⟩ := h.2.2 x hx v hv hpair
  exact ⟨A,hA,hstep,hdef.sound hf hs⟩

theorem checkedHierarchyGraph_of_context (N s d r f : ZFSet.{u}) (C : Context N) :
    CheckedHierarchyGraph N ZFSet.omega (ZFSet.prod ZFSet.omega ZFSet.omega) s d r f ↔
      HierarchyGraph N s d r f := by
  constructor
  · exact CheckedHierarchyGraph.sound
      (family_mem N C.transitive C.pairing C.union C.omega_mem)
      (supportGraph_mem N C.transitive C.pairing C.union C.omega_mem)
  · intro h
    refine ⟨h.1,h.2.1,?_⟩
    intro x hx v hv hpair
    obtain ⟨A,hA,hstep,hdef⟩ := h.2.2 x hx v hv hpair
    exact ⟨A,hA,hstep,(checkedDefSuccessor_of_context N A v C hA).mpr hdef⟩

theorem CheckedHierarchyGraph.stage_exact {N R d r f x A : ZFSet.{u}}
    (hf : ∀ p : SentenceForm, family p ∈ N)
    (hs : ∀ p : SentenceForm, supportGraph p ∈ N)
    (h : CheckedHierarchyGraph N ZFSet.omega (ZFSet.prod ZFSet.omega ZFSet.omega)
      (seed R) d r f) (hx : x ∈ d) (hstep : StageStep (seed R) f r x A) :
    A = stage R x :=
  ((h.sound hf hs).stageStep_iff x hx A).mp hstep

end TuringRigidity.RelativeConstructible

end OAI
