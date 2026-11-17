/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/CheckedDefSuccessor.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.VariableCertificateBounds
public import LeanPool.TuringConeRigidity.Constructibility.DomainParameterizedSyntax
public import LeanPool.TuringConeRigidity.Constructibility.ContextDefinablePower

/-!
# Checked Def Successor
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

def CheckedDefSuccessor (N w s A D : ZFSet.{u}) : Prop :=
  ∃ Q ∈ N, ∃ B ∈ N, (PowerBound N w Q ∧ PowerBound N s B) ∧
    ∃ G ∈ N, ∃ T ∈ N, ∃ H ∈ N, ∃ Z ∈ N, DefSystem Q B A G T H Z D

theorem checkedDefSuccessor_domainDefinable {M : ZFSet.{u}} (C : Context M) :
    DomainDefinable M (fun N e => CheckedDefSuccessor N (e 2) (e 3) (e 1) (e 0)) := by
  have hs := (defSystem_allBounds C 5 4 7 3 2 1 0
    6).toDomain.existsSet.existsSet.existsSet.existsSet
  have hb := (powerBound_domainDefinable C 4 1).and (powerBound_domainDefinable C 5 0)
  exact (hb.and hs).existsSet.existsSet

theorem CheckedDefSuccessor.sound {N A D : ZFSet.{u}}
    (hf : ∀ p : SentenceForm, family p ∈ N)
    (hs : ∀ p : SentenceForm, supportGraph p ∈ N)
    (h : CheckedDefSuccessor N ZFSet.omega (ZFSet.prod ZFSet.omega ZFSet.omega) A D) :
    D = definablePower A := by
  obtain ⟨Q,_,B,_,hb,G,_,T,_,H,_,Z,_,hd⟩ := h
  exact hd.exact (fun p => (hb.1 _).mpr ⟨hf p,family_subset_omega p⟩)
    (fun p => (hb.2 _).mpr ⟨hs p,supportGraph_subset p⟩)

theorem checkedDefSuccessor_of_context (M A D : ZFSet.{u}) (C : Context M) (hA : A ∈ M) :
    CheckedDefSuccessor M ZFSet.omega (ZFSet.prod ZFSet.omega ZFSet.omega) A D ↔
      D = definablePower A := by
  constructor
  · exact CheckedDefSuccessor.sound
      (family_mem M C.transitive C.pairing C.union C.omega_mem)
      (supportGraph_mem M C.transitive C.pairing C.union C.omega_mem)
  · rintro rfl
    obtain ⟨Q,hQ,hq,hf⟩ := internal_family_bound M C.transitive C.pairing C.union C.power
      C.omega_mem
    obtain ⟨B,hB,hb⟩ := internal_power M C.transitive C.power (C.prod_mem C.omega_mem C.omega_mem)
    have hs (p : SentenceForm) : supportGraph p ∈ B := (hb _).mpr
      ⟨supportGraph_mem M C.transitive C.pairing C.union C.omega_mem p,supportGraph_subset p⟩
    exact ⟨Q,hQ,B,hB,⟨hq,hb⟩,internal_defSystem_of_context M C Q B A hA hf hs⟩

end TuringRigidity.RelativeConstructible

end OAI
