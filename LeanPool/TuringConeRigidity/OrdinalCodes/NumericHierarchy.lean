/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NumericHierarchy.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NumericDomain
public import LeanPool.TuringConeRigidity.Constructibility.SeedBoundStageSyntax

/-!
# Numeric Hierarchy
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.NumericSyntax
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding RelativeConstructible
open BoundedDefinability SetModelFunctions SetModelReals
universe u
theorem stageStep_definable (s f r x A : ℕ) :
    Numeric.{u} (fun e => StageStep (e s) (e f) (e r) (e x) (e A)) := by
  have hn := defAllMem (defOr (member_definable 0 (s+1))
    ((((defPairMem 1 0 (f+3)).and (member_definable 2 0)).existsMem (r+2)).existsMem (x+1))) A
  have hc := defAllMem (defAllMem (defImp (defPairMem 1 0 (f+2))
    (defSubset 0 (A+2))) (r+1)) x
  exact (defSubset s A).and (hn.and hc)

theorem functionGraph_definable (d r f : ℕ) :
    Numeric.{u} (fun e => FunctionGraph (e d) (e r) (e f)) := by
  refine ⟨.functionGraph (2*f) (2*d) (2*r),?_⟩
  intro B hB e
  simp only [Formula.eval_functionGraph,mix_even,FunctionGraph]

theorem insertedSelf_definable (s R : ℕ) :
    Numeric.{u} (fun e => e s = insert (e R) (e R)) := by
  have h := (member_definable R s).and ((defSubset R s).and
    (defAllMem (defOr (equal_definable 0 (R+1)) (member_definable 0 (R+1))) s))
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

theorem checkedDefSuccessor_domainDefinable :
    Domain.{u} (fun N e => CheckedDefSuccessor N (e 2) (e 3) (e 1) (e 0)) := by
  have hs := (defSystem_allBounds 5 4 7 3 2 1 0 6).toDomain.existsSet.existsSet.existsSet.existsSet
  have hb := (powerBound_domain 4 1).and (powerBound_domain 5 0)
  exact (hb.and hs).existsSet.existsSet

theorem checkedHierarchyGraph_domainDefinable
    (w sq s d r f : ℕ) :
    Domain.{u} (fun N e => CheckedHierarchyGraph N (e w) (e sq) (e s) (e d) (e r) (e f)) := by
  have hd := (defAllMem (defSubset 0 (d+1)) d).toDomain
  have hf := (functionGraph_definable d r f).toDomain
  have hv := (checkedDefSuccessor_domainDefinable).subst
    (fun i => match i with | 0 => 1 | 1 => 0 | 2 => w+3 | _ => sq+3)
  have hs := (stageStep_definable (s+3) (f+3) (r+3) 2 0).toDomain.and hv
  have hi := (defPairMem 1 0 (f+2)).toDomain.imp hs.existsSet
  exact hd.and (hf.and ((hi.allMem (r+1)).allMem d))

theorem seedBoundStage_domainDefinable :
    Domain.{u} (fun N e => SeedBoundStage N (e 3) (e 4) (e 2) (e 1) (e 0)) := by
  have h := (insertedSelf_definable 3 6).toDomain.and
    ((member_definable 5 2).toDomain.and
      ((checkedHierarchyGraph_domainDefinable 7 8 3 2 0 1).and
        (stageStep_definable 3 1 0 5 4).toDomain))
  exact h.existsSet.existsSet.existsSet.existsSet

end TuringRigidity.NumericSyntax

end OAI
