/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/CollectionHierarchySyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.ContextHierarchyGraph
public import LeanPool.TuringConeRigidity.Syntax.SigmaCollectionClosure
public import LeanPool.TuringConeRigidity.Constructibility.HierarchySyntax

/-!
# Collection Hierarchy Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u
theorem hierarchyGraph_sigmaDefinable_collection {M : ZFSet.{u}} (C : Context M) (hRep :
  SigmaReplacement M) (hColl : SigmaCollection M) (s d r f : ℕ) :
    SigmaDefinable M (fun e => HierarchyGraph M (e s) (e d) (e r) (e f)) := by
  have hd := (defAllMem (defSubset C 0 (d+1)) d).toSigma C.transitive
  have hf := (functionGraph_definable C d r f).toSigma C.transitive
  have hv : SigmaDefinable M (fun e => e 1 = definablePower (e 0)) :=
    (definablePower_sigmaDefinable_context M C).subst (fun i => if i = 0 then 1 else 0)
  have hs := ((stageStep_definable C (s+3) (f+3) (r+3) 2 0).toSigma C.transitive).and hv
  have hi := SigmaDefinable.impBounded C (defPairMem C 1 0 (f+2)) hs.existsSet
  exact hd.and (hf.and ((hi.allMem_collection C hRep hColl (r+1)).allMem_collection C hRep hColl d))

theorem uniform_hierarchy_certificate_collection (M R d q : ZFSet.{u}) (C : Context M) (hRep :
  SigmaReplacement M) (hColl : SigmaCollection M) (hs : seed R ∈ M) (hdM : d ∈ M) (hqM : q ∈ M)
    (hd : Transitive d) (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) :
    ∃ p : SigmaFormula, ∃ a : ℕ → ZFSet.{u}, (∀ i, a i ∈ M) ∧
      ∀ x ∈ d, ∀ f ∈ M, p.Realize M (cons f (cons x a)) ↔
        ∃ r ∈ M, HierarchyGraph M (seed R) (hull d q x) r f := by
  have hh : Definable M (fun e => e 1 ∈ q ∧ Transitive (e 1) ∧ e 3 ∈ e 1 ∧
      ∀ b ∈ q, Transitive b → e 3 ∈ b → e 1 ⊆ b) := by
    refine ⟨.isHull 2 6 1 3,cons d (fun _ => q),?_,?_⟩
    · intro i
      cases i with
      | zero => exact hdM
      | succ i => exact hqM
    · intro e
      simp [Formula.eval_isHull,mix,cons]
  have hg : SigmaDefinable M (fun e => HierarchyGraph M (seed R) (e 1) (e 0) (e 2)) := by
    have h := hierarchyGraph_sigmaDefinable_collection C hRep hColl 0 2 1 3
    have eq := (equal_param hs 0).toSigma C.transitive
    have hx := (eq.and h).existsSet
    exact hx.congr (fun e _ => by simp [hs])
  have hc := (hh.toSigma C.transitive).and hg
  obtain ⟨p,a,ha,hp⟩ := sigma_binary_relation (fun x f =>
    ∃ c ∈ M, ∃ r ∈ M, (c ∈ q ∧ Transitive c ∧ x ∈ c ∧
      ∀ b ∈ q, Transitive b → x ∈ b → c ⊆ b) ∧ HierarchyGraph M (seed R) c r f)
    hc.existsSet.existsSet
  refine ⟨p,a,ha,?_⟩
  intro x hx f hf
  rw [hp x (C.transitive d hdM x hx) f hf]
  constructor
  · rintro ⟨c,hc,r,hr,hh,hg⟩
    have he := (isHull_iff M d q C.transitive C.separation hdM hqM hd hq hx hc).mp hh
    subst c
    exact ⟨r,hr,hg⟩
  · rintro ⟨r,hr,hg⟩
    have hc := hull_mem M d q C.transitive C.separation hdM hqM (C.transitive d hdM x hx)
    exact ⟨_,hc,r,hr,(isHull_iff M d q C.transitive C.separation hdM hqM hd hq hx hc).mpr rfl,hg⟩

end TuringRigidity.RelativeConstructible

end OAI
