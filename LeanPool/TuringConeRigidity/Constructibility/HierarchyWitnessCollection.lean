/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/HierarchyWitnessCollection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.HierarchySyntax

/-!
# Hierarchy Witness Collection
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

/-- A bounded collection of satisfaction and definition witnesses for the hierarchy value at
`x`. -/
def HierarchyRequest (Q B s f r x c : ZFSet.{u}) : Prop :=
  ∃ A ∈ c, ∃ v ∈ r, ∃ G ∈ c, ∃ T ∈ c, ∃ H ∈ c, ∃ Z ∈ c,
    ZFSet.pair x v ∈ f ∧ StageStep s f r x A ∧ DefSystem Q B A G T H Z v

theorem hierarchyRequest_definable {M Q B : ZFSet.{u}} (C : Context M)
    (hQ : Q ∈ M) (hB : B ∈ M) (s f r x c : ℕ) :
    Definable M (fun e => HierarchyRequest Q B (e s) (e f) (e r) (e x) (e c)) := by
  have h := (defPairMem C (x+6) 4 (f+6)).and
    ((stageStep_definable C (s+6) (f+6) (r+6) (x+6) 5).and
      (defSystem_definable C hQ hB 5 3 2 1 0 4))
  exact (((((h.existsMem (c+5)).existsMem (c+4)).existsMem (c+3)).existsMem (c+2)).existsMem
    (r+1)).existsMem c

theorem hierarchyRequest_binary {M Q B s f r : ZFSet.{u}} (C : Context M)
    (hQ : Q ∈ M) (hB : B ∈ M) (hs : s ∈ M) (hf : f ∈ M) (hr : r ∈ M) :
    ∃ p : SigmaFormula, ∃ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ M) ∧
      ∀ x ∈ M, ∀ c ∈ M, p.Realize M (cons c (cons x e)) ↔
        HierarchyRequest Q B s f r x c := by
  have h := (hierarchyRequest_definable C hQ hB 2 1 0 4 3).toSigma C.transitive
  have eq := ((equal_param hr 0).and ((equal_param hf 1).and (equal_param hs 2))).toSigma
    C.transitive
  have hc := (eq.and h).existsSet.existsSet.existsSet
  apply sigma_binary_relation _ (hc.congr ?_)
  intro e _
  simp only [cons_zero,cons_succ]
  constructor
  · rintro ⟨s',_,f',_,r',_,⟨rfl,rfl,rfl⟩,h⟩
    exact h
  · intro h
    exact ⟨s,hs,f,hf,r,hr,⟨rfl,rfl,rfl⟩,h⟩

theorem hierarchy_witness_collection {M Q B s d r f : ZFSet.{u}} (C : Context M)
    (hColl : SigmaCollection M) (hQ : Q ∈ M) (hB : B ∈ M)
    (hq : ∀ p : SentenceForm, family p ∈ Q)
    (hb : ∀ p : SentenceForm, supportGraph p ∈ B)
    (hs : s ∈ M) (hd : d ∈ M) (hr : r ∈ M) (hf : f ∈ M)
    (hg : HierarchyGraph M s d r f) :
    ∃ W ∈ M, ∀ x ∈ d, ∃ c ∈ W, HierarchyRequest Q B s f r x c := by
  obtain ⟨p,e,he,hp⟩ := hierarchyRequest_binary C hQ hB hs hf hr
  obtain ⟨W,hW,hw⟩ := hColl p e he d hd (by
    intro x hx
    obtain ⟨v,hv,hfv,_⟩ := hg.2.1.2 x hx
    obtain ⟨A,hA,hstep,hvA⟩ := hg.2.2 x hx v hv hfv
    obtain ⟨G,hG,T,hT,H,hH,Z,hZ,hdef⟩ := internal_defSystem_of_context M C Q B A hA hq hb
    let a : Fin 5 → ZFSet.{u} := fun i => match i.val with
      | 0 => A | 1 => G | 2 => T | 3 => H | _ => Z
    have ha : ∀ i, a i ∈ M := by
      intro i; dsimp [a]; split <;> assumption
    have hc := finite_range_mem M C.transitive C.pairing C.union (C.nat_mem 0) 5 a ha
    refine ⟨ZFSet.range a,hc,(hp x (C.transitive d hd x hx) _ hc).mpr ?_⟩
    refine ⟨A,ZFSet.mem_range.mpr ⟨⟨0,by decide⟩,rfl⟩,v,hv,
      G,ZFSet.mem_range.mpr ⟨⟨1,by decide⟩,rfl⟩,
      T,ZFSet.mem_range.mpr ⟨⟨2,by decide⟩,rfl⟩,
      H,ZFSet.mem_range.mpr ⟨⟨3,by decide⟩,rfl⟩,
      Z,ZFSet.mem_range.mpr ⟨⟨4,by decide⟩,rfl⟩,hfv,hstep,?_⟩
    rwa [hvA])
  exact ⟨W,hW,fun x hx => by
    obtain ⟨c,hc,h⟩ := hw x hx
    exact ⟨c,hc,(hp x (C.transitive d hd x hx) c (C.transitive W hW c hc)).mp h⟩⟩

end TuringRigidity.RelativeConstructible

end OAI
