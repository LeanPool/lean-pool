/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OmegaGraphRestriction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.InternalOmegaPower

/-!
# Omega Graph Restriction
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem omegaStageStep_domain (M x r f : ZFSet.{u}) (hg : OmegaGraph M x r f) :
    StageStep (1 : Ordinal.{u}).toZFSet f r x (Ordinal.omega0 ^ x.rank).toZFSet := by
  refine ⟨?_,?_,?_⟩
  · intro z hz; exact (omegaPower_members x.rank z).mpr (Or.inl hz)
  · intro z hz
    rcases (omegaPower_members x.rank z).mp hz with hz|⟨t,ht,hz⟩
    · exact Or.inl hz
    · rw [hg.1.toZFSet_rank_eq] at ht
      obtain ⟨v,hv,hfv,_⟩ := hg.2.1.2 t ht
      rw [← hg.correct t ht v hv hfv] at hz
      exact Or.inr ⟨t,ht,v,hv,hfv,hz⟩
  · intro t ht v hv hfv z hz
    rw [hg.correct t ht v hv hfv] at hz
    exact (omegaPower_members x.rank z).mpr
      (Or.inr ⟨t,hg.1.toZFSet_rank_eq.symm ▸ ht,hz⟩)

theorem omegaStageStep_domain_exact {M x r f A : ZFSet.{u}} (hg : OmegaGraph M x r f)
    (hs : StageStep (1 : Ordinal.{u}).toZFSet f r x A) :
    A = (Ordinal.omega0 ^ x.rank).toZFSet := by
  have ht := omegaStageStep_domain M x r f hg
  apply ZFSet.ext; intro z
  constructor
  · intro hz
    rcases hs.2.1 z hz with hz|⟨t,ht',v,hv,hfv,hz⟩
    · exact ht.1 hz
    · exact ht.2.2 t ht' v hv hfv hz
  · intro hz
    rcases ht.2.1 z hz with hz|⟨t,ht',v,hv,hfv,hz⟩
    · exact hs.1 hz
    · exact hs.2.2 t ht' v hv hfv hz

theorem internal_omegaGraph_below (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (x : ZFSet.{u}) (hx : x ∈ M) (ho : x.IsOrdinal) :
    ∃ f ∈ M, OmegaGraph M x (iterUnion 2 f) f := by
  obtain ⟨f,hf,hg⟩ := internal_omegaGraph M hM hT x hx ho
  let p : Formula := .existsMem 1 (.existsMem 3 (.orderedPair 2 1 0))
  let e : ℕ → ZFSet.{u} := cons x (fun _ => iterUnion 2 f)
  let g := ZFSet.sep (fun z => p.Eval (cons z e)) f
  have hgM : g ∈ M := sep_mem M hM hT.separation.finitePrefix.bounded p e
    (by
      intro i
      cases i
      · exact hx
      · exact iterUnion_mem M hM hT.union hf 2) hf
  have hm (z : ZFSet.{u}) : z ∈ g ↔ ∃ t ∈ x, z = ZFSet.pair t (omegaNext t) := by
    change z ∈ ZFSet.sep _ f ↔ _
    simp only [ZFSet.mem_sep,p,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ]
    change (z ∈ f ∧ ∃ t ∈ x, ∃ v ∈ iterUnion 2 f, z = ZFSet.pair t v) ↔ _
    constructor
    · rintro ⟨hz,t,ht,v,hv,rfl⟩
      exact ⟨t,ht,by rw [hg.correct t (ZFSet.mem_insert_of_mem x ht) v hv hz]⟩
    · rintro ⟨t,ht,rfl⟩
      have hp := (hg.mem_iff _).mpr ⟨t,ZFSet.mem_insert_of_mem x ht,rfl⟩
      exact ⟨hp,t,ht,_,second_mem_doubleUnion hp,rfl⟩
  exact ⟨g,hgM,omegaGraph_of_mem_iff M x g hM hT hx hgM ho hm⟩

theorem OmegaGraph.value_subset_power {M r f : ZFSet.{u}} {a : Ordinal.{u}}
    (hg : OmegaGraph M a.toZFSet r f) (t v : ZFSet.{u})
    (ht : t ∈ a.toZFSet) (hv : v ∈ r) (hfv : ZFSet.pair t v ∈ f) :
    v ⊆ (Ordinal.omega0 ^ a).toZFSet := by
  rw [hg.correct t ht v hv hfv,omegaNext]
  obtain ⟨b,hb,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
  rw [Ordinal.rank_toZFSet]
  exact Ordinal.toZFSet_monotone
    (Ordinal.opow_le_opow_right Ordinal.omega0_pos (Order.succ_le_of_lt hb))

end TuringRigidity.OrdinalArithmetic

end OAI
